//! Ion 1.1 binary writer (partial).
//!
//! This currently targets only the subset needed for regression tests and ad-hoc tooling.
//! It does NOT emit Ion 1.1 e-expressions/macros and does not model module mutation directives.
//! Symbol values can be written as either inline text (A0..AF/FA) or as symbol addresses (E1..E3).

const std = @import("std");
const ion = @import("../ion.zig");
const value = @import("value.zig");

const IonError = ion.IonError;

pub fn writeBinary11(allocator: std.mem.Allocator, doc: []const value.Element) IonError![]u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    // Ion 1.1 IVM: E0 01 01 EA
    try appendSlice(&out, allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    for (doc) |e| try writeElement(allocator, &out, e);

    return out.toOwnedSlice(allocator) catch return IonError.OutOfMemory;
}

fn writeElement(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), e: value.Element) IonError!void {
    if (e.annotations.len != 0) {
        try writeAnnotationsSequence(allocator, out, e.annotations);
    }
    try writeValue(allocator, out, e.value);
}

fn writeValue(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), v: value.Value) IonError!void {
    switch (v) {
        .null => try appendByte(out, allocator, 0xEA),
        .bool => |b| try appendByte(out, allocator, if (b) 0x6E else 0x6F),
        .int => |i| try writeInt(allocator, out, i),
        .float => |f| try writeFloat(allocator, out, f),
        .decimal => |d| try writeDecimal(allocator, out, d),
        .string => |s| try writeString(allocator, out, s),
        .symbol => |s| try writeSymbol(allocator, out, s),
        .blob => |b| try writeLob(allocator, out, 0xFE, b),
        .clob => |b| try writeLob(allocator, out, 0xFF, b),
        .list => |items| try writeSequence(allocator, out, 0xB0, 0xFB, items),
        .sexp => |items| try writeSequence(allocator, out, 0xC0, 0xFC, items),
        .@"struct" => |st| try writeStruct(allocator, out, st),
        .timestamp => return IonError.Unsupported, // TODO
    }
}

fn writeInt(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), i: value.Int) IonError!void {
    const bytes = try twosComplementIntBytesLe(allocator, i);
    defer allocator.free(bytes);

    if (bytes.len <= 8) {
        try appendByte(out, allocator, 0x60 + @as(u8, @intCast(bytes.len)));
        try appendSlice(out, allocator, bytes);
        return;
    }

    try appendByte(out, allocator, 0xF6);
    try writeFlexUIntShift1(out, allocator, bytes.len);
    try appendSlice(out, allocator, bytes);
}

fn writeFloat(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), f: f64) IonError!void {
    if (f == 0.0 and !std.math.signbit(f)) {
        try appendByte(out, allocator, 0x6A);
        return;
    }
    try appendByte(out, allocator, 0x6D);
    var buf: [8]u8 = undefined;
    std.mem.writeInt(u64, &buf, @bitCast(f), .little);
    try appendSlice(out, allocator, &buf);
}

fn writeDecimal(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), d: value.Decimal) IonError!void {
    var payload = std.ArrayListUnmanaged(u8){};
    defer payload.deinit(allocator);

    // Exponent as FlexInt.
    try writeFlexIntShift1(&payload, allocator, d.exponent);

    const coeff_is_zero = switch (d.coefficient) {
        .small => |v| v == 0,
        .big => |v| v.eqlZero(),
    };
    if (coeff_is_zero) {
        if (d.is_negative) try appendByte(&payload, allocator, 0x00); // negative zero marker
    } else {
        // Coefficient bytes are signed two's complement in binary Ion 1.1.
        switch (d.coefficient) {
            .small => |v| {
                if (v < 0) return IonError.InvalidIon;
                const signed: i128 = if (d.is_negative) -v else v;
                const bytes = try twosComplementI128BytesLe(allocator, signed);
                defer allocator.free(bytes);
                try appendSlice(&payload, allocator, bytes);
            },
            .big => |mag_ptr| {
                // This writer currently stores decimals as {sign, magnitude, exponent}. To emit the
                // Ion 1.1 binary coefficient field (signed two's complement), we materialize a
                // signed BigInt in a temporary and write it out immediately.
                var tmp = std.math.big.int.Managed.init(allocator) catch return IonError.OutOfMemory;
                defer tmp.deinit();
                tmp.copy(mag_ptr.*.toConst()) catch return IonError.OutOfMemory;
                if (d.is_negative) tmp.negate();
                const bytes = try twosComplementBigIntConstBytesLe(allocator, tmp.toConst());
                defer allocator.free(bytes);
                try appendSlice(&payload, allocator, bytes);
            },
        }
    }

    if (payload.items.len <= 15) {
        try appendByte(out, allocator, 0x70 + @as(u8, @intCast(payload.items.len)));
        try appendSlice(out, allocator, payload.items);
        return;
    }
    try appendByte(out, allocator, 0xF7);
    try writeFlexUIntShift1(out, allocator, payload.items.len);
    try appendSlice(out, allocator, payload.items);
}

fn writeString(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), s: []const u8) IonError!void {
    if (!std.unicode.utf8ValidateSlice(s)) return IonError.InvalidIon;
    if (s.len <= 15) {
        try appendByte(out, allocator, 0x90 + @as(u8, @intCast(s.len)));
        try appendSlice(out, allocator, s);
        return;
    }
    try appendByte(out, allocator, 0xF9);
    try writeFlexUIntShift1(out, allocator, s.len);
    try appendSlice(out, allocator, s);
}

fn writeSymbol(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), s: value.Symbol) IonError!void {
    if (s.text) |t| {
        if (!std.unicode.utf8ValidateSlice(t)) return IonError.InvalidIon;
        if (t.len <= 15) {
            try appendByte(out, allocator, 0xA0 + @as(u8, @intCast(t.len)));
            try appendSlice(out, allocator, t);
            return;
        }
        try appendByte(out, allocator, 0xFA);
        try writeFlexUIntShift1(out, allocator, t.len);
        try appendSlice(out, allocator, t);
        return;
    }
    if (s.sid) |sid| {
        // Symbol address: E1..E3 (fixed uint with bias).
        if (sid <= 0xFF) {
            try appendByte(out, allocator, 0xE1);
            try appendByte(out, allocator, @intCast(sid));
            return;
        }
        if (sid <= 0xFFFF + 256) {
            try appendByte(out, allocator, 0xE2);
            const raw: u16 = @intCast(sid - 256);
            var buf: [2]u8 = undefined;
            std.mem.writeInt(u16, &buf, raw, .little);
            try appendSlice(out, allocator, &buf);
            return;
        }
        if (sid <= 0xFFFFFF + 65792) {
            try appendByte(out, allocator, 0xE3);
            const raw: u32 = sid - 65792;
            try appendByte(out, allocator, @intCast(raw & 0xFF));
            try appendByte(out, allocator, @intCast((raw >> 8) & 0xFF));
            try appendByte(out, allocator, @intCast((raw >> 16) & 0xFF));
            return;
        }
        return IonError.Unsupported;
    }
    return IonError.Unsupported;
}

fn writeLob(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), op: u8, bytes: []const u8) IonError!void {
    try appendByte(out, allocator, op);
    try writeFlexUIntShift1(out, allocator, bytes.len);
    try appendSlice(out, allocator, bytes);
}

fn writeSequence(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), short_base: u8, long_op: u8, items: []const value.Element) IonError!void {
    var body = std.ArrayListUnmanaged(u8){};
    defer body.deinit(allocator);
    for (items) |e| try writeElement(allocator, &body, e);

    if (body.items.len <= 15) {
        try appendByte(out, allocator, short_base + @as(u8, @intCast(body.items.len)));
        try appendSlice(out, allocator, body.items);
        return;
    }

    try appendByte(out, allocator, long_op);
    try writeFlexUIntShift1(out, allocator, body.items.len);
    try appendSlice(out, allocator, body.items);
}

fn writeStruct(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), st: value.Struct) IonError!void {
    // For simplicity, always use FlexSym field-name mode:
    // struct-body := FlexUInt(0) then repeated (FlexSym field-name, value-expr).
    var body = std.ArrayListUnmanaged(u8){};
    defer body.deinit(allocator);

    try writeFlexUIntShift1(&body, allocator, 0);
    for (st.fields) |f| {
        try writeFlexSymSymbol(&body, allocator, f.name);
        try writeElement(allocator, &body, f.value);
    }

    if (body.items.len <= 15) {
        try appendByte(out, allocator, 0xD0 + @as(u8, @intCast(body.items.len)));
        try appendSlice(out, allocator, body.items);
        return;
    }

    try appendByte(out, allocator, 0xFD);
    try writeFlexUIntShift1(out, allocator, body.items.len);
    try appendSlice(out, allocator, body.items);
}

fn writeAnnotationsSequence(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), anns: []const value.Symbol) IonError!void {
    if (anns.len == 0) return;

    var all_sid_only = true;
    for (anns) |a| {
        if (a.text != null or a.sid == null) {
            all_sid_only = false;
            break;
        }
    }

    if (all_sid_only) {
        switch (anns.len) {
            1 => {
                try appendByte(out, allocator, 0xE4);
                try writeFlexUIntShift1(out, allocator, anns[0].sid.?);
            },
            2 => {
                try appendByte(out, allocator, 0xE5);
                try writeFlexUIntShift1(out, allocator, anns[0].sid.?);
                try writeFlexUIntShift1(out, allocator, anns[1].sid.?);
            },
            else => {
                var seq = std.ArrayListUnmanaged(u8){};
                defer seq.deinit(allocator);
                for (anns) |a| {
                    try writeFlexUIntShift1(&seq, allocator, a.sid.?);
                }
                try appendByte(out, allocator, 0xE6);
                try writeFlexUIntShift1(out, allocator, seq.items.len);
                try appendSlice(out, allocator, seq.items);
            },
        }
        return;
    }

    switch (anns.len) {
        1 => {
            try appendByte(out, allocator, 0xE7);
            try writeFlexSymSymbol(out, allocator, anns[0]);
        },
        2 => {
            try appendByte(out, allocator, 0xE8);
            try writeFlexSymSymbol(out, allocator, anns[0]);
            try writeFlexSymSymbol(out, allocator, anns[1]);
        },
        else => {
            var seq = std.ArrayListUnmanaged(u8){};
            defer seq.deinit(allocator);
            for (anns) |a| {
                try writeFlexSymSymbol(&seq, allocator, a);
            }
            try appendByte(out, allocator, 0xE9);
            try writeFlexUIntShift1(out, allocator, seq.items.len);
            try appendSlice(out, allocator, seq.items);
        },
    }
}

fn writeFlexSymSymbol(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, sym: value.Symbol) IonError!void {
    if (sym.text) |t| {
        if (!std.unicode.utf8ValidateSlice(t)) return IonError.InvalidIon;
        // FlexSym inline text: FlexInt(-len) then bytes.
        try writeFlexIntShift1(out, allocator, -@as(i64, @intCast(t.len)));
        try appendSlice(out, allocator, t);
        return;
    }
    if (sym.sid) |sid| {
        if (sid == 0) {
            // FlexSym escape: FlexInt(0) then 0x60 => symbol 0.
            try writeFlexIntShift1(out, allocator, 0);
            try appendByte(out, allocator, 0x60);
            return;
        }
        try writeFlexIntShift1(out, allocator, @intCast(sid));
        return;
    }
    return IonError.Unsupported;
}

fn twosComplementIntBytesLe(allocator: std.mem.Allocator, i: value.Int) IonError![]u8 {
    return switch (i) {
        .small => |v| try twosComplementI128BytesLe(allocator, v),
        .big => |p| blk: {
            break :blk twosComplementBigIntConstBytesLe(allocator, p.toConst());
        },
    };
}

fn twosComplementBigIntConstBytesLe(allocator: std.mem.Allocator, c: std.math.big.int.Const) IonError![]u8 {
    if (c.eqlZero()) return allocator.dupe(u8, &.{}) catch return IonError.OutOfMemory;
    const bits_abs = c.bitCountAbs();
    const bit_count: usize = if (c.positive) bits_abs else bits_abs + 1;
    const len: usize = (bit_count + 7) / 8;
    const buf = allocator.alloc(u8, len) catch return IonError.OutOfMemory;
    @memset(buf, if (c.positive) 0x00 else 0xFF);
    c.writeTwosComplement(buf, .little);
    return trimTwosComplementLe(allocator, buf);
}

fn twosComplementI128BytesLe(allocator: std.mem.Allocator, v: i128) IonError![]u8 {
    var buf: [16]u8 = undefined;
    std.mem.writeInt(i128, &buf, v, .little);
    // Trim redundant sign extension bytes from the high end.
    var len: usize = buf.len;
    while (len > 0) {
        const msb = buf[len - 1];
        if (len == 1) break;
        const next_msb = buf[len - 2];
        const sign = (next_msb & 0x80) != 0;
        if (!sign and msb == 0x00) {
            len -= 1;
            continue;
        }
        if (sign and msb == 0xFF) {
            len -= 1;
            continue;
        }
        break;
    }
    if (len == 1 and buf[0] == 0x00) return allocator.dupe(u8, &.{}) catch return IonError.OutOfMemory;
    return allocator.dupe(u8, buf[0..len]) catch return IonError.OutOfMemory;
}

fn trimTwosComplementLe(allocator: std.mem.Allocator, owned: []u8) IonError![]u8 {
    // `owned` is a two's complement little-endian encoding; remove redundant sign-extension bytes.
    if (owned.len == 0) return owned;
    const sign = (owned[owned.len - 1] & 0x80) != 0;
    var len: usize = owned.len;
    while (len > 1) {
        const msb = owned[len - 1];
        const next = owned[len - 2];
        const next_sign = (next & 0x80) != 0;
        if (!sign and msb == 0x00 and !next_sign) {
            len -= 1;
            continue;
        }
        if (sign and msb == 0xFF and next_sign) {
            len -= 1;
            continue;
        }
        break;
    }
    if (len == owned.len) return owned;
    const trimmed = allocator.dupe(u8, owned[0..len]) catch return IonError.OutOfMemory;
    allocator.free(owned);
    return trimmed;
}

fn writeFlexUIntShift1(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, v: usize) IonError!void {
    const raw: u128 = (@as(u128, v) << 1) | 1;
    var tmp = raw;
    while (tmp != 0) : (tmp >>= 8) {
        try appendByte(out, allocator, @intCast(tmp & 0xFF));
    }
}

fn writeFlexIntShift1(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, v: i64) IonError!void {
    const raw_i128: i128 = @as(i128, v) * 2 + 1;
    const bytes = try twosComplementI128BytesLe(allocator, raw_i128);
    defer allocator.free(bytes);
    try appendSlice(out, allocator, bytes);
}

fn appendByte(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, b: u8) IonError!void {
    out.append(allocator, b) catch return IonError.OutOfMemory;
}

fn appendSlice(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, bytes: []const u8) IonError!void {
    out.appendSlice(allocator, bytes) catch return IonError.OutOfMemory;
}
