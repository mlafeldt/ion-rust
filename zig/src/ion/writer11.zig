//! Ion 1.1 binary writer (partial).
//!
//! This targets a value-only subset (no general e-expression/macro emission).
//! For self-contained output, it can emit a minimal module prelude (`set_symbols`) so user symbols
//! can be encoded by address without relying on external module state.
//!
//! Symbol values can be written as either inline text (A0..AF/FA) or as symbol addresses (E1..E3),
//! and system symbols can be referenced using `0xEE` (SystemSymbolAddress).

const std = @import("std");
const ion = @import("../ion.zig");
const value = @import("value.zig");
const symtab = @import("symtab.zig");

const IonError = ion.IonError;

pub const Options = struct {
    /// Controls how symbol values are encoded.
    ///
    /// - `.inline_text_only` writes symbols only as inline text (A0..AF/FA) and rejects
    ///   symbols that do not have text.
    /// - `.addresses` also allows encoding symbols by address (E1..E3) and may use the system
    ///   symbol address opcode `0xEE` when the symbol text matches a known Ion 1.1 system symbol.
    ///
    /// Note: emitting symbol addresses correctly requires module/symbol table context. This writer
    /// can either be given that state via `user_symbol_ids` (for ad-hoc tooling), or it can emit a
    /// minimal `set_symbols` prelude via `writeBinary11SelfContained` to make the output
    /// deterministic and self-contained.
    symbol_encoding: enum { inline_text_only, addresses } = .addresses,

    /// Optional mapping from user symbol text -> module address (SID) for emitting symbol addresses.
    /// When present and `symbol_encoding == .addresses`, symbols with matching `text` will be
    /// encoded using E1..E3 (or FlexSym positive addresses) instead of inline text.
    user_symbol_ids: ?*const std.StringHashMapUnmanaged(u32) = null,
};

pub fn writeBinary11(allocator: std.mem.Allocator, doc: []const value.Element) IonError![]u8 {
    return writeBinary11WithOptions(allocator, doc, .{});
}

pub fn writeBinary11WithOptions(allocator: std.mem.Allocator, doc: []const value.Element, options: Options) IonError![]u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    // Ion 1.1 IVM: E0 01 01 EA
    try appendSlice(&out, allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    for (doc) |e| try writeElement(allocator, &out, options, e);

    return out.toOwnedSlice(allocator) catch return IonError.OutOfMemory;
}

pub fn writeBinary11SelfContained(allocator: std.mem.Allocator, doc: []const value.Element) IonError![]u8 {
    // Emit a minimal module prelude (set_symbols) so non-system symbols can be encoded by address
    // without external module context.
    //
    // This writer keeps a strict contract: it requires `text` for any non-system symbol. SID-only
    // non-system symbols cannot be serialized deterministically in a self-contained stream because
    // their meaning depends on ambient module state.
    var map = std.StringHashMapUnmanaged(u32){};
    defer map.deinit(allocator);
    var user_texts = std.ArrayListUnmanaged([]const u8){};
    defer user_texts.deinit(allocator);

    try collectUserSymbolTexts(allocator, doc, &map, &user_texts);

    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    // Ion 1.1 IVM: E0 01 01 EA
    try appendSlice(&out, allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    if (user_texts.items.len != 0) {
        try writeSetSymbolsDirective(allocator, &out, user_texts.items);
    }

    const opts: Options = .{ .symbol_encoding = .addresses, .user_symbol_ids = &map };
    for (doc) |e| try writeElement(allocator, &out, opts, e);

    return out.toOwnedSlice(allocator) catch return IonError.OutOfMemory;
}

fn writeElement(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), options: Options, e: value.Element) IonError!void {
    if (e.annotations.len != 0) {
        try writeAnnotationsSequence(allocator, out, options, e.annotations);
    }
    try writeValue(allocator, out, options, e.value);
}

fn writeValue(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), options: Options, v: value.Value) IonError!void {
    switch (v) {
        .null => |t| try writeNull(allocator, out, t),
        .bool => |b| try appendByte(out, allocator, if (b) 0x6E else 0x6F),
        .int => |i| try writeInt(allocator, out, i),
        .float => |f| try writeFloat(allocator, out, f),
        .decimal => |d| try writeDecimal(allocator, out, d),
        .string => |s| try writeString(allocator, out, s),
        .symbol => |s| try writeSymbol(allocator, out, options, s),
        .blob => |b| try writeLob(allocator, out, 0xFE, b),
        .clob => |b| try writeLob(allocator, out, 0xFF, b),
        .list => |items| try writeDelimitedList(allocator, out, options, items),
        .sexp => |items| try writeDelimitedSexp(allocator, out, options, items),
        .@"struct" => |st| try writeDelimitedStruct(allocator, out, options, st),
        .timestamp => |ts| try writeTimestamp(allocator, out, ts),
    }
}

fn ionTypeToTypeCode(t: value.IonType) ?u8 {
    return switch (t) {
        .null => null,
        .bool => 0x00,
        .int => 0x01,
        .float => 0x02,
        .decimal => 0x03,
        .timestamp => 0x04,
        .string => 0x05,
        .symbol => 0x06,
        .blob => 0x07,
        .clob => 0x08,
        .list => 0x09,
        .sexp => 0x0A,
        .@"struct" => 0x0B,
    };
}

fn writeNull(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), t: value.IonType) IonError!void {
    if (t == .null) {
        try appendByte(out, allocator, 0xEA);
        return;
    }
    const tc = ionTypeToTypeCode(t) orelse return IonError.InvalidIon;
    try appendByte(out, allocator, 0xEB);
    try appendByte(out, allocator, tc);
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

fn writeTimestamp(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), ts: value.Timestamp) IonError!void {
    // Prefer the short timestamp opcode table when possible. Fall back to long timestamps for
    // unsupported precisions/ranges/offsets.
    if (try writeTimestampShort(allocator, out, ts)) return;

    // Otherwise, use the long timestamp opcode (0xF8) and emit the bit-field payload format that
    // `binary11.decodeTimestampLong11()` expects.
    var payload = std.ArrayListUnmanaged(u8){};
    defer payload.deinit(allocator);
    try encodeTimestampLongPayload(&payload, allocator, ts);

    try appendByte(out, allocator, 0xF8);
    try writeFlexUIntShift1(out, allocator, payload.items.len);
    try appendSlice(out, allocator, payload.items);
}

fn writeTimestampShort(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), ts: value.Timestamp) IonError!bool {
    // Supports short timestamp codes 0..5:
    // - 0: year
    // - 1: month
    // - 2: day
    // - 3: minute (UTC or unknown offset)
    // - 4: second (UTC or unknown offset)
    // - 5: milliseconds (UTC or unknown offset)
    //
    // For other precisions/offsets, return false and let the caller use the long form.
    if (ts.year < 1970 or ts.year > 2097) return false;

    const year_diff: u8 = @intCast(ts.year - 1970);

    // Helper to build byte payloads that match `binary11.decodeTimestampShort11()`.
    const setBitsU16At = struct {
        fn run(bytes: []u8, offset: usize, mask: u16, v: u16) void {
            const cur = std.mem.readInt(u16, @as(*const [2]u8, @ptrCast(bytes[offset .. offset + 2].ptr)), .little);
            const shift: u4 = @intCast(@ctz(mask));
            const next = (cur & ~mask) | ((v << shift) & mask);
            std.mem.writeInt(u16, @as(*[2]u8, @ptrCast(bytes[offset .. offset + 2].ptr)), next, .little);
        }
    }.run;
    const setBitsU32At = struct {
        fn run(bytes: []u8, offset: usize, mask: u32, v: u32) void {
            const cur = std.mem.readInt(u32, @as(*const [4]u8, @ptrCast(bytes[offset .. offset + 4].ptr)), .little);
            const shift: u5 = @intCast(@ctz(mask));
            const next = (cur & ~mask) | ((v << shift) & mask);
            std.mem.writeInt(u32, @as(*[4]u8, @ptrCast(bytes[offset .. offset + 4].ptr)), next, .little);
        }
    }.run;

    switch (ts.precision) {
        .year => {
            // 80 + 0, payload size 1.
            try appendByte(out, allocator, 0x80);
            try appendByte(out, allocator, year_diff & 0x7F);
            return true;
        },
        .month => {
            const month = ts.month orelse return IonError.InvalidIon;
            if (month < 1 or month > 12) return IonError.InvalidIon;
            // 80 + 1, payload size 2.
            try appendByte(out, allocator, 0x81);
            try appendByte(out, allocator, (year_diff & 0x7F) | ((month & 0x01) << 7));
            try appendByte(out, allocator, @intCast((month >> 1) & 0x07));
            return true;
        },
        .day => {
            const month = ts.month orelse return IonError.InvalidIon;
            const day = ts.day orelse return IonError.InvalidIon;
            if (month < 1 or month > 12) return IonError.InvalidIon;
            if (day < 1 or day > 31) return IonError.InvalidIon;
            // 80 + 2, payload size 2.
            try appendByte(out, allocator, 0x82);
            try appendByte(out, allocator, (year_diff & 0x7F) | ((month & 0x01) << 7));
            try appendByte(out, allocator, @as(u8, @intCast((month >> 1) & 0x07)) | ((day & 0x1F) << 3));
            return true;
        },
        .minute, .second, .fractional => {
            const month = ts.month orelse return IonError.InvalidIon;
            const day = ts.day orelse return IonError.InvalidIon;
            const hour = ts.hour orelse return IonError.InvalidIon;
            const minute = ts.minute orelse return IonError.InvalidIon;
            if (month < 1 or month > 12) return IonError.InvalidIon;
            if (day < 1 or day > 31) return IonError.InvalidIon;
            if (hour > 23 or minute > 59) return IonError.InvalidIon;

            // If a known offset is present and representable, emit the known-offset short codes.
            if (ts.offset_minutes) |off| {
                if (@mod(off, @as(i16, 15)) == 0) {
                    const off_i32: i32 = off;
                    // Decoder uses: offset = off_mult*15 - (14*60). So off_mult = (offset + 840)/15.
                    const biased = off_i32 + 14 * 60;
                    if (biased >= 0 and @mod(biased, 15) == 0) {
                        const off_mult: i32 = @divTrunc(biased, 15);
                        if (off_mult >= 0 and off_mult <= 127) {
                            const fixed_len: usize = switch (ts.precision) {
                                .minute => 5,
                                .second => 5,
                                .fractional => 7, // ms only; else fall back to long
                                else => unreachable,
                            };
                            var buf = [_]u8{0} ** 7;
                            const payload = buf[0..fixed_len];

                            // year/month/day
                            payload[0] = (year_diff & 0x7F) | ((month & 0x01) << 7);
                            payload[1] = @as(u8, @intCast((month >> 1) & 0x07)) | ((day & 0x1F) << 3);
                            // hour/minute
                            payload[2] = (hour & 0x1F) | ((minute & 0x07) << 5);
                            payload[3] = @intCast((minute >> 3) & 0x07); // minute high bits in bits0..2

                            // offset multiple in u16 at payload[3..5], mask 0x03F8 (bits3..9)
                            setBitsU16At(payload, 3, 0x03F8, @intCast(off_mult));

                            if (ts.precision == .minute) {
                                try appendByte(out, allocator, 0x88);
                                try appendSlice(out, allocator, payload);
                                return true;
                            }

                            const sec = ts.second orelse return IonError.InvalidIon;
                            if (sec > 59) return IonError.InvalidIon;
                            // seconds: payload[4] >> 2
                            payload[4] = (payload[4] & 0x03) | (@as(u8, @intCast(sec)) << 2);

                            if (ts.precision == .second) {
                                try appendByte(out, allocator, 0x89);
                                try appendSlice(out, allocator, payload);
                                return true;
                            }

                            const frac = ts.fractional orelse return IonError.InvalidIon;
                            if (frac.is_negative) return IonError.InvalidIon;
                            if (frac.exponent != -3) return false;
                            const ms_u16: u16 = switch (frac.coefficient) {
                                .small => |v| blk: {
                                    if (v < 0) return IonError.InvalidIon;
                                    if (v > 1023) return false;
                                    break :blk @intCast(v);
                                },
                                .big => return false,
                            };
                            // ms bits: u16 at payload[5..7], mask 0x03FF
                            setBitsU16At(payload, 5, 0x03FF, ms_u16);
                            try appendByte(out, allocator, 0x8A);
                            try appendSlice(out, allocator, payload);
                            return true;
                        }
                    }
                }
                // Non-zero/non-representable offsets: use long timestamp.
                return false;
            }

            const is_utc: bool = ts.offset_minutes != null;

            // Base 2 bytes: year/month/day
            const b0: u8 = (year_diff & 0x7F) | ((month & 0x01) << 7);
            const b1: u8 = @as(u8, @intCast((month >> 1) & 0x07)) | ((day & 0x1F) << 3);

            // Next 2 bytes: hour/minute + is_utc in payload[3] bit3.
            const b2: u8 = (hour & 0x1F) | ((minute & 0x07) << 5);
            var b3: u8 = @intCast((minute >> 3) & 0x07);
            if (is_utc) b3 |= 0x08;

            if (ts.precision == .minute) {
                // 80 + 3, payload size 4.
                try appendByte(out, allocator, 0x83);
                try appendByte(out, allocator, b0);
                try appendByte(out, allocator, b1);
                try appendByte(out, allocator, b2);
                try appendByte(out, allocator, b3);
                return true;
            }

            const sec = ts.second orelse return IonError.InvalidIon;
            if (sec > 59) return IonError.InvalidIon;
            // Seconds occupy bits 4..9 of u16 at payload[3..5]:
            // - low 4 bits in payload[3] bits 4..7
            // - high 2 bits in payload[4] bits 0..1
            b3 |= (sec & 0x0F) << 4;
            var b4: u8 = @intCast((sec >> 4) & 0x03);

            if (ts.precision == .second) {
                // 80 + 4, payload size 5.
                try appendByte(out, allocator, 0x84);
                try appendByte(out, allocator, b0);
                try appendByte(out, allocator, b1);
                try appendByte(out, allocator, b2);
                try appendByte(out, allocator, b3);
                try appendByte(out, allocator, b4);
                return true;
            }

            // Milliseconds only: exponent -3 and coefficient fits in the short table (0..1023).
            const frac = ts.fractional orelse return IonError.InvalidIon;
            if (frac.is_negative) return IonError.InvalidIon;
            if (frac.exponent == -3) {
                const ms_u16: u16 = switch (frac.coefficient) {
                    .small => |v| blk: {
                        if (v < 0) return IonError.InvalidIon;
                        if (v > 1023) return false;
                        break :blk @intCast(v);
                    },
                    .big => return false,
                };

                // Milliseconds occupy bits 2..11 of u16 at payload[4..6]:
                // - payload[4] bits 2..7 = low 6 bits
                // - payload[5] bits 0..3 = high 4 bits
                b4 |= @as(u8, @intCast((ms_u16 & 0x3F) << 2));
                const b5: u8 = @intCast((ms_u16 >> 6) & 0x0F);

                // 80 + 5, payload size 6.
                try appendByte(out, allocator, 0x85);
                try appendByte(out, allocator, b0);
                try appendByte(out, allocator, b1);
                try appendByte(out, allocator, b2);
                try appendByte(out, allocator, b3);
                try appendByte(out, allocator, b4);
                try appendByte(out, allocator, b5);
                return true;
            }

            if (frac.exponent == -6) {
                const us_u32: u32 = switch (frac.coefficient) {
                    .small => |v| blk: {
                        if (v < 0) return IonError.InvalidIon;
                        if (v > 1_048_575) return false; // 20 bits
                        break :blk @intCast(v);
                    },
                    .big => return false,
                };
                var payload = [_]u8{0} ** 7;
                payload[0] = b0;
                payload[1] = b1;
                payload[2] = b2;
                payload[3] = b3;
                payload[4] = b4;
                // us bits live in u32 at payload[3..7], mask 0x3FFF_FC00
                setBitsU32At(&payload, 3, 0x3FFF_FC00, us_u32);
                try appendByte(out, allocator, 0x86);
                try appendSlice(out, allocator, &payload);
                return true;
            }

            if (frac.exponent == -9) {
                const ns_u32: u32 = switch (frac.coefficient) {
                    .small => |v| blk: {
                        if (v < 0) return IonError.InvalidIon;
                        if (v > 999_999_999) return false;
                        break :blk @intCast(v);
                    },
                    .big => return false,
                };
                var payload = [_]u8{0} ** 8;
                payload[0] = b0;
                payload[1] = b1;
                payload[2] = b2;
                payload[3] = b3;
                payload[4] = b4; // includes seconds high bits in bits0..1
                // ns bits live in u32 at payload[4..8], bits2..31. Encode as (ns<<2).
                const raw: u32 = ns_u32 << 2;
                std.mem.writeInt(u32, @as(*[4]u8, @ptrCast(payload[4..8].ptr)), raw, .little);
                // Re-apply seconds bits (payload[4] bits0..1) after overwriting u32.
                payload[4] = (payload[4] & 0xFC) | (b4 & 0x03);
                try appendByte(out, allocator, 0x87);
                try appendSlice(out, allocator, &payload);
                return true;
            }

            return false;
        },
    }
}

fn encodeTimestampLongPayload(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, ts: value.Timestamp) IonError!void {
    if (ts.year < 0 or ts.year > 0x3FFF) return IonError.InvalidIon;

    const fixed_len: usize = switch (ts.precision) {
        .year => 2,
        .month, .day => 3,
        .minute => 6,
        .second => 7,
        .fractional => 7, // scale + coeff appended after the fixed header
    };

    const buf = try allocator.alloc(u8, fixed_len);
    defer allocator.free(buf);
    @memset(buf, 0);

    const setBitsU16At = struct {
        fn run(bytes: []u8, offset: usize, mask: u16, v: u16) void {
            const cur = std.mem.readInt(u16, @as(*const [2]u8, @ptrCast(bytes[offset .. offset + 2].ptr)), .little);
            const shift: u4 = @intCast(@ctz(mask));
            const next = (cur & ~mask) | ((v << shift) & mask);
            std.mem.writeInt(u16, @as(*[2]u8, @ptrCast(bytes[offset .. offset + 2].ptr)), next, .little);
        }
    }.run;

    // year: low 14 bits of payload[0..2]
    setBitsU16At(buf, 0, 0x3FFF, @intCast(ts.year));
    if (ts.precision == .year) {
        try appendSlice(out, allocator, buf);
        return;
    }

    const month = ts.month orelse return IonError.InvalidIon;
    if (month < 1 or month > 12) return IonError.InvalidIon;
    // month: bits 6..9 of u16 at payload[1..3]
    setBitsU16At(buf, 1, 0x03C0, @intCast(month));

    const day: u8 = if (ts.precision == .month) 0 else (ts.day orelse return IonError.InvalidIon);
    if (ts.precision != .month) {
        if (day < 1 or day > 31) return IonError.InvalidIon;
    }
    // day: payload[2] bits 2..6
    buf[2] = (buf[2] & ~@as(u8, 0x7C)) | ((day & 0x1F) << 2);

    if (ts.precision == .month or ts.precision == .day) {
        try appendSlice(out, allocator, buf);
        return;
    }

    const hour = ts.hour orelse return IonError.InvalidIon;
    const minute = ts.minute orelse return IonError.InvalidIon;
    if (hour > 23 or minute > 59) return IonError.InvalidIon;

    const off_bits: u16 = blk: {
        if (ts.offset_minutes) |off| {
            if (off < -1440 or off > 1439) return IonError.InvalidIon;
            const tmp: i32 = @as(i32, off) + 1440;
            if (tmp == 0x0FFF) return IonError.InvalidIon; // reserved for unknown offset
            break :blk @intCast(tmp);
        } else {
            break :blk 0x0FFF; // unknown offset
        }
    };

    // hour: bits 7..11 of u16 at payload[2..4]
    setBitsU16At(buf, 2, 0x0F80, @intCast(hour));
    // minute: bits 4..9 of u16 at payload[3..5]
    setBitsU16At(buf, 3, 0x03F0, @intCast(minute));
    // offset bits: bits 2..13 of u16 at payload[4..6]
    setBitsU16At(buf, 4, 0x3FFC, off_bits);

    if (ts.precision == .minute) {
        try appendSlice(out, allocator, buf);
        return;
    }

    const sec = ts.second orelse return IonError.InvalidIon;
    if (sec > 59) return IonError.InvalidIon;
    // seconds: bits 6..11 of u16 at payload[5..7]
    setBitsU16At(buf, 5, 0x0FC0, @intCast(sec));

    try appendSlice(out, allocator, buf);
    if (ts.precision == .second) return;

    const frac = ts.fractional orelse return IonError.InvalidIon;
    if (frac.is_negative) return IonError.InvalidIon;
    if (frac.exponent > 0) return IonError.InvalidIon;
    const scale: usize = @intCast(-frac.exponent);
    try writeFlexUIntShift1(out, allocator, scale);

    switch (frac.coefficient) {
        .small => |v| {
            if (v < 0) return IonError.InvalidIon;
            const coeff_u128: u128 = @intCast(v);
            if (coeff_u128 == 0) return;
            var coeff_buf: [16]u8 = undefined;
            std.mem.writeInt(u128, &coeff_buf, coeff_u128, .little);
            var coeff_len: usize = 16;
            while (coeff_len > 0 and coeff_buf[coeff_len - 1] == 0) : (coeff_len -= 1) {}
            try appendSlice(out, allocator, coeff_buf[0..coeff_len]);
        },
        .big => |p| {
            // Ion 1.1 long timestamps store fractional seconds coefficient as a fixed-width unsigned
            // integer byte sequence (little-endian). Support arbitrary-sized coefficients by writing
            // the BigInt magnitude directly (no string conversions).
            const c = p.toConst();
            if (!c.positive) return IonError.InvalidIon;
            try appendFixedUIntMagnitudeLe(out, allocator, c);
        },
    }
}

fn writeFloat(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), f: f64) IonError!void {
    // Prefer the narrower float encodings when the value is exactly representable.
    if (f == 0.0 and !std.math.signbit(f)) {
        try appendByte(out, allocator, 0x6A);
        return;
    }

    // Preserve NaN/Inf bit patterns by defaulting to f64.
    if (!std.math.isFinite(f)) {
        try appendByte(out, allocator, 0x6D);
        var buf: [8]u8 = undefined;
        std.mem.writeInt(u64, &buf, @bitCast(f), .little);
        try appendSlice(out, allocator, &buf);
        return;
    }

    const hf: f16 = @floatCast(f);
    if (@as(f64, @floatCast(hf)) == f) {
        try appendByte(out, allocator, 0x6B);
        var buf: [2]u8 = undefined;
        std.mem.writeInt(u16, &buf, @bitCast(hf), .little);
        try appendSlice(out, allocator, &buf);
        return;
    }

    const f32v: f32 = @floatCast(f);
    if (@as(f64, @floatCast(f32v)) == f) {
        try appendByte(out, allocator, 0x6C);
        var buf: [4]u8 = undefined;
        std.mem.writeInt(u32, &buf, @bitCast(f32v), .little);
        try appendSlice(out, allocator, &buf);
        return;
    }

    try appendByte(out, allocator, 0x6D);
    var buf: [8]u8 = undefined;
    std.mem.writeInt(u64, &buf, @bitCast(f), .little);
    try appendSlice(out, allocator, &buf);
}

fn appendFixedUIntMagnitudeLe(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, c: std.math.big.int.Const) IonError!void {
    if (!c.positive) return IonError.InvalidIon;
    const bits = c.bitCountAbs();
    const byte_len: usize = (bits + 7) / 8;
    if (byte_len == 0) return;

    const old_len = out.items.len;
    const dst = out.addManyAsSlice(allocator, byte_len) catch return IonError.OutOfMemory;
    @memset(dst, 0);
    c.writeTwosComplement(dst, .little);
    var used = byte_len;
    while (used > 0 and dst[used - 1] == 0) : (used -= 1) {}
    out.items.len = old_len + used;
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

fn writeSymbol(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), options: Options, s: value.Symbol) IonError!void {
    if (s.text) |t| {
        if (!std.unicode.utf8ValidateSlice(t)) return IonError.InvalidIon;
        if (options.symbol_encoding == .addresses) {
            if (symtab.SystemSymtab11.sidForText(t)) |sys_sid| {
                if (sys_sid <= 0xFF) {
                    // System symbol address: EE <addr>
                    try appendByte(out, allocator, 0xEE);
                    try appendByte(out, allocator, @intCast(sys_sid));
                    return;
                }
            }
            if (options.user_symbol_ids) |m| {
                if (m.get(t)) |sid| {
                    try writeSymbolAddress(out, allocator, sid);
                    return;
                }
            }
        }
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

    if (options.symbol_encoding == .inline_text_only) {
        // We don't have module/symbol-address state in this mode, but we can still inline known
        // Ion 1.1 system symbol texts by SID.
        if (s.sid) |sid| {
            if (sid > 0 and sid <= symtab.SystemSymtab11.max_id) {
                if (symtab.SystemSymtab11.textForSid(sid)) |sys_text| {
                    if (!std.unicode.utf8ValidateSlice(sys_text)) return IonError.InvalidIon;
                    if (sys_text.len <= 15) {
                        try appendByte(out, allocator, 0xA0 + @as(u8, @intCast(sys_text.len)));
                        try appendSlice(out, allocator, sys_text);
                        return;
                    }

                    try appendByte(out, allocator, 0xFA);
                    try writeFlexUIntShift1(out, allocator, sys_text.len);
                    try appendSlice(out, allocator, sys_text);
                    return;
                }
            }
        }
        return IonError.InvalidIon;
    }

    if (s.sid) |sid| {
        if (options.symbol_encoding == .inline_text_only) return IonError.InvalidIon;

        // If the caller provided an SID-only system symbol, encode it as a system symbol address.
        // This keeps the output self-contained and avoids depending on ambient module state.
        if (sid > 0 and sid <= symtab.SystemSymtab11.max_id and sid <= 0xFF) {
            try appendByte(out, allocator, 0xEE);
            try appendByte(out, allocator, @intCast(sid));
            return;
        }

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
        // Ion 1.1 symbol address opcodes only allow 1-, 2-, or 3-byte fixed UInt payloads (with
        // biases). Larger SIDs cannot be represented and are invalid Ion.
        return IonError.InvalidIon;
    }
    return IonError.InvalidIon;
}

fn writeSymbolAddress(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, sid: u32) IonError!void {
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
    return IonError.InvalidIon;
}

fn writeLob(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), op: u8, bytes: []const u8) IonError!void {
    try appendByte(out, allocator, op);
    try writeFlexUIntShift1(out, allocator, bytes.len);
    try appendSlice(out, allocator, bytes);
}

fn writeDelimitedList(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), options: Options, items: []const value.Element) IonError!void {
    try appendByte(out, allocator, 0xF1);
    for (items) |e| try writeElement(allocator, out, options, e);
    try appendByte(out, allocator, 0xF0);
}

fn writeDelimitedSexp(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), options: Options, items: []const value.Element) IonError!void {
    try appendByte(out, allocator, 0xF2);
    for (items) |e| try writeElement(allocator, out, options, e);
    try appendByte(out, allocator, 0xF0);
}

fn writeDelimitedStruct(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), options: Options, st: value.Struct) IonError!void {
    try appendByte(out, allocator, 0xF3);
    for (st.fields) |f| {
        try writeFlexSymSymbol(out, allocator, options, f.name);
        try writeElement(allocator, out, options, f.value);
    }
    // Delimited struct close marker: FlexSym escape F0.
    try writeFlexIntShift1(out, allocator, 0);
    try appendByte(out, allocator, 0xF0);
}

fn writeSequence(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), options: Options, short_base: u8, long_op: u8, items: []const value.Element) IonError!void {
    var body = std.ArrayListUnmanaged(u8){};
    defer body.deinit(allocator);
    for (items) |e| try writeElement(allocator, &body, options, e);

    if (body.items.len <= 15) {
        try appendByte(out, allocator, short_base + @as(u8, @intCast(body.items.len)));
        try appendSlice(out, allocator, body.items);
        return;
    }

    try appendByte(out, allocator, long_op);
    try writeFlexUIntShift1(out, allocator, body.items.len);
    try appendSlice(out, allocator, body.items);
}

fn writeStruct(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), options: Options, st: value.Struct) IonError!void {
    // For simplicity, always use FlexSym field-name mode:
    // struct-body := FlexUInt(0) then repeated (FlexSym field-name, value-expr).
    var body = std.ArrayListUnmanaged(u8){};
    defer body.deinit(allocator);

    try writeFlexUIntShift1(&body, allocator, 0);
    for (st.fields) |f| {
        try writeFlexSymSymbol(&body, allocator, options, f.name);
        try writeElement(allocator, &body, options, f.value);
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

fn writeAnnotationsSequence(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), options: Options, anns: []const value.Symbol) IonError!void {
    if (anns.len == 0) return;

    if (options.symbol_encoding == .inline_text_only) {
        switch (anns.len) {
            1 => {
                try appendByte(out, allocator, 0xE7);
                try writeFlexSymSymbol(out, allocator, options, anns[0]);
            },
            2 => {
                try appendByte(out, allocator, 0xE8);
                try writeFlexSymSymbol(out, allocator, options, anns[0]);
                try writeFlexSymSymbol(out, allocator, options, anns[1]);
            },
            else => {
                var seq = std.ArrayListUnmanaged(u8){};
                defer seq.deinit(allocator);
                for (anns) |a| {
                    try writeFlexSymSymbol(&seq, allocator, options, a);
                }
                try appendByte(out, allocator, 0xE9);
                try writeFlexUIntShift1(out, allocator, seq.items.len);
                try appendSlice(out, allocator, seq.items);
            },
        }
        return;
    }

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
            try writeFlexSymSymbol(out, allocator, options, anns[0]);
        },
        2 => {
            try appendByte(out, allocator, 0xE8);
            try writeFlexSymSymbol(out, allocator, options, anns[0]);
            try writeFlexSymSymbol(out, allocator, options, anns[1]);
        },
        else => {
            var seq = std.ArrayListUnmanaged(u8){};
            defer seq.deinit(allocator);
            for (anns) |a| {
                try writeFlexSymSymbol(&seq, allocator, options, a);
            }
            try appendByte(out, allocator, 0xE9);
            try writeFlexUIntShift1(out, allocator, seq.items.len);
            try appendSlice(out, allocator, seq.items);
        },
    }
}

fn writeFlexSymSymbol(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, options: Options, sym: value.Symbol) IonError!void {
    if (sym.text) |t| {
        if (!std.unicode.utf8ValidateSlice(t)) return IonError.InvalidIon;
        if (options.symbol_encoding == .addresses) {
            if (symtab.SystemSymtab11.sidForText(t)) |sys_sid| {
                if (sys_sid >= 1 and sys_sid <= 0x80) {
                    // FlexSym escape: FlexInt(0) then 0x60 + <addr>.
                    try writeFlexIntShift1(out, allocator, 0);
                    try appendByte(out, allocator, @intCast(0x60 + sys_sid));
                    return;
                }
            }
            if (options.user_symbol_ids) |m| {
                if (m.get(t)) |sid| {
                    try writeFlexIntShift1(out, allocator, @intCast(sid));
                    return;
                }
            }
        }
        // FlexSym inline text: FlexInt(-len) then bytes.
        try writeFlexIntShift1(out, allocator, -@as(i64, @intCast(t.len)));
        try appendSlice(out, allocator, t);
        return;
    }
    if (sym.sid) |sid| {
        if (options.symbol_encoding == .inline_text_only) {
            if (sid > 0 and sid <= symtab.SystemSymtab11.max_id) {
                const sys_text = symtab.SystemSymtab11.textForSid(sid) orelse return IonError.InvalidIon;
                if (!std.unicode.utf8ValidateSlice(sys_text)) return IonError.InvalidIon;
                try writeFlexIntShift1(out, allocator, -@as(i64, @intCast(sys_text.len)));
                try appendSlice(out, allocator, sys_text);
                return;
            }
            return IonError.InvalidIon;
        }
        if (sid == 0) {
            // FlexSym escape: FlexInt(0) then 0x60 => symbol 0.
            try writeFlexIntShift1(out, allocator, 0);
            try appendByte(out, allocator, 0x60);
            return;
        }
        try writeFlexIntShift1(out, allocator, @intCast(sid));
        return;
    }
    return IonError.InvalidIon;
}

fn writeSetSymbolsDirective(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), user_texts: []const []const u8) IonError!void {
    // Encode a system macro invocation:
    //   (:$ion::set_symbols <text*>)
    // using the conformance-style encoding that our binary reader accepts:
    //   EF 13 <presence> <args...>
    // where presence is:
    //   0 => no args
    //   1 => single tagged value
    //   2 => tagged expression group
    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, 0x13); // system macro address 19

    if (user_texts.len == 0) {
        try appendByte(out, allocator, 0x00);
        return;
    }
    if (user_texts.len == 1) {
        try appendByte(out, allocator, 0x01);
        try writeString(allocator, out, user_texts[0]);
        return;
    }

    var payload = std.ArrayListUnmanaged(u8){};
    defer payload.deinit(allocator);
    for (user_texts) |t| {
        try writeString(allocator, &payload, t);
    }

    try appendByte(out, allocator, 0x02);
    try writeFlexUIntShift1(out, allocator, payload.items.len);
    try appendSlice(out, allocator, payload.items);
}

fn collectUserSymbolTexts(
    allocator: std.mem.Allocator,
    elems: []const value.Element,
    map: *std.StringHashMapUnmanaged(u32),
    out_texts: *std.ArrayListUnmanaged([]const u8),
) IonError!void {
    var next_sid: u32 = 1;

    const addText = struct {
        fn run(alloc: std.mem.Allocator, m: *std.StringHashMapUnmanaged(u32), texts: *std.ArrayListUnmanaged([]const u8), next: *u32, t: []const u8) IonError!void {
            if (symtab.SystemSymtab11.sidForText(t) != null) return;
            if (m.contains(t)) return;
            m.put(alloc, t, next.*) catch return IonError.OutOfMemory;
            texts.append(alloc, t) catch return IonError.OutOfMemory;
            next.* += 1;
        }
    }.run;

    const validateSidOnly = struct {
        fn run(sym: value.Symbol) IonError!void {
            if (sym.text != null) return;
            if (sym.sid) |sid| {
                // Allow SID-only system symbols; everything else requires text for self-contained output.
                if (sid > 0 and sid <= symtab.SystemSymtab11.max_id) return;
                return IonError.InvalidIon;
            }
            return IonError.InvalidIon;
        }
    }.run;

    const walkElement = struct {
        fn run(
            alloc: std.mem.Allocator,
            m: *std.StringHashMapUnmanaged(u32),
            texts: *std.ArrayListUnmanaged([]const u8),
            next: *u32,
            e: value.Element,
        ) IonError!void {
            for (e.annotations) |a| {
                if (a.text) |t| try addText(alloc, m, texts, next, t) else try validateSidOnly(a);
            }
            switch (e.value) {
                .symbol => |s| {
                    if (s.text) |t| try addText(alloc, m, texts, next, t) else try validateSidOnly(s);
                },
                .list => |items| for (items) |child| try run(alloc, m, texts, next, child),
                .sexp => |items| for (items) |child| try run(alloc, m, texts, next, child),
                .@"struct" => |st| {
                    for (st.fields) |f| {
                        if (f.name.text) |t| try addText(alloc, m, texts, next, t) else try validateSidOnly(f.name);
                        try run(alloc, m, texts, next, f.value);
                    }
                },
                .null, .bool, .int, .float, .decimal, .timestamp, .string, .blob, .clob => {},
            }
        }
    }.run;

    for (elems) |e| try walkElement(allocator, map, out_texts, &next_sid, e);
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
    // For positive values whose top byte would have the sign bit set (e.g. 2^127), we need at
    // least one extra 0x00 sign-extension byte to keep the two's complement encoding positive.
    // Similarly, for negative values we may need additional 0xFF sign-extension bytes. We
    // over-allocate by one byte and then trim redundant sign extension.
    const bits_abs = c.bitCountAbs();
    const len_min: usize = (bits_abs + 7) / 8;
    const len: usize = len_min + 1;
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
    // FlexUInt encoding uses a tag bit that is the least-significant set bit of the underlying
    // little-endian integer. If the tag bit is at position (N-1), the encoding is N bytes long and
    // the value is obtained by shifting right by N bits.
    //
    // This means each byte contributes 7 payload bits. Choose the minimal byte length that can
    // represent `v`.
    const uv: u128 = @intCast(v);
    const bits: usize = if (v == 0) 0 else (usize_bits: {
        const lz: usize = @intCast(@clz(uv));
        break :usize_bits 128 - lz;
    });
    const n: usize = @max(@as(usize, 1), (bits + 6) / 7);

    const tag: u128 = @as(u128, 1) << @intCast(n - 1);
    const raw: u128 = (uv << @intCast(n)) | tag;
    var i: usize = 0;
    while (i < n) : (i += 1) {
        try appendByte(out, allocator, @intCast((raw >> @intCast(i * 8)) & 0xFF));
    }
}

fn writeFlexIntShift1(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, v: i64) IonError!void {
    // FlexInt is the signed analogue of FlexUInt: N bytes encode a signed value occupying 7*N bits.
    // The tag bit is at position (N-1) and the value is recovered by shifting right by N.
    var n: usize = 1;
    while (true) : (n += 1) {
        if (n > 10) return IonError.InvalidIon; // i64 fits in <=10 bytes (70 payload bits).
        const width: usize = n * 7;
        const mag_bits: usize = width - 1;
        if (mag_bits >= 63) break;
        const max: i64 = (@as(i64, 1) << @intCast(mag_bits)) - 1;
        const min: i64 = -(@as(i64, 1) << @intCast(mag_bits));
        if (v >= min and v <= max) break;
    }

    const width: usize = n * 7;
    const mask: u128 = (@as(u128, 1) << @intCast(width)) - 1;
    const payload_twos: u128 = @as(u128, @bitCast(@as(i128, v))) & mask;
    const tag: u128 = @as(u128, 1) << @intCast(n - 1);
    const raw: u128 = (payload_twos << @intCast(n)) | tag;
    var i: usize = 0;
    while (i < n) : (i += 1) {
        try appendByte(out, allocator, @intCast((raw >> @intCast(i * 8)) & 0xFF));
    }
}

fn appendByte(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, b: u8) IonError!void {
    out.append(allocator, b) catch return IonError.OutOfMemory;
}

fn appendSlice(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, bytes: []const u8) IonError!void {
    out.appendSlice(allocator, bytes) catch return IonError.OutOfMemory;
}
