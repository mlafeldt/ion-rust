//! Ion writer (text + binary) for the Zig port.
//!
//! - Binary writer:
//!   - Emits the Ion 1.0 IVM.
//!   - Emits a simple local symbol table for encountered symbol text.
//!   - Writes values using Ion binary encodings for supported types.
//! - Text writer:
//!   - Produces legal Ion text consumable by the text parser and ion-tests.
//!   - Uses `\\xNN` escapes for non-ASCII bytes in clobs.
//!   - Avoids accidental string literal concatenation by alternating short/long string forms
//!     for adjacent string values at top-level and in sexps.

const std = @import("std");
const ion = @import("../ion.zig");
const value = @import("value.zig");
const symtab = @import("symtab.zig");

const IonError = ion.IonError;

const FixedSymtab = struct {
    /// Number of local symbol slots reserved after the system table.
    /// Local SIDs are `SystemSymtab.max_id + 1 + index`.
    slots: []?[]const u8,
};

fn appendByte(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, b: u8) IonError!void {
    out.append(allocator, b) catch return IonError.OutOfMemory;
}

fn appendSlice(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, bytes: []const u8) IonError!void {
    out.appendSlice(allocator, bytes) catch return IonError.OutOfMemory;
}

fn appendUninit(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, len: usize) IonError![]u8 {
    return out.addManyAsSlice(allocator, len) catch return IonError.OutOfMemory;
}

/// Serializes top-level Ion elements to Ion binary (Ion 1.0).
///
/// Ownership: returns an allocated `[]u8` owned by `allocator`; caller must free it.
pub fn writeBinary(allocator: std.mem.Allocator, doc: []const value.Element) IonError![]u8 {
    var intern = try SymbolIntern.init(allocator);
    defer intern.deinit(allocator);
    try intern.collectFromElements(doc);

    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    // IVM
    try appendSlice(&out, allocator, &.{ 0xE0, 0x01, 0x00, 0xEA });

    // Emit a local symbol table if needed.
    if (intern.fixed.slots.len != 0 or intern.new_symbols.items.len != 0) {
        try writeLocalSymtabBinary(allocator, &out, &intern);
    }

    for (doc) |elem| try writeElementBinary(allocator, &out, &intern, elem);

    return out.toOwnedSlice(allocator) catch return IonError.OutOfMemory;
}

/// Serializes top-level Ion elements to Ion text.
///
/// Note: this writer intentionally does not attempt to preserve the original textual
/// representation. It produces a legal text form suitable for parsing and roundtrips.
///
/// Ownership: returns an allocated `[]u8` owned by `allocator`; caller must free it.
pub fn writeText(allocator: std.mem.Allocator, doc: []const value.Element) IonError![]u8 {
    return writeTextImpl(allocator, doc, .roundtrip);
}

/// Serializes top-level Ion elements to Ion text for use by the Ion 1.1 conformance DSL runner.
///
/// Unlike `writeText`, this does *not* auto-insert a synthetic `$ion_symbol_table` import to
/// make `$<sid>` tokens parseable. The conformance suite relies on invalid/out-of-range symbol
/// addresses to signal errors, so we must not "helpfully" make them parseable here.
pub fn writeTextConformance(allocator: std.mem.Allocator, doc: []const value.Element) IonError![]u8 {
    return writeTextImpl(allocator, doc, .conformance);
}

const TextMode = enum { roundtrip, conformance };

fn writeTextImpl(allocator: std.mem.Allocator, doc: []const value.Element, mode: TextMode) IonError![]u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    if (mode == .roundtrip) {
        if (maxUnknownLocalSid(doc)) |max_sid| {
            const max_id: u32 = max_sid - symtab.SystemSymtab.max_id;
            // Emit a minimal symbol table that makes `$<sid>` tokens parseable as unknown symbols
            // without materializing a gigantic `symbols:[null, null, ...]` list.
            //
            // We intentionally use an import to a likely-nonexistent shared table; if the reader
            // doesn't have it, the imported slots remain unknown (which is what `$<sid>` encodes).
            var buf: [128]u8 = undefined;
            const header = std.fmt.bufPrint(
                &buf,
                "'$ion_symbol_table'::{{imports:[{{name:\"$ion_symbol_table\",version:1,max_id:{d}}}]}}",
                .{max_id},
            ) catch return IonError.InvalidIon;
            try appendSlice(&out, allocator, header);
            try appendByte(&out, allocator, '\n');
        }
    }

    var first: bool = true;
    var prev_was_string: bool = false;
    var last_string_style: StringStyle = .short;
    for (doc) |elem| {
        if (!first) try appendByte(&out, allocator, '\n');
        first = false;
        if (elem.value == .string) {
            const style: StringStyle = if (prev_was_string) blk: {
                break :blk switch (last_string_style) {
                    .short => .long,
                    .long => .short,
                };
            } else .short;
            last_string_style = style;
            prev_was_string = true;
            try writeElementTextStringStyle(allocator, &out, elem, style);
        } else {
            prev_was_string = false;
            try writeElementText(allocator, &out, elem);
        }
    }
    return out.toOwnedSlice(allocator) catch return IonError.OutOfMemory;
}

fn maxUnknownLocalSid(elements: []const value.Element) ?u32 {
    var max_sid: u32 = 0;
    for (elements) |e| updateMaxUnknownLocalSidElem(e, &max_sid);
    return if (max_sid > symtab.SystemSymtab.max_id) max_sid else null;
}

fn updateMaxUnknownLocalSidElem(elem: value.Element, max_sid: *u32) void {
    for (elem.annotations) |a| updateMaxUnknownLocalSidSym(a, max_sid);
    updateMaxUnknownLocalSidValue(elem.value, max_sid);
}

fn updateMaxUnknownLocalSidValue(v: value.Value, max_sid: *u32) void {
    switch (v) {
        .symbol => |s| updateMaxUnknownLocalSidSym(s, max_sid),
        .list => |items| for (items) |e| updateMaxUnknownLocalSidElem(e, max_sid),
        .sexp => |items| for (items) |e| updateMaxUnknownLocalSidElem(e, max_sid),
        .@"struct" => |st| {
            for (st.fields) |f| {
                updateMaxUnknownLocalSidSym(f.name, max_sid);
                updateMaxUnknownLocalSidElem(f.value, max_sid);
            }
        },
        else => {},
    }
}

fn updateMaxUnknownLocalSidSym(s: value.Symbol, max_sid: *u32) void {
    if (s.text != null) return;
    const sid = s.sid orelse return;
    if (sid <= symtab.SystemSymtab.max_id) return;
    if (sid > max_sid.*) max_sid.* = sid;
}

const SymbolIntern = struct {
    allocator: std.mem.Allocator,
    map: std.StringHashMapUnmanaged(u32) = .{},
    fixed: FixedSymtab = .{ .slots = &.{} },
    new_symbols: std.ArrayListUnmanaged([]const u8) = .{},

    fn init(allocator: std.mem.Allocator) IonError!SymbolIntern {
        return .{ .allocator = allocator };
    }

    fn deinit(self: *SymbolIntern, allocator: std.mem.Allocator) void {
        self.map.deinit(allocator);
        if (self.fixed.slots.len != 0) allocator.free(self.fixed.slots);
        self.new_symbols.deinit(allocator);
    }

    fn sidForText(self: *SymbolIntern, allocator: std.mem.Allocator, text: []const u8) IonError!u32 {
        _ = allocator;
        if (symtab.SystemSymtab.sidForText(text)) |sid| return sid;
        if (self.map.get(text)) |sid| return sid;
        const sid: u32 = symtab.SystemSymtab.max_id + 1 + @as(u32, @intCast(self.fixed.slots.len + self.new_symbols.items.len));
        self.map.put(self.allocator, text, sid) catch return IonError.OutOfMemory;
        self.new_symbols.append(self.allocator, text) catch return IonError.OutOfMemory;
        return sid;
    }

    fn collectFromElements(self: *SymbolIntern, elements: []const value.Element) IonError!void {
        const fixed_len = try self.maxExplicitLocalSid(elements);
        if (fixed_len != 0) {
            const slots = self.allocator.alloc(?[]const u8, fixed_len) catch return IonError.OutOfMemory;
            @memset(slots, null);
            try self.fillFixedSlots(elements, slots);
            self.fixed = .{ .slots = slots };
            // Seed text->sid mapping for fixed slots with known text so we can reuse them for symbols
            // that only carry text.
            for (slots, 0..) |opt, idx| {
                if (opt) |t| {
                    const sid: u32 = symtab.SystemSymtab.max_id + 1 + @as(u32, @intCast(idx));
                    self.map.put(self.allocator, t, sid) catch return IonError.OutOfMemory;
                }
            }
        }
        for (elements) |e| try self.collectFromElement(e);
    }

    fn maxExplicitLocalSid(self: *SymbolIntern, elements: []const value.Element) IonError!usize {
        _ = self;
        var max_sid: u32 = symtab.SystemSymtab.max_id;
        for (elements) |e| try maxExplicitLocalSidElem(e, &max_sid);
        if (max_sid <= symtab.SystemSymtab.max_id) return 0;
        return @as(usize, @intCast(max_sid - symtab.SystemSymtab.max_id));
    }

    fn maxExplicitLocalSidElem(elem: value.Element, max_sid: *u32) IonError!void {
        for (elem.annotations) |a| try maxExplicitLocalSidSym(a, max_sid);
        try maxExplicitLocalSidValue(elem.value, max_sid);
    }

    fn maxExplicitLocalSidValue(v: value.Value, max_sid: *u32) IonError!void {
        switch (v) {
            .symbol => |s| try maxExplicitLocalSidSym(s, max_sid),
            .list => |items| for (items) |e| try maxExplicitLocalSidElem(e, max_sid),
            .sexp => |items| for (items) |e| try maxExplicitLocalSidElem(e, max_sid),
            .@"struct" => |st| {
                for (st.fields) |f| {
                    try maxExplicitLocalSidSym(f.name, max_sid);
                    try maxExplicitLocalSidElem(f.value, max_sid);
                }
            },
            else => {},
        }
    }

    fn maxExplicitLocalSidSym(s: value.Symbol, max_sid: *u32) IonError!void {
        if (s.sid) |sid| {
            if (sid > symtab.SystemSymtab.max_id and sid > max_sid.*) max_sid.* = sid;
        }
    }

    fn fillFixedSlots(self: *SymbolIntern, elements: []const value.Element, slots: []?[]const u8) IonError!void {
        for (elements) |e| try self.fillFixedSlotsElem(e, slots);
    }

    fn fillFixedSlotsElem(self: *SymbolIntern, elem: value.Element, slots: []?[]const u8) IonError!void {
        for (elem.annotations) |a| try self.fillFixedSlotsSym(a, slots);
        try self.fillFixedSlotsValue(elem.value, slots);
    }

    fn fillFixedSlotsValue(self: *SymbolIntern, v: value.Value, slots: []?[]const u8) IonError!void {
        switch (v) {
            .symbol => |s| try self.fillFixedSlotsSym(s, slots),
            .list => |items| for (items) |e| try self.fillFixedSlotsElem(e, slots),
            .sexp => |items| for (items) |e| try self.fillFixedSlotsElem(e, slots),
            .@"struct" => |st| {
                for (st.fields) |f| {
                    try self.fillFixedSlotsSym(f.name, slots);
                    try self.fillFixedSlotsElem(f.value, slots);
                }
            },
            else => {},
        }
    }

    fn fillFixedSlotsSym(self: *SymbolIntern, s: value.Symbol, slots: []?[]const u8) IonError!void {
        _ = self;
        const sid = s.sid orelse return;
        if (sid <= symtab.SystemSymtab.max_id) return;
        const idx: usize = @intCast(sid - (symtab.SystemSymtab.max_id + 1));
        if (idx >= slots.len) return IonError.InvalidIon;
        if (s.text) |t| {
            if (slots[idx]) |existing| {
                if (!std.mem.eql(u8, existing, t)) return IonError.InvalidIon;
            } else {
                slots[idx] = t;
            }
        }
    }

    fn collectFromElement(self: *SymbolIntern, elem: value.Element) IonError!void {
        for (elem.annotations) |a| {
            if (a.text) |t| _ = try self.sidForText(self.allocator, t);
        }
        try self.collectFromValue(elem.value);
    }

    fn collectFromValue(self: *SymbolIntern, v: value.Value) IonError!void {
        switch (v) {
            .symbol => |s| {
                if (s.text) |t| _ = try self.sidForText(self.allocator, t);
            },
            .list => |items| for (items) |e| try self.collectFromElement(e),
            .sexp => |items| for (items) |e| try self.collectFromElement(e),
            .@"struct" => |st| {
                for (st.fields) |f| {
                    if (f.name.text) |t| _ = try self.sidForText(self.allocator, t);
                    try self.collectFromElement(f.value);
                }
            },
            else => {},
        }
    }
};

fn writeLocalSymtabBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), intern: *SymbolIntern) IonError!void {
    // $ion_symbol_table::{symbols:[...]}
    var list_body = std.ArrayListUnmanaged(u8){};
    defer list_body.deinit(allocator);
    for (intern.fixed.slots) |opt| {
        if (opt) |t| {
            try writeTypedValueHeader(allocator, &list_body, 8, t.len);
            try appendSlice(&list_body, allocator, t);
        } else {
            // null.string
            try appendByte(&list_body, allocator, (8 << 4) | 0x0F);
        }
    }
    for (intern.new_symbols.items) |t| {
        try writeTypedValueHeader(allocator, &list_body, 8, t.len);
        try appendSlice(&list_body, allocator, t);
    }

    var list_value = std.ArrayListUnmanaged(u8){};
    defer list_value.deinit(allocator);
    try writeTypedValueHeader(allocator, &list_value, 11, list_body.items.len);
    try appendSlice(&list_value, allocator, list_body.items);

    var struct_body = std.ArrayListUnmanaged(u8){};
    defer struct_body.deinit(allocator);
    // field name "symbols" is system SID 7
    try writeVarUInt(allocator, &struct_body, 7);
    try appendSlice(&struct_body, allocator, list_value.items);

    var struct_value = std.ArrayListUnmanaged(u8){};
    defer struct_value.deinit(allocator);
    try writeTypedValueHeader(allocator, &struct_value, 13, struct_body.items.len);
    try appendSlice(&struct_value, allocator, struct_body.items);

    var ann_seq = std.ArrayListUnmanaged(u8){};
    defer ann_seq.deinit(allocator);
    // $ion_symbol_table is system SID 3
    try writeVarUInt(allocator, &ann_seq, 3);
    const ann_len: u64 = @intCast(ann_seq.items.len);

    var payload = std.ArrayListUnmanaged(u8){};
    defer payload.deinit(allocator);
    try writeVarUInt(allocator, &payload, ann_len);
    try appendSlice(&payload, allocator, ann_seq.items);
    try appendSlice(&payload, allocator, struct_value.items);

    try writeTypedValueHeader(allocator, out, 14, payload.items.len);
    try appendSlice(out, allocator, payload.items);
}

fn writeElementBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), intern: *SymbolIntern, elem: value.Element) IonError!void {
    if (elem.annotations.len == 0) {
        return writeValueBinary(allocator, out, intern, elem.value);
    }

    var value_buf = std.ArrayListUnmanaged(u8){};
    defer value_buf.deinit(allocator);
    try writeValueBinary(allocator, &value_buf, intern, elem.value);

    var ann_seq = std.ArrayListUnmanaged(u8){};
    defer ann_seq.deinit(allocator);
    for (elem.annotations) |a| {
        const sid: u32 = if (a.sid) |s| s else if (a.text) |t| try intern.sidForText(allocator, t) else return IonError.InvalidIon;
        try writeVarUInt(allocator, &ann_seq, sid);
    }
    const ann_len: u64 = @intCast(ann_seq.items.len);

    var payload = std.ArrayListUnmanaged(u8){};
    defer payload.deinit(allocator);
    try writeVarUInt(allocator, &payload, ann_len);
    try appendSlice(&payload, allocator, ann_seq.items);
    try appendSlice(&payload, allocator, value_buf.items);

    try writeTypedValueHeader(allocator, out, 14, payload.items.len);
    try appendSlice(out, allocator, payload.items);
}

fn writeValueBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), intern: *SymbolIntern, v: value.Value) IonError!void {
    switch (v) {
        .null => |t| return writeNullBinary(allocator, out, t),
        .bool => |b| return writeBoolBinary(allocator, out, b),
        .int => |i| return writeIntBinary(allocator, out, i),
        .float => |f| return writeFloatBinary(allocator, out, f),
        .decimal => |d| return writeDecimalBinary(allocator, out, d),
        .timestamp => |ts| return writeTimestampBinary(allocator, out, ts),
        .symbol => |s| return writeSymbolBinary(allocator, out, intern, s),
        .string => |s| return writeBytesValue(allocator, out, 8, s),
        .clob => |b| return writeBytesValue(allocator, out, 9, b),
        .blob => |b| return writeBytesValue(allocator, out, 10, b),
        .list => |items| return writeSequenceBinary(allocator, out, intern, 11, items),
        .sexp => |items| return writeSequenceBinary(allocator, out, intern, 12, items),
        .@"struct" => |st| return writeStructBinary(allocator, out, intern, st),
    }
}

fn writeNullBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), t: value.IonType) IonError!void {
    const type_id: u8 = switch (t) {
        .null => 0,
        .bool => 1,
        .int => 2,
        .float => 4,
        .decimal => 5,
        .timestamp => 6,
        .symbol => 7,
        .string => 8,
        .clob => 9,
        .blob => 10,
        .list => 11,
        .sexp => 12,
        .@"struct" => 13,
    };
    try appendByte(out, allocator, (type_id << 4) | 0x0F);
}

fn writeBoolBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), b: bool) IonError!void {
    const lc: u8 = if (b) 1 else 0;
    try appendByte(out, allocator, (@as(u8, 1) << 4) | lc);
}

fn writeIntBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), i: value.Int) IonError!void {
    const IntSign = enum { pos, neg };
    var sign: IntSign = .pos;

    switch (i) {
        .small => |v| {
            if (v == 0) {
                try appendByte(out, allocator, (2 << 4) | 0);
                return;
            }
            if (v < 0) sign = .neg;
            if (v < 0 and v == std.math.minInt(i128)) return IonError.Unsupported;
            const mag_u128: u128 = if (v < 0) @intCast(@abs(v)) else @intCast(v);
            var mag_buf: [16]u8 = undefined;
            var n: usize = 16;
            var tmp = mag_u128;
            while (tmp != 0) : (tmp >>= 8) {
                n -= 1;
                mag_buf[n] = @intCast(tmp & 0xFF);
            }
            const body = mag_buf[n..16];
            const type_id: u8 = if (sign == .neg) 3 else 2;
            try writeTypedValueHeader(allocator, out, type_id, body.len);
            try appendSlice(out, allocator, body);
        },
        .big => |bint| {
            var mag = bint.*; // copy
            if (mag.eqlZero()) {
                try appendByte(out, allocator, (2 << 4) | 0);
                return;
            }
            if (!mag.isPositive()) {
                sign = .neg;
                mag.abs();
            }
            const bits: usize = mag.toConst().bitCountAbs();
            const byte_len: usize = (bits + 7) / 8;
            const type_id: u8 = if (sign == .neg) 3 else 2;
            try writeTypedValueHeader(allocator, out, type_id, byte_len);
            const dst = try appendUninit(out, allocator, byte_len);
            @memset(dst, 0);
            // Performance: write BigInt directly into the output buffer (avoid temp alloc + copy).
            mag.toConst().writeTwosComplement(dst, .big);
        },
    }
}

fn writeFloatBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), f: f64) IonError!void {
    if (f == 0.0 and !std.math.signbit(f)) {
        try appendByte(out, allocator, (4 << 4) | 0);
        return;
    }
    var buf: [8]u8 = undefined;
    std.mem.writeInt(u64, &buf, @bitCast(f), .big);
    try writeTypedValueHeader(allocator, out, 4, 8);
    try appendSlice(out, allocator, &buf);
}

fn writeDecimalBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), d: value.Decimal) IonError!void {
    const coeff_is_zero = switch (d.coefficient) {
        .small => |v| v == 0,
        .big => |v| v.eqlZero(),
    };
    if (coeff_is_zero and d.exponent == 0 and !d.is_negative) {
        try appendByte(out, allocator, (5 << 4) | 0);
        return;
    }

    var body = std.ArrayListUnmanaged(u8){};
    defer body.deinit(allocator);

    try writeVarInt(allocator, &body, d.exponent);

    if (coeff_is_zero) {
        if (d.is_negative) {
            // negative zero as Int field
            try appendByte(&body, allocator, 0x80);
        }
    } else {
        switch (d.coefficient) {
            .small => |v| {
                if (v < 0) return IonError.InvalidIon;
                var mag_buf: [16]u8 = undefined;
                var n: usize = 16;
                var tmp: u128 = @intCast(v);
                while (tmp != 0) : (tmp >>= 8) {
                    n -= 1;
                    mag_buf[n] = @intCast(tmp & 0xFF);
                }
                var bytes = mag_buf[n..16];
                // signed-magnitude: preserve magnitude bits, encode sign in MSB of first byte
                if (d.is_negative) {
                    if ((bytes[0] & 0x80) != 0) {
                        try appendByte(&body, allocator, 0x80);
                    } else {
                        bytes[0] |= 0x80;
                    }
                } else {
                    if ((bytes[0] & 0x80) != 0) {
                        try appendByte(&body, allocator, 0x00);
                    }
                }
                try appendSlice(&body, allocator, bytes);
            },
            .big => |bint| {
                var mag = bint.*;
                mag.abs();
                const bits: usize = mag.toConst().bitCountAbs();
                const byte_len: usize = (bits + 7) / 8;
                const msb_bits: usize = if (bits == 0) 0 else ((bits - 1) % 8) + 1;

                if (d.is_negative) {
                    if (msb_bits == 8) try appendByte(&body, allocator, 0x80);
                } else {
                    if (msb_bits == 8) try appendByte(&body, allocator, 0x00);
                }

                const dst = try appendUninit(&body, allocator, byte_len);
                @memset(dst, 0);
                mag.toConst().writeTwosComplement(dst, .big);
                if (d.is_negative and msb_bits != 8) dst[0] |= 0x80;
            },
        }
    }

    try writeTypedValueHeader(allocator, out, 5, body.items.len);
    try appendSlice(out, allocator, body.items);
}

fn writeTimestampBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), ts: value.Timestamp) IonError!void {
    var body = std.ArrayListUnmanaged(u8){};
    defer body.deinit(allocator);

    if (ts.offset_minutes) |off| {
        try writeVarInt(allocator, &body, off);
    } else {
        // negative zero
        try appendByte(&body, allocator, 0xC0);
    }

    try writeVarUInt(allocator, &body, @intCast(ts.year));

    if (ts.precision == .year) {
        try writeTypedValueHeader(allocator, out, 6, body.items.len);
        try appendSlice(out, allocator, body.items);
        return;
    }
    try writeVarUInt(allocator, &body, ts.month orelse return IonError.InvalidIon);
    if (ts.precision == .month) {
        try writeTypedValueHeader(allocator, out, 6, body.items.len);
        try appendSlice(out, allocator, body.items);
        return;
    }
    try writeVarUInt(allocator, &body, ts.day orelse return IonError.InvalidIon);
    if (ts.precision == .day) {
        try writeTypedValueHeader(allocator, out, 6, body.items.len);
        try appendSlice(out, allocator, body.items);
        return;
    }
    try writeVarUInt(allocator, &body, ts.hour orelse return IonError.InvalidIon);
    try writeVarUInt(allocator, &body, ts.minute orelse return IonError.InvalidIon);
    if (ts.precision == .minute) {
        try writeTypedValueHeader(allocator, out, 6, body.items.len);
        try appendSlice(out, allocator, body.items);
        return;
    }
    try writeVarUInt(allocator, &body, ts.second orelse return IonError.InvalidIon);
    if (ts.precision == .second) {
        try writeTypedValueHeader(allocator, out, 6, body.items.len);
        try appendSlice(out, allocator, body.items);
        return;
    }
    const frac = ts.fractional orelse return IonError.InvalidIon;
    try writeVarInt(allocator, &body, frac.exponent);
    // coefficient as Int field (fixed-length signed magnitude)
    const frac_coeff_is_zero = switch (frac.coefficient) {
        .small => |v| v == 0,
        .big => |v| v.eqlZero(),
    };
    if (frac_coeff_is_zero) {
        if (frac.is_negative) {
            try appendByte(&body, allocator, 0x80);
        }
    } else {
        switch (frac.coefficient) {
            .small => |v| {
                if (v < 0) return IonError.InvalidIon;
                var mag_buf: [16]u8 = undefined;
                var n: usize = 16;
                var tmp: u128 = @intCast(v);
                while (tmp != 0) : (tmp >>= 8) {
                    n -= 1;
                    mag_buf[n] = @intCast(tmp & 0xFF);
                }
                var bytes = mag_buf[n..16];

                if (frac.is_negative) {
                    if ((bytes[0] & 0x80) != 0) {
                        try appendByte(&body, allocator, 0x80);
                    } else {
                        bytes[0] |= 0x80;
                    }
                } else {
                    // Timestamp fractional coefficient is a signed-magnitude Int field; keep sign bit clear.
                    if ((bytes[0] & 0x80) != 0) {
                        try appendByte(&body, allocator, 0x00);
                    }
                }
                try appendSlice(&body, allocator, bytes);
            },
            .big => |bint| {
                var mag = bint.*;
                mag.abs();
                const bits: usize = mag.toConst().bitCountAbs();
                const byte_len: usize = (bits + 7) / 8;
                const msb_bits: usize = if (bits == 0) 0 else ((bits - 1) % 8) + 1;

                // Decide any required prefix before writing bytes so we can write directly into `body`.
                if (frac.is_negative) {
                    if (msb_bits == 8) try appendByte(&body, allocator, 0x80);
                } else {
                    if (msb_bits == 8) try appendByte(&body, allocator, 0x00);
                }

                const dst = try appendUninit(&body, allocator, byte_len);
                @memset(dst, 0);
                mag.toConst().writeTwosComplement(dst, .big);
                if (frac.is_negative and msb_bits != 8) dst[0] |= 0x80;
            },
        }
    }
    try writeTypedValueHeader(allocator, out, 6, body.items.len);
    try appendSlice(out, allocator, body.items);
}

fn writeSymbolBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), intern: *SymbolIntern, s: value.Symbol) IonError!void {
    const sid: u32 = if (s.sid) |v| v else if (s.text) |t| try intern.sidForText(allocator, t) else 0;
    if (sid == 0) {
        try appendByte(out, allocator, (7 << 4) | 0);
        return;
    }
    var buf: [5]u8 = undefined;
    var n: usize = buf.len;
    var tmp: u32 = sid;
    while (tmp != 0) : (tmp >>= 8) {
        n -= 1;
        buf[n] = @intCast(tmp & 0xFF);
    }
    const body = buf[n..];
    try writeTypedValueHeader(allocator, out, 7, body.len);
    try appendSlice(out, allocator, body);
}

fn writeBytesValue(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), type_id: u8, bytes: []const u8) IonError!void {
    try writeTypedValueHeader(allocator, out, type_id, bytes.len);
    try appendSlice(out, allocator, bytes);
}

fn writeSequenceBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), intern: *SymbolIntern, type_id: u8, items: []const value.Element) IonError!void {
    var body = std.ArrayListUnmanaged(u8){};
    defer body.deinit(allocator);
    for (items) |e| try writeElementBinary(allocator, &body, intern, e);
    try writeTypedValueHeader(allocator, out, type_id, body.items.len);
    try appendSlice(out, allocator, body.items);
}

fn writeStructBinary(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), intern: *SymbolIntern, st: value.Struct) IonError!void {
    var body = std.ArrayListUnmanaged(u8){};
    defer body.deinit(allocator);
    for (st.fields) |f| {
        const sid: u32 = if (f.name.sid) |s| s else if (f.name.text) |t| try intern.sidForText(allocator, t) else return IonError.InvalidIon;
        try writeVarUInt(allocator, &body, sid);
        try writeElementBinary(allocator, &body, intern, f.value);
    }
    try writeTypedValueHeader(allocator, out, 13, body.items.len);
    try appendSlice(out, allocator, body.items);
}

fn writeTypedValueHeader(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), type_id: u8, body_len: usize) IonError!void {
    if (body_len <= 13) {
        try appendByte(out, allocator, (type_id << 4) | @as(u8, @intCast(body_len)));
        return;
    }
    try appendByte(out, allocator, (type_id << 4) | 14);
    try writeVarUInt(allocator, out, @intCast(body_len));
}

fn writeVarUInt(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), value_u: u64) IonError!void {
    // Big-endian base-128, end flag on last byte.
    if (value_u == 0) {
        try appendByte(out, allocator, 0x80);
        return;
    }
    var chunks: [10]u8 = undefined;
    var n: usize = 0;
    var v = value_u;
    while (v != 0) : (v >>= 7) {
        chunks[n] = @intCast(v & 0x7F);
        n += 1;
    }
    var k: usize = 0;
    while (k < n) : (k += 1) {
        var b: u8 = chunks[n - 1 - k];
        if (k == n - 1) b |= 0x80;
        try appendByte(out, allocator, b);
    }
}

fn writeVarInt(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), value_i: i64) IonError!void {
    if (value_i == 0) {
        try appendByte(out, allocator, 0x80);
        return;
    }
    const neg = value_i < 0;
    if (neg and value_i == std.math.minInt(i64)) return IonError.Unsupported;
    var mag: u64 = if (neg) @intCast(@abs(value_i)) else @intCast(value_i);

    var occupied_bits: usize = 64 - @as(usize, @intCast(@clz(mag)));
    if (occupied_bits == 0) occupied_bits = 1;
    const remaining = if (occupied_bits > 6) occupied_bits - 6 else 0;
    const bytes_required: usize = 1 + (remaining + 6) / 7;
    if (bytes_required > 10) return IonError.Unsupported;

    var buf: [10]u8 = [_]u8{0} ** 10;
    const start = buf.len - bytes_required;
    const last = buf.len - 1;

    // Fill least significant groups first, from right to left.
    var pos: usize = buf.len;
    var left: usize = bytes_required;
    while (left != 0) : (left -= 1) {
        pos -= 1;
        if (left == 1) {
            buf[pos] = @intCast(mag & 0x3F);
            if (neg) buf[pos] |= 0x40;
        } else {
            buf[pos] = @intCast(mag & 0x7F);
            mag >>= 7;
        }
    }
    buf[last] |= 0x80;
    try appendSlice(out, allocator, buf[start..]);
}

// ---- Text Writer ----

const StringStyle = enum { short, long };

fn writeElementText(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), elem: value.Element) IonError!void {
    for (elem.annotations) |a| {
        try writeSymbolText(allocator, out, a);
        try appendSlice(out, allocator, "::");
    }
    try writeValueText(allocator, out, elem.value);
}

fn writeElementTextStringStyle(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), elem: value.Element, style: StringStyle) IonError!void {
    for (elem.annotations) |a| {
        try writeSymbolText(allocator, out, a);
        try appendSlice(out, allocator, "::");
    }
    if (elem.value == .string) {
        try writeStringTextStyle(allocator, out, elem.value.string, style);
    } else {
        try writeValueText(allocator, out, elem.value);
    }
}

fn writeValueText(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), v: value.Value) IonError!void {
    switch (v) {
        .null => |t| {
            if (t == .null) {
                try appendSlice(out, allocator, "null");
            } else {
                try appendSlice(out, allocator, "null.");
                try appendSlice(out, allocator, @tagName(t));
            }
        },
        .bool => |b| try appendSlice(out, allocator, if (b) "true" else "false"),
        .int => |i| {
            switch (i) {
                .small => |v_i| {
                    var buf: [64]u8 = undefined;
                    const s = std.fmt.bufPrint(&buf, "{}", .{v_i}) catch return IonError.InvalidIon;
                    try appendSlice(out, allocator, s);
                },
                .big => |v_i| {
                    // Performance: printing BigInts in base-10 is expensive (division-heavy) and requires
                    // allocating a temporary string. Roundtrip tests only need a parseable representation,
                    // not a specific formatting, so emit a hex int literal.
                    var mag = v_i.*;
                    if (!mag.isPositive()) {
                        try appendByte(out, allocator, '-');
                        mag.abs();
                    }
                    try appendSlice(out, allocator, "0x");
                    const bits: usize = mag.toConst().bitCountAbs();
                    const byte_len: usize = (bits + 7) / 8;
                    if (byte_len == 0) {
                        try appendByte(out, allocator, '0');
                        return;
                    }
                    const bytes = allocator.alloc(u8, byte_len) catch return IonError.OutOfMemory;
                    defer allocator.free(bytes);
                    @memset(bytes, 0);
                    mag.toConst().writeTwosComplement(bytes, .big);
                    const hex = "0123456789ABCDEF";
                    for (bytes) |b| {
                        try appendByte(out, allocator, hex[b >> 4]);
                        try appendByte(out, allocator, hex[b & 0x0F]);
                    }
                },
            }
        },
        .float => |f| {
            if (std.math.isNan(f)) return appendSlice(out, allocator, "nan");
            if (std.math.isInf(f)) {
                if (f > 0) try appendSlice(out, allocator, "+inf") else try appendSlice(out, allocator, "-inf");
                return;
            }
            if (f == 0.0 and std.math.signbit(f)) {
                try appendSlice(out, allocator, "-0e0");
                return;
            }
            var buf: [128]u8 = undefined;
            const s = std.fmt.bufPrint(&buf, "{e}", .{f}) catch return IonError.InvalidIon;
            try appendSlice(out, allocator, s);
        },
        .decimal => |d| {
            if (d.is_negative) try appendByte(out, allocator, '-');
            switch (d.coefficient) {
                .small => |c| {
                    var buf: [128]u8 = undefined;
                    const coeff_s = std.fmt.bufPrint(&buf, "{}", .{c}) catch return IonError.InvalidIon;
                    try appendSlice(out, allocator, coeff_s);
                },
                .big => |c| {
                    var mag = c.*;
                    mag.abs();
                    const coeff_s = mag.toString(allocator, 10, .lower) catch return IonError.OutOfMemory;
                    defer allocator.free(coeff_s);
                    try appendSlice(out, allocator, coeff_s);
                },
            }
            try appendByte(out, allocator, 'd');
            var buf: [64]u8 = undefined;
            const exp_s = std.fmt.bufPrint(&buf, "{}", .{d.exponent}) catch return IonError.InvalidIon;
            try appendSlice(out, allocator, exp_s);
        },
        .timestamp => |ts| try writeTimestampText(allocator, out, ts),
        .symbol => |s| try writeSymbolText(allocator, out, s),
        .string => |s| try writeStringTextStyle(allocator, out, s, .short),
        .clob => |b| try writeClobText(allocator, out, b),
        .blob => |b| try writeBlobText(allocator, out, b),
        .list => |items| {
            try appendByte(out, allocator, '[');
            for (items, 0..) |e, idx| {
                if (idx != 0) try appendSlice(out, allocator, ",");
                try writeElementText(allocator, out, e);
            }
            try appendByte(out, allocator, ']');
        },
        .sexp => |items| {
            try appendByte(out, allocator, '(');
            var prev_was_string: bool = false;
            var last_string_style: StringStyle = .short;
            for (items, 0..) |e, idx| {
                if (idx != 0) try appendByte(out, allocator, ' ');
                if (e.value == .string) {
                    const style: StringStyle = if (prev_was_string) blk: {
                        break :blk switch (last_string_style) {
                            .short => .long,
                            .long => .short,
                        };
                    } else .short;
                    last_string_style = style;
                    prev_was_string = true;
                    try writeElementTextStringStyle(allocator, out, e, style);
                } else {
                    prev_was_string = false;
                    try writeElementText(allocator, out, e);
                }
            }
            try appendByte(out, allocator, ')');
        },
        .@"struct" => |st| {
            try appendByte(out, allocator, '{');
            for (st.fields, 0..) |f, idx| {
                if (idx != 0) try appendSlice(out, allocator, ",");
                try writeSymbolAsFieldNameText(allocator, out, f.name);
                try appendByte(out, allocator, ':');
                try writeElementText(allocator, out, f.value);
            }
            try appendByte(out, allocator, '}');
        },
    }
}

fn writeTimestampText(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), ts: value.Timestamp) IonError!void {
    var buf: [128]u8 = undefined;
    try appendSlice(out, allocator, std.fmt.bufPrint(&buf, "{d:0>4}", .{@as(u32, @intCast(ts.year))}) catch return IonError.InvalidIon);
    if (ts.precision == .year) {
        // Match the ion-tests corpus: year-precision timestamps include a trailing 'T'.
        try appendByte(out, allocator, 'T');
        return;
    }
    try appendByte(out, allocator, '-');
    try appendSlice(out, allocator, std.fmt.bufPrint(&buf, "{d:0>2}", .{ts.month orelse return IonError.InvalidIon}) catch return IonError.InvalidIon);
    if (ts.precision == .month) {
        // Match the ion-tests corpus: month-precision timestamps include a trailing 'T'.
        try appendByte(out, allocator, 'T');
        return;
    }
    try appendByte(out, allocator, '-');
    try appendSlice(out, allocator, std.fmt.bufPrint(&buf, "{d:0>2}", .{ts.day orelse return IonError.InvalidIon}) catch return IonError.InvalidIon);
    if (ts.precision == .day) return;
    try appendByte(out, allocator, 'T');
    try appendSlice(out, allocator, std.fmt.bufPrint(&buf, "{d:0>2}", .{ts.hour orelse return IonError.InvalidIon}) catch return IonError.InvalidIon);
    try appendByte(out, allocator, ':');
    try appendSlice(out, allocator, std.fmt.bufPrint(&buf, "{d:0>2}", .{ts.minute orelse return IonError.InvalidIon}) catch return IonError.InvalidIon);

    if (ts.precision == .second or ts.precision == .fractional) {
        try appendByte(out, allocator, ':');
        try appendSlice(out, allocator, std.fmt.bufPrint(&buf, "{d:0>2}", .{ts.second orelse return IonError.InvalidIon}) catch return IonError.InvalidIon);
        if (ts.precision == .fractional) {
            const frac = ts.fractional orelse return IonError.InvalidIon;
            const digits: usize = @intCast(-frac.exponent);
            try appendByte(out, allocator, '.');
            // Print coefficient with leading zeros to width.
            var coeff_owned: ?[]u8 = null;
            defer if (coeff_owned) |b| allocator.free(b);
            var coeff_s: []const u8 = undefined;
            switch (frac.coefficient) {
                .small => |c| {
                    var tmp: [256]u8 = undefined;
                    coeff_s = std.fmt.bufPrint(&tmp, "{}", .{c}) catch return IonError.InvalidIon;
                    if (coeff_s.len < digits) {
                        var pad: usize = digits - coeff_s.len;
                        while (pad != 0) : (pad -= 1) try appendByte(out, allocator, '0');
                    }
                    try appendSlice(out, allocator, coeff_s);
                },
                .big => |c| {
                    var mag = c.*;
                    mag.abs();
                    const s = mag.toString(allocator, 10, .lower) catch return IonError.OutOfMemory;
                    coeff_owned = s;
                    coeff_s = s;
                    if (coeff_s.len < digits) {
                        var pad: usize = digits - coeff_s.len;
                        while (pad != 0) : (pad -= 1) try appendByte(out, allocator, '0');
                    }
                    try appendSlice(out, allocator, coeff_s);
                },
            }
        }
    } else if (ts.precision != .minute) {
        return IonError.InvalidIon;
    }

    // Offset
    if (ts.offset_minutes) |off| {
        if (off == 0) {
            try appendByte(out, allocator, 'Z');
        } else {
            const sign: u8 = if (off < 0) '-' else '+';
            const abs_m: u16 = @intCast(if (off < 0) -off else off);
            const hh: u16 = @intCast(@divTrunc(abs_m, 60));
            const mm: u16 = abs_m - hh * 60;
            try appendByte(out, allocator, sign);
            try appendSlice(out, allocator, std.fmt.bufPrint(&buf, "{d:0>2}", .{hh}) catch return IonError.InvalidIon);
            try appendByte(out, allocator, ':');
            try appendSlice(out, allocator, std.fmt.bufPrint(&buf, "{d:0>2}", .{mm}) catch return IonError.InvalidIon);
        }
    } else {
        // Unknown offset: encode as -00:00
        try appendSlice(out, allocator, "-00:00");
    }
}

fn writeSymbolAsFieldNameText(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), s: value.Symbol) IonError!void {
    // Use quoted symbol for simplicity.
    try writeSymbolText(allocator, out, s);
}

fn writeSymbolText(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), s: value.Symbol) IonError!void {
    if (s.text == null) {
        const sid: u32 = s.sid orelse 0;
        var buf: [32]u8 = undefined;
        const printed = std.fmt.bufPrint(&buf, "${d}", .{sid}) catch return IonError.InvalidIon;
        try appendSlice(out, allocator, printed);
        return;
    }
    try appendByte(out, allocator, '\'');
    try writeEscapedBytes(allocator, out, s.text.?, false);
    try appendByte(out, allocator, '\'');
}

fn writeStringTextStyle(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), s: []const u8, style: StringStyle) IonError!void {
    switch (style) {
        .short => {
            try appendByte(out, allocator, '"');
            try writeEscapedBytes(allocator, out, s, false);
            try appendByte(out, allocator, '"');
        },
        .long => {
            try appendSlice(out, allocator, "'''");
            try writeEscapedBytes(allocator, out, s, false);
            try appendSlice(out, allocator, "'''");
        },
    }
}

fn writeClobText(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), b: []const u8) IonError!void {
    try appendSlice(out, allocator, "{{\"");
    try writeEscapedBytes(allocator, out, b, true);
    try appendSlice(out, allocator, "\"}}");
}

fn writeBlobText(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), b: []const u8) IonError!void {
    try appendSlice(out, allocator, "{{");
    const enc = std.base64.standard.Encoder;
    const out_len = enc.calcSize(b.len);
    const tmp = allocator.alloc(u8, out_len) catch return IonError.OutOfMemory;
    defer allocator.free(tmp);
    _ = enc.encode(tmp, b);
    try appendSlice(out, allocator, tmp);
    try appendSlice(out, allocator, "}}");
}

fn writeEscapedBytes(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), bytes: []const u8, allow_raw_bytes: bool) IonError!void {
    for (bytes) |c| {
        switch (c) {
            0x00 => try appendSlice(out, allocator, "\\0"),
            0x07 => try appendSlice(out, allocator, "\\a"),
            0x08 => try appendSlice(out, allocator, "\\b"),
            0x09 => try appendSlice(out, allocator, "\\t"),
            0x0A => try appendSlice(out, allocator, "\\n"),
            0x0C => try appendSlice(out, allocator, "\\f"),
            0x0D => try appendSlice(out, allocator, "\\r"),
            '\\' => try appendSlice(out, allocator, "\\\\"),
            '"' => try appendSlice(out, allocator, "\\\""),
            '\'' => try appendSlice(out, allocator, "\\'"),
            else => {
                const needs_hex = if (allow_raw_bytes)
                    (c < 0x20 or c == 0x7F or c >= 0x80)
                else
                    (c < 0x20 or c == 0x7F);
                if (needs_hex) {
                    var buf: [4]u8 = undefined;
                    const s = std.fmt.bufPrint(&buf, "\\x{X:0>2}", .{c}) catch return IonError.InvalidIon;
                    try appendSlice(out, allocator, s);
                } else {
                    try appendByte(out, allocator, c);
                }
            },
        }
    }
}
