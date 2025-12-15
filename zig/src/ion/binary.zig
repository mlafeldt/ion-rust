//! Ion 1.0 binary parser.
//!
//! This parser is tailored to the `ion-tests` corpus and supports:
//! - TLV decoding for Ion 1.0 binary after the IVM.
//! - Annotation wrappers (type 14), NOP padding (type 0; rejects null.nop).
//! - Containers (list/sexp/struct), including NOP padding inside containers.
//! - Numerics, decimals, timestamps, strings, symbols, clobs/blobs.
//! - Minimal local symbol table handling (`$ion_symbol_table::{symbols:[...]}`).
//! - IVM occurring within the stream (ignored if it is `E0 01 00 EA`).
//! - Ion "ordered struct" encoding variant as used by the corpus.

const std = @import("std");
const ion = @import("../ion.zig");
const value = @import("value.zig");
const symtab = @import("symtab.zig");

const IonError = ion.IonError;

const SharedSymtab = struct {
    name: []const u8,
    version: u32,
    // Index 0 corresponds to the shared table's SID 1 (shared table SIDs are 1-based).
    symbols: []const ?[]const u8,
};

/// Parses an Ion binary stream that begins with the Ion 1.0 IVM (`E0 01 00 EA`).
///
/// All returned slices are allocated in `arena` and valid until the arena is deinited.
pub fn parseTopLevel(arena: *value.Arena, bytes: []const u8) IonError![]value.Element {
    if (bytes.len < 4) return IonError.InvalidIon;
    if (!(bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x00 and bytes[3] == 0xEA)) return IonError.InvalidIon;
    var d = try Decoder.init(arena, bytes[4..]);
    return d.parseTopLevel();
}

const Decoder = struct {
    arena: *value.Arena,
    input: []const u8,
    i: usize = 0,
    st: symtab.SymbolTable,
    shared: std.StringHashMapUnmanaged(SharedSymtab) = .{},

    fn init(arena: *value.Arena, input: []const u8) IonError!Decoder {
        return .{
            .arena = arena,
            .input = input,
            .i = 0,
            .st = try symtab.SymbolTable.init(arena),
            .shared = .{},
        };
    }

    fn parseTopLevel(self: *Decoder) IonError![]value.Element {
        defer self.st.deinit();
        defer self.shared.deinit(self.arena.allocator());
        var out = std.ArrayListUnmanaged(value.Element){};
        errdefer out.deinit(self.arena.allocator());

        while (self.i < self.input.len) {
            // Ion Version Marker (IVM) may appear as a 4-byte system marker within the stream.
            // In the ion-tests corpus we only accept the Ion 1.0 IVM and ignore it.
            if (self.i + 4 <= self.input.len and std.mem.eql(u8, self.input[self.i .. self.i + 4], &.{ 0xE0, 0x01, 0x00, 0xEA })) {
                self.i += 4;
                continue;
            }

            // Skip any top-level NOP padding.
            while (self.i < self.input.len) {
                const td = try self.peekTypeDescriptor();
                if (td.type_id != 0 or td.is_null) break;
                _ = try self.readNop();
            }
            if (self.i >= self.input.len) break;

            const before = self.i;
            const elem = try self.readElement();
            if (isSystemValue(elem)) {
                try self.maybeConsumeSymbolTable(elem);
            } else {
                out.append(self.arena.allocator(), elem) catch return IonError.OutOfMemory;
            }
            if (self.i == before) return IonError.InvalidIon;
        }

        return out.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
    }

    fn readElement(self: *Decoder) IonError!value.Element {
        const td = try self.peekTypeDescriptor();
        if (td.type_id == 14) {
            return self.readAnnotationWrapper();
        }
        // No wrapper: plain value, no annotations.
        const v = try self.readValue();
        return .{ .annotations = &.{}, .value = v };
    }

    fn readAnnotationWrapper(self: *Decoder) IonError!value.Element {
        const td = try self.readTypeDescriptor();
        if (td.type_id != 14) return IonError.InvalidIon;
        if (td.is_null) return IonError.InvalidIon;
        const body_len = try self.readLength(td.length_code);
        if (self.i + body_len > self.input.len) return IonError.Incomplete;
        const body = self.input[self.i .. self.i + body_len];
        self.i += body_len;

        var cursor: usize = 0;
        const ann_len = try readVarUInt(body, &cursor);
        if (ann_len == 0) return IonError.InvalidIon;
        if (cursor + ann_len > body.len) return IonError.Incomplete;
        const ann_bytes = body[cursor .. cursor + ann_len];
        cursor += ann_len;

        var anns = std.ArrayListUnmanaged(value.Symbol){};
        errdefer anns.deinit(self.arena.allocator());
        var ann_cursor: usize = 0;
        while (ann_cursor < ann_bytes.len) {
            const sid = try readVarUInt(ann_bytes, &ann_cursor);
            const sym = try self.resolveSidToSymbol(@intCast(sid));
            anns.append(self.arena.allocator(), sym) catch return IonError.OutOfMemory;
        }
        const annotations = anns.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;

        const wrapped = body[cursor..];
        var sub = Decoder{
            .arena = self.arena,
            .input = wrapped,
            .i = 0,
            .st = self.st,
        };
        // Parse exactly one element/value from the wrapper payload.
        const inner = try sub.readElement();
        if (sub.i != sub.input.len) return IonError.InvalidIon;
        // Ion binary annotation wrappers must not be nested.
        if (inner.annotations.len != 0) return IonError.InvalidIon;
        // keep symbol table updates in sync (sub shares it by value, so nothing)

        return .{ .annotations = annotations, .value = inner.value };
    }

    fn readValue(self: *Decoder) IonError!value.Value {
        const td = try self.readTypeDescriptor();
        // Bool values encode their value in the length code and have no body bytes.
        if (!td.is_null and td.type_id == 1) {
            return try decodeBool(td.length_code);
        }
        if (td.is_null) {
            const t = typeIdToIonType(td.type_id) orelse return IonError.InvalidIon;
            return value.Value{ .null = t };
        }

        // Ion 1.0 "ordered struct" encoding uses a different meaning for length codes < 14:
        // the length code specifies the number of bytes used to encode the struct length
        // (as a VarUInt) immediately following the type descriptor.
        if (td.type_id == 13 and td.length_code < 14) {
            const short_len: usize = @intCast(td.length_code);
            if (self.i + short_len > self.input.len) return IonError.Incomplete;
            const save_i = self.i;
            const body_unordered = self.input[self.i .. self.i + short_len];
            const unordered = self.decodeStruct(body_unordered) catch |e| switch (e) {
                IonError.Incomplete => {
                    if (short_len == 0) return IonError.Incomplete;
                    // Try ordered struct interpretation: read a VarUInt length using exactly `short_len` bytes.
                    var cursor: usize = save_i;
                    const len_prefix_start = cursor;
                    const body_len_u64 = try readVarUInt(self.input, &cursor);
                    if (cursor - len_prefix_start != short_len) return IonError.InvalidIon;
                    const body_len: usize = @intCast(body_len_u64);
                    // Empty ordered structs are invalid in the ion-tests corpus; use the normal D0 encoding instead.
                    if (body_len == 0) return IonError.InvalidIon;
                    if (cursor + body_len > self.input.len) return IonError.Incomplete;
                    const body = self.input[cursor .. cursor + body_len];
                    self.i = cursor + body_len;
                    return value.Value{ .@"struct" = try self.decodeStruct(body) };
                },
                else => return e,
            };
            // Unordered short struct.
            self.i = save_i + short_len;
            return value.Value{ .@"struct" = unordered };
        }

        const body_len = try self.readLength(td.length_code);
        if (self.i + body_len > self.input.len) return IonError.Incomplete;
        const body = self.input[self.i .. self.i + body_len];
        self.i += body_len;

        return switch (td.type_id) {
            0 => return IonError.InvalidIon, // NOP should be handled outside
            1 => return IonError.InvalidIon, // handled above
            2 => try decodePosInt(self.arena, body),
            3 => try decodeNegInt(self.arena, body),
            4 => try decodeFloat(body),
            5 => try decodeDecimal(self.arena, body),
            6 => try self.decodeTimestamp(body),
            7 => try self.decodeSymbol(body),
            8 => try decodeString(body),
            9 => value.Value{ .clob = try self.arena.dupe(body) },
            10 => value.Value{ .blob = try self.arena.dupe(body) },
            11 => value.Value{ .list = try self.decodeSequence(body) },
            12 => value.Value{ .sexp = try self.decodeSequence(body) },
            13 => value.Value{ .@"struct" = try self.decodeStruct(body) },
            14 => unreachable, // wrapper handled elsewhere
            else => IonError.Unsupported,
        };
    }

    fn decodeSequence(self: *Decoder, body: []const u8) IonError![]value.Element {
        var cursor: usize = 0;
        var out = std.ArrayListUnmanaged(value.Element){};
        errdefer out.deinit(self.arena.allocator());
        while (cursor < body.len) {
            // Skip NOP pads inside container.
            while (cursor < body.len) {
                const td = parseTypeDesc(body[cursor]);
                if (td.type_id != 0 or td.is_null) break;
                cursor += try skipNop(body[cursor..]);
            }
            if (cursor >= body.len) break;

            var sub = Decoder{ .arena = self.arena, .input = body, .i = cursor, .st = self.st };
            const elem = try sub.readElement();
            cursor = sub.i;
            out.append(self.arena.allocator(), elem) catch return IonError.OutOfMemory;
        }
        return out.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
    }

    fn decodeStruct(self: *Decoder, body: []const u8) IonError!value.Struct {
        var cursor: usize = 0;
        var fields = std.ArrayListUnmanaged(value.StructField){};
        errdefer fields.deinit(self.arena.allocator());
        while (cursor < body.len) {
            const name_sid = try readVarUInt(body, &cursor);
            if (cursor >= body.len) return IonError.Incomplete;

            // NOP padding may appear in structs as a (sid, nop-pad) pair (the sid may be non-zero).
            const next_td = parseTypeDesc(body[cursor]);
            if (next_td.type_id == 0 and !next_td.is_null) {
                cursor += try skipNop(body[cursor..]);
                continue;
            }
            var sub = Decoder{ .arena = self.arena, .input = body, .i = cursor, .st = self.st };
            const elem = try sub.readElement();
            cursor = sub.i;
            const name = try self.resolveSidToSymbol(@intCast(name_sid));
            fields.append(self.arena.allocator(), .{ .name = name, .value = elem }) catch return IonError.OutOfMemory;
        }
        return .{ .fields = fields.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory };
    }

    fn decodeSymbol(self: *Decoder, body: []const u8) IonError!value.Value {
        const sid: u32 = if (body.len == 0) 0 else @intCast(readFixedUInt(body) catch return IonError.InvalidIon);
        const sym = try self.resolveSidToSymbol(sid);
        return value.Value{ .symbol = sym };
    }

    fn resolveSidToSymbol(self: *Decoder, sid: u32) IonError!value.Symbol {
        if (sid == 0) return value.unknownSymbol();
        const slot = self.st.slotForSid(sid) orelse return IonError.InvalidIon;
        if (slot) |text| return value.makeSymbolId(sid, text);
        return value.makeSymbolId(sid, null);
    }

    fn decodeTimestamp(self: *Decoder, body: []const u8) IonError!value.Value {
        var cursor: usize = 0;
        const offset = try readVarInt(body, &cursor);
        const year = try readVarUInt(body, &cursor);

        var ts: value.Timestamp = .{
            .year = @intCast(year),
            .month = null,
            .day = null,
            .hour = null,
            .minute = null,
            .second = null,
            .fractional = null,
            .offset_minutes = if (offset.is_negative_zero) null else @intCast(offset.value),
            .precision = .year,
        };
        if (ts.year == 0) return IonError.InvalidIon;

        if (cursor >= body.len) {
            ts.offset_minutes = null;
            return value.Value{ .timestamp = ts };
        }
        const month = try readVarUInt(body, &cursor);
        if (month == 0 or month > 12) return IonError.InvalidIon;
        ts.month = @intCast(month);
        ts.precision = .month;

        if (cursor >= body.len) {
            ts.offset_minutes = null;
            return value.Value{ .timestamp = ts };
        }
        const day = try readVarUInt(body, &cursor);
        if (day == 0 or day > daysInMonth(ts.year, @intCast(month))) return IonError.InvalidIon;
        ts.day = @intCast(day);
        ts.precision = .day;

        if (cursor >= body.len) {
            ts.offset_minutes = null;
            return value.Value{ .timestamp = ts };
        }
        const hour = try readVarUInt(body, &cursor);
        const minute = try readVarUInt(body, &cursor);
        if (hour > 23 or minute > 59) return IonError.InvalidIon;
        ts.hour = @intCast(hour);
        ts.minute = @intCast(minute);
        ts.precision = .minute;

        if (cursor >= body.len) return value.Value{ .timestamp = ts };
        const second = try readVarUInt(body, &cursor);
        if (second > 59) return IonError.InvalidIon;
        ts.second = @intCast(second);
        ts.precision = .second;

        if (cursor >= body.len) return value.Value{ .timestamp = ts };
        const frac_exp = try readVarInt(body, &cursor);
        const frac_bytes = body[cursor..];
        const coeff_int = try readFixedIntAny(self.arena, frac_bytes);
        const mag_is_zero = switch (coeff_int.magnitude) {
            .small => |v| v == 0,
            .big => |v| v.eqlZero(),
        };
        if (coeff_int.is_negative and !mag_is_zero) return IonError.InvalidIon;
        const mag = coeff_int.magnitude;
        // Fractional seconds must be a proper fraction: 0 <= value < 1.
        if (frac_exp.is_negative_zero) return IonError.InvalidIon;
        const exp_i32: i32 = @intCast(frac_exp.value);
        if (!mag_is_zero and exp_i32 >= 0) return IonError.InvalidIon;
        if (!mag_is_zero and exp_i32 < 0) {
            const scale: usize = @intCast(-exp_i32);
            const digits: usize = switch (mag) {
                .small => |v| blk: {
                    var digits_n: usize = 0;
                    var tmp: u128 = @intCast(v);
                    while (tmp != 0) : (tmp /= 10) digits_n += 1;
                    break :blk digits_n;
                },
                .big => |v| blk: {
                    var abs_mag = v.*;
                    abs_mag.abs();
                    const s = abs_mag.toString(self.arena.gpa, 10, .lower) catch return IonError.OutOfMemory;
                    defer self.arena.gpa.free(s);
                    break :blk s.len;
                },
            };
            if (digits > scale) return IonError.InvalidIon;
        }
        // 0d0 is equivalent to having no fractional seconds field.
        if (mag_is_zero and exp_i32 == 0) {
            ts.fractional = null;
            ts.precision = .second;
            return value.Value{ .timestamp = ts };
        }
        ts.fractional = .{ .is_negative = false, .coefficient = mag, .exponent = exp_i32 };
        ts.precision = .fractional;
        return value.Value{ .timestamp = ts };
    }

    fn maybeConsumeSymbolTable(self: *Decoder, elem: value.Element) IonError!void {
        if (elem.annotations.len != 1) return;
        const ann = elem.annotations[0].text orelse return;
        if (elem.value != .@"struct") return;

        const st_val = elem.value.@"struct";
        const allocator = self.arena.allocator();

        if (std.mem.eql(u8, ann, "$ion_shared_symbol_table")) {
            var name: ?[]const u8 = null;
            var version: ?u32 = null;
            var symbols: ?[]const ?[]const u8 = null;

            for (st_val.fields) |f| {
                const fname = f.name.text orelse continue;
                if (std.mem.eql(u8, fname, "name")) {
                    if (f.value.value != .string) return IonError.InvalidIon;
                    name = f.value.value.string;
                    continue;
                }
                if (std.mem.eql(u8, fname, "version")) {
                    if (f.value.value != .int) return IonError.InvalidIon;
                    const v_i = switch (f.value.value.int) {
                        .small => |v| v,
                        .big => return IonError.InvalidIon,
                    };
                    if (v_i <= 0 or v_i > std.math.maxInt(u32)) return IonError.InvalidIon;
                    version = @intCast(v_i);
                    continue;
                }
                if (std.mem.eql(u8, fname, "symbols")) {
                    if (f.value.value != .list) return IonError.InvalidIon;
                    const items = f.value.value.list;
                    const out = allocator.alloc(?[]const u8, items.len) catch return IonError.OutOfMemory;
                    for (items, 0..) |e, idx| {
                        out[idx] = switch (e.value) {
                            .null => null,
                            .string => |s| s,
                            else => return IonError.InvalidIon,
                        };
                    }
                    symbols = out;
                    continue;
                }
            }

            const n = name orelse return IonError.InvalidIon;
            const v = version orelse return IonError.InvalidIon;
            const syms = symbols orelse return IonError.InvalidIon;
            const key = std.fmt.allocPrint(allocator, "{s}:{d}", .{ n, v }) catch return IonError.OutOfMemory;
            self.shared.put(allocator, key, .{ .name = n, .version = v, .symbols = syms }) catch return IonError.OutOfMemory;
            return;
        }

        if (!std.mem.eql(u8, ann, "$ion_symbol_table")) return;

        // New local symbol table resets the current local symbol space (system symbols always present).
        self.st.deinit();
        self.st = try symtab.SymbolTable.init(self.arena);

        const applyImport = struct {
            fn run(d: *Decoder, import_name: []const u8, import_version: u32, import_max_id: u32) IonError!void {
                if (import_max_id == 0) return;

                const arena_alloc = d.arena.allocator();
                const key = std.fmt.allocPrint(arena_alloc, "{s}:{d}", .{ import_name, import_version }) catch return IonError.OutOfMemory;
                if (d.shared.get(key)) |shared_st| {
                    try d.st.addImport(shared_st.symbols, import_max_id);
                } else {
                    try d.st.addImport(&.{}, import_max_id);
                }
            }
        }.run;

        const parseImportStruct = struct {
            fn run(d: *Decoder, imp_st: value.Struct) IonError!struct { name: []const u8, version: u32, max_id: u32 } {
                var name: ?[]const u8 = null;
                var version: u32 = 1;
                var max_id: ?u32 = null;

                for (imp_st.fields) |ff| {
                    const nn = ff.name.text orelse continue;
                    if (std.mem.eql(u8, nn, "name")) {
                        switch (ff.value.value) {
                            .string => |s| name = s,
                            .symbol => |s| name = s.text orelse return IonError.InvalidIon,
                            else => return IonError.InvalidIon,
                        }
                        continue;
                    }
                    if (std.mem.eql(u8, nn, "version")) {
                        if (ff.value.value != .int) return IonError.InvalidIon;
                        const v_i = switch (ff.value.value.int) {
                            .small => |v| v,
                            .big => return IonError.InvalidIon,
                        };
                        if (v_i <= 0 or v_i > std.math.maxInt(u32)) return IonError.InvalidIon;
                        version = @intCast(v_i);
                        continue;
                    }
                    if (std.mem.eql(u8, nn, "max_id")) {
                        if (ff.value.value != .int) return IonError.InvalidIon;
                        const m_i = switch (ff.value.value.int) {
                            .small => |v| v,
                            .big => return IonError.InvalidIon,
                        };
                        if (m_i < 0 or m_i > std.math.maxInt(u32)) return IonError.InvalidIon;
                        max_id = @intCast(m_i);
                        continue;
                    }
                }

                const n = name orelse return IonError.InvalidIon;
                const m = max_id orelse blk: {
                    const arena_alloc = d.arena.allocator();
                    const key = std.fmt.allocPrint(arena_alloc, "{s}:{d}", .{ n, version }) catch return IonError.OutOfMemory;
                    if (d.shared.get(key)) |shared_st| break :blk @as(u32, @intCast(shared_st.symbols.len));
                    break :blk 0;
                };

                return .{ .name = n, .version = version, .max_id = m };
            }
        }.run;

        var seen_symbols = false;
        var seen_imports = false;
        for (st_val.fields) |f| {
            const fname = f.name.text orelse continue;
            if (std.mem.eql(u8, fname, "imports")) {
                if (seen_imports) return IonError.InvalidIon;
                seen_imports = true;

                switch (f.value.value) {
                    .null => {},
                    .symbol => |s| {
                        const t = s.text orelse return IonError.InvalidIon;
                        if (!std.mem.eql(u8, t, "$ion_symbol_table")) return IonError.InvalidIon;
                    },
                    .list => |imports| {
                        for (imports) |imp_elem| {
                            switch (imp_elem.value) {
                                .symbol => |s| {
                                    const t = s.text orelse return IonError.InvalidIon;
                                    if (!std.mem.eql(u8, t, "$ion_symbol_table")) return IonError.InvalidIon;
                                },
                                .@"struct" => |imp_st| {
                                    const desc = try parseImportStruct(self, imp_st);
                                    try applyImport(self, desc.name, desc.version, desc.max_id);
                                },
                                else => return IonError.InvalidIon,
                            }
                        }
                    },
                    else => return IonError.InvalidIon,
                }
                continue;
            }

            if (!std.mem.eql(u8, fname, "symbols")) continue;
            if (seen_symbols) return IonError.InvalidIon;
            seen_symbols = true;
            if (f.value.value != .list) return IonError.InvalidIon;
            for (f.value.value.list) |sym_elem| {
                if (sym_elem.value == .null) {
                    _ = try self.st.addNullSlot();
                } else if (sym_elem.value == .string) {
                    _ = try self.st.addSymbolText(sym_elem.value.string);
                } else {
                    return IonError.InvalidIon;
                }
            }
        }
    }

    fn readNop(self: *Decoder) IonError!usize {
        const td = try self.readTypeDescriptor();
        if (td.type_id != 0 or td.is_null) return IonError.InvalidIon;
        const body_len = try self.readLength(td.length_code);
        if (self.i + body_len > self.input.len) return IonError.Incomplete;
        self.i += body_len;
        return 1 + td.length_bytes + body_len;
    }

    fn peekTypeDescriptor(self: *const Decoder) IonError!TypeDesc {
        if (self.i >= self.input.len) return IonError.Incomplete;
        return parseTypeDesc(self.input[self.i]);
    }

    fn readTypeDescriptor(self: *Decoder) IonError!TypeDesc {
        const td = try self.peekTypeDescriptor();
        self.i += 1;
        return td;
    }

    fn readLength(self: *Decoder, length_code: u4) IonError!usize {
        if (length_code < 14) return @intCast(length_code);
        if (length_code == 15) return 0;
        // varUInt
        const len = try readVarUInt(self.input, &self.i);
        return @intCast(len);
    }
};

const TypeDesc = struct {
    type_id: u4,
    length_code: u4,
    is_null: bool,
    length_bytes: usize = 0,
};

fn parseTypeDesc(b: u8) TypeDesc {
    const type_id: u4 = @intCast(b >> 4);
    const lc: u4 = @intCast(b & 0x0F);
    return .{ .type_id = type_id, .length_code = lc, .is_null = lc == 15, .length_bytes = 0 };
}

fn isLeapYear(year: i32) bool {
    if (@mod(year, 4) != 0) return false;
    if (@mod(year, 100) != 0) return true;
    return @mod(year, 400) == 0;
}

fn daysInMonth(year: i32, month: u8) u8 {
    return switch (month) {
        1, 3, 5, 7, 8, 10, 12 => 31,
        4, 6, 9, 11 => 30,
        2 => if (isLeapYear(year)) 29 else 28,
        else => 0,
    };
}

fn typeIdToIonType(type_id: u4) ?value.IonType {
    return switch (type_id) {
        0 => .null,
        1 => .bool,
        2, 3 => .int,
        4 => .float,
        5 => .decimal,
        6 => .timestamp,
        7 => .symbol,
        8 => .string,
        9 => .clob,
        10 => .blob,
        11 => .list,
        12 => .sexp,
        13 => .@"struct",
        else => null,
    };
}

fn isSystemValue(elem: value.Element) bool {
    if (elem.annotations.len == 1 and elem.value == .@"struct") {
        const ann = elem.annotations[0].text orelse return false;
        return std.mem.eql(u8, ann, "$ion_symbol_table") or std.mem.eql(u8, ann, "$ion_shared_symbol_table");
    }
    return false;
}

fn decodeBool(length_code: u4) IonError!value.Value {
    return switch (length_code) {
        0 => value.Value{ .bool = false },
        1 => value.Value{ .bool = true },
        15 => value.Value{ .null = .bool },
        else => IonError.InvalidIon,
    };
}

fn decodePosInt(arena: *value.Arena, body: []const u8) IonError!value.Value {
    if (body.len == 0) return value.Value{ .int = .{ .small = 0 } };
    if (body.len <= 16) {
        const mag = readFixedUInt(body) catch return IonError.InvalidIon;
        if (mag <= @as(u128, std.math.maxInt(i128))) {
            return value.Value{ .int = .{ .small = @intCast(mag) } };
        }
        const bi = try bigIntFromMagnitudeBytes(arena, body);
        bi.setSign(true);
        return value.Value{ .int = .{ .big = bi } };
    }
    const bi = try bigIntFromMagnitudeBytes(arena, body);
    bi.setSign(true);
    return value.Value{ .int = .{ .big = bi } };
}

fn decodeNegInt(arena: *value.Arena, body: []const u8) IonError!value.Value {
    if (body.len == 0) return IonError.InvalidIon;
    if (body.len <= 16) {
        const mag = readFixedUInt(body) catch return IonError.InvalidIon;
        if (mag == 0) return IonError.InvalidIon;
        if (mag <= @as(u128, std.math.maxInt(i128))) {
            const v: i128 = @intCast(mag);
            return value.Value{ .int = .{ .small = -v } };
        }
        const bi = try bigIntFromMagnitudeBytes(arena, body);
        bi.setSign(false);
        return value.Value{ .int = .{ .big = bi } };
    }
    if (allZero(body)) return IonError.InvalidIon;
    const bi = try bigIntFromMagnitudeBytes(arena, body);
    bi.setSign(false);
    return value.Value{ .int = .{ .big = bi } };
}

fn decodeFloat(body: []const u8) IonError!value.Value {
    return switch (body.len) {
        0 => value.Value{ .float = 0.0 },
        4 => {
            const bits = std.mem.readInt(u32, @as(*const [4]u8, @ptrCast(body[0..4].ptr)), .big);
            const f32v: f32 = @bitCast(bits);
            return value.Value{ .float = @as(f64, @floatCast(f32v)) };
        },
        8 => value.Value{ .float = @bitCast(std.mem.readInt(u64, @as(*const [8]u8, @ptrCast(body[0..8].ptr)), .big)) },
        else => IonError.InvalidIon,
    };
}

fn decodeDecimal(arena: *value.Arena, body: []const u8) IonError!value.Value {
    if (body.len == 0) return value.Value{ .decimal = .{ .is_negative = false, .coefficient = .{ .small = 0 }, .exponent = 0 } };
    var cursor: usize = 0;
    const exp = try readVarInt(body, &cursor);
    const coeff_bytes = body[cursor..];
    if (coeff_bytes.len == 0) {
        return value.Value{ .decimal = .{ .is_negative = false, .coefficient = .{ .small = 0 }, .exponent = @intCast(exp.value) } };
    }

    const fixed = try readFixedIntAny(arena, coeff_bytes);
    return value.Value{ .decimal = .{
        .is_negative = fixed.is_negative,
        .coefficient = fixed.magnitude,
        .exponent = @intCast(exp.value),
    } };
}

const FixedIntAny = struct {
    is_negative: bool,
    magnitude: value.Int, // non-negative magnitude
    is_negative_zero: bool,
};

fn readFixedIntAny(arena: *value.Arena, body: []const u8) IonError!FixedIntAny {
    if (body.len == 0) return .{ .is_negative = false, .magnitude = .{ .small = 0 }, .is_negative_zero = false };
    const neg = (body[0] & 0x80) != 0;
    if (body.len <= 16) {
        var buf: [16]u8 = undefined;
        std.mem.copyForwards(u8, buf[0..body.len], body);
        buf[0] &= 0x7F;
        const mag = readFixedUInt(buf[0..body.len]) catch return IonError.InvalidIon;
        const mag_i: i128 = @intCast(mag);
        return .{
            .is_negative = neg,
            .magnitude = .{ .small = mag_i },
            .is_negative_zero = neg and mag == 0,
        };
    }

    // Big magnitude.
    var mag_bytes = try arena.allocator().dupe(u8, body);
    mag_bytes[0] &= 0x7F;
    const is_zero = allZero(mag_bytes);
    const bi = try bigIntFromMagnitudeBytes(arena, mag_bytes);
    bi.setSign(true);
    return .{
        .is_negative = neg,
        .magnitude = .{ .big = bi },
        .is_negative_zero = neg and is_zero,
    };
}

fn allZero(bytes: []const u8) bool {
    for (bytes) |b| if (b != 0) return false;
    return true;
}

fn bigIntFromMagnitudeBytes(arena: *value.Arena, magnitude_be: []const u8) IonError!*std.math.big.int.Managed {
    // Performance: avoid `bytes -> hex string -> bigInt.setString()` conversions.
    // The corpus/conformance suites exercise a lot of large integers/decimals, and string formatting
    // here quickly becomes a dominant allocation + CPU cost.
    const bi = try arena.makeBigInt();
    const bit_count: usize = magnitude_be.len * 8;
    const limb_bits: usize = @bitSizeOf(std.math.big.Limb);
    const needed_limbs: usize = if (bit_count == 0) 1 else (bit_count + limb_bits - 1) / limb_bits;
    bi.ensureCapacity(needed_limbs) catch return IonError.OutOfMemory;
    var m = bi.toMutable();
    m.readTwosComplement(magnitude_be, bit_count, .big, .unsigned);
    bi.setMetadata(true, m.len);
    return bi;
}

fn decodeString(body: []const u8) IonError!value.Value {
    if (!std.unicode.utf8ValidateSlice(body)) return IonError.InvalidIon;
    return value.Value{ .string = body };
}

fn readFixedUInt(body: []const u8) !u128 {
    if (body.len > 16) return error.Overflow;
    var v: u128 = 0;
    for (body) |b| {
        v = (v << 8) | b;
    }
    return v;
}

const FixedInt = struct {
    is_negative: bool,
    magnitude: u128,
    is_negative_zero: bool,
};

fn readFixedInt(body: []const u8) IonError!FixedInt {
    if (body.len == 0) return .{ .is_negative = false, .magnitude = 0, .is_negative_zero = false };
    if (body.len > 16) return IonError.Unsupported;
    const first = body[0];
    const neg = (first & 0x80) != 0;
    // Use a small stack buffer instead of allocations.
    var buf: [16]u8 = undefined;
    std.mem.copyForwards(u8, buf[0..body.len], body);
    buf[0] &= 0x7F;
    const mag = readFixedUInt(buf[0..body.len]) catch return IonError.InvalidIon;
    return .{ .is_negative = neg, .magnitude = mag, .is_negative_zero = neg and mag == 0 };
}

const VarIntResult = struct {
    value: i64,
    is_negative_zero: bool,
};

fn readVarUInt(bytes: []const u8, cursor: *usize) IonError!u64 {
    var v: u64 = 0;
    var saw_end = false;
    while (cursor.* < bytes.len) : (cursor.* += 1) {
        const b = bytes[cursor.*];
        const is_end = (b & 0x80) != 0;
        v = (v << 7) | @as(u64, b & 0x7F);
        if (is_end) {
            cursor.* += 1;
            saw_end = true;
            break;
        }
    }
    if (!saw_end) return IonError.Incomplete;
    return v;
}

fn readVarInt(bytes: []const u8, cursor: *usize) IonError!VarIntResult {
    if (cursor.* >= bytes.len) return IonError.Incomplete;
    const first = bytes[cursor.*];
    const sign = (first & 0x40) != 0;
    var v: u64 = first & 0x3F;
    cursor.* += 1;
    if ((first & 0x80) != 0) {
        if (v > @as(u64, std.math.maxInt(i64))) return IonError.Unsupported;
        const mag: i64 = @intCast(v);
        if (sign and mag == 0) return .{ .value = 0, .is_negative_zero = true };
        return .{ .value = if (sign) -mag else mag, .is_negative_zero = false };
    }

    while (cursor.* < bytes.len) {
        const b = bytes[cursor.*];
        const is_end = (b & 0x80) != 0;
        v = (v << 7) | @as(u64, b & 0x7F);
        cursor.* += 1;
        if (is_end) break;
    }
    if (cursor.* == 0 or (bytes[cursor.* - 1] & 0x80) == 0) return IonError.Incomplete;
    if (v > @as(u64, std.math.maxInt(i64))) return IonError.Unsupported;
    const mag: i64 = @intCast(v);
    if (sign and mag == 0) return .{ .value = 0, .is_negative_zero = true };
    return .{ .value = if (sign) -mag else mag, .is_negative_zero = false };
}

fn skipNop(slice: []const u8) IonError!usize {
    if (slice.len == 0) return IonError.Incomplete;
    const opcode = slice[0];
    if ((opcode >> 4) != 0) return IonError.InvalidIon;
    const lc: u4 = @intCast(opcode & 0x0F);
    if (lc == 15) return IonError.InvalidIon;
    var cursor: usize = 1;
    var body_len: usize = 0;
    if (lc < 14) {
        body_len = @intCast(lc);
    } else if (lc == 14) {
        body_len = @intCast(try readVarUInt(slice, &cursor));
    } else {
        body_len = 0;
    }
    if (cursor + body_len > slice.len) return IonError.Incomplete;
    return cursor + body_len;
}
