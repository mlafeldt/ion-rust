const std = @import("std");
const ion = @import("../ion.zig");
const value = ion.value;

pub const DenoteError = error{
    OutOfMemory,
    Unsupported,
};

fn makeSymbol(arena: *value.Arena, text: []const u8) value.Symbol {
    // Denotation constructor names are compile-time strings; avoid arena duplication to keep
    // denotation evaluation cheap and reduce allocator churn during the conformance suite.
    _ = arena;
    return .{ .sid = null, .text = text };
}

fn makeElem(arena: *value.Arena, v: value.Value) value.Element {
    _ = arena;
    return .{ .annotations = &.{}, .value = v };
}

fn makeSexp(arena: *value.Arena, items: []const value.Element) DenoteError!value.Element {
    const owned = arena.allocator().dupe(value.Element, items) catch return DenoteError.OutOfMemory;
    return makeElem(arena, .{ .sexp = owned });
}

fn makeCtor0(arena: *value.Arena, name: []const u8) DenoteError!value.Element {
    const head = makeElem(arena, .{ .symbol = makeSymbol(arena, name) });
    return makeSexp(arena, &.{head});
}

fn makeCtor1(arena: *value.Arena, name: []const u8, arg: value.Element) DenoteError!value.Element {
    const head = makeElem(arena, .{ .symbol = makeSymbol(arena, name) });
    return makeSexp(arena, &.{ head, arg });
}

fn makeCtor2(arena: *value.Arena, name: []const u8, a1: value.Element, a2: value.Element) DenoteError!value.Element {
    const head = makeElem(arena, .{ .symbol = makeSymbol(arena, name) });
    return makeSexp(arena, &.{ head, a1, a2 });
}

fn makeTextBytesSexp(arena: *value.Arena, bytes: []const u8) DenoteError!value.Element {
    // Avoid `ArrayList`/`realloc` churn: conformance uses this encoding heavily.
    const items = arena.allocator().alloc(value.Element, bytes.len + 1) catch return DenoteError.OutOfMemory;
    items[0] = makeElem(arena, .{ .symbol = makeSymbol(arena, "text") });
    for (bytes, 0..) |b, i| {
        items[i + 1] = makeElem(arena, .{ .int = .{ .small = @intCast(b) } });
    }
    return makeElem(arena, .{ .sexp = items });
}

fn denoteString(arena: *value.Arena, s: []const u8) DenoteError!value.Element {
    // Canonicalize strings as (String <utf8-bytes...>).
    const bytes = s;
    const bytes_sexp = try makeTextBytesSexp(arena, bytes);
    return makeCtor1(arena, "String", bytes_sexp);
}

fn denoteSymbol(arena: *value.Arena, sym: value.Symbol) DenoteError!value.Element {
    if (sym.text) |t| {
        const bytes_sexp = try makeTextBytesSexp(arena, t);
        return makeCtor1(arena, "Symbol", bytes_sexp);
    }
    if (sym.sid) |sid| {
        const sid_elem = makeElem(arena, .{ .int = .{ .small = @intCast(sid) } });
        return makeCtor1(arena, "Symbol", sid_elem);
    }
    const bytes_sexp = try makeTextBytesSexp(arena, "");
    return makeCtor1(arena, "Symbol", bytes_sexp);
}

fn denoteListLike(arena: *value.Arena, ctor: []const u8, elems: []const value.Element) DenoteError!value.Element {
    const items = arena.allocator().alloc(value.Element, elems.len + 1) catch return DenoteError.OutOfMemory;
    items[0] = makeElem(arena, .{ .symbol = makeSymbol(arena, ctor) });
    for (elems, 0..) |e, i| items[i + 1] = try denoteElement(arena, e);
    return makeElem(arena, .{ .sexp = items });
}

fn denoteStruct(arena: *value.Arena, st: value.Struct) DenoteError!value.Element {
    const items = arena.allocator().alloc(value.Element, st.fields.len + 1) catch return DenoteError.OutOfMemory;
    items[0] = makeElem(arena, .{ .symbol = makeSymbol(arena, "Struct") });

    for (st.fields, 0..) |f, i| {
        // Conformance denotes struct field names as either:
        // - an integer (SID) if a field name was addressed by ID, or
        // - a string literal if the field name is textual.
        //
        // Prefer a known SID when present, since binary Ion often resolves system symbols to both
        // `sid` and `text`, but the denotation language expects the SID form.
        const name_elem: value.Element = if (f.name.sid) |sid|
            makeElem(arena, .{ .int = .{ .small = @intCast(sid) } })
        else if (f.name.text) |t|
            makeElem(arena, .{ .string = t })
        else
            makeElem(arena, .{ .int = .{ .small = 0 } });
        const val_elem = try denoteElement(arena, f.value);
        const pair_items = arena.allocator().alloc(value.Element, 2) catch return DenoteError.OutOfMemory;
        pair_items[0] = name_elem;
        pair_items[1] = val_elem;
        items[i + 1] = makeElem(arena, .{ .sexp = pair_items });
    }

    return makeElem(arena, .{ .sexp = items });
}

fn denoteFloat(arena: *value.Arena, f: f64) DenoteError!value.Element {
    // Conformance denotes floats via a canonical Ion text representation string.
    //
    // Zig's `{e}` formatting matches the conformance suite's expected encodings for finite values
    // (e.g. `0e0`, `6.125e0`, `1.401298464324817e-45`, `5e-324`).
    var buf: [128]u8 = undefined;
    const s: []const u8 = if (std.math.isNan(f))
        "nan"
    else if (std.math.isInf(f))
        (if (f > 0) "+inf" else "-inf")
    else if (f == 0.0 and std.math.signbit(f))
        "-0e0"
    else if (f == 0.0)
        "0e0"
    else
        (std.fmt.bufPrint(&buf, "{e}", .{f}) catch return DenoteError.Unsupported);

    return makeCtor1(arena, "Float", try denoteString(arena, s));
}

fn denoteDecimal(arena: *value.Arena, d: value.Decimal) DenoteError!value.Element {
    // Conformance denotes decimals as (Decimal <coefficient> <exponent>) where:
    // - coefficient is an integer, except negative zero which is represented as the string "negative_0"
    // - exponent is an integer
    const coeff_is_zero = switch (d.coefficient) {
        .small => |v| v == 0,
        .big => |v| v.eqlZero(),
    };

    const coeff_elem: value.Element = if (coeff_is_zero and d.is_negative) blk: {
        break :blk try denoteString(arena, "negative_0");
    } else blk: {
        const coeff_int: value.Int = switch (d.coefficient) {
            .small => |v| .{ .small = if (d.is_negative) -v else v },
            .big => |b| if (!d.is_negative) .{ .big = b } else blk2: {
                const copy = arena.makeBigInt() catch return DenoteError.OutOfMemory;
                copy.copy(b.toConst()) catch return DenoteError.OutOfMemory;
                copy.setSign(false);
                break :blk2 .{ .big = copy };
            },
        };
        break :blk try makeCtor1(arena, "Int", makeElem(arena, .{ .int = coeff_int }));
    };

    const exp_elem = try makeCtor1(arena, "Int", makeElem(arena, .{ .int = .{ .small = @intCast(d.exponent) } }));
    return makeCtor2(arena, "Decimal", coeff_elem, exp_elem);
}

pub fn denoteElement(arena: *value.Arena, elem: value.Element) DenoteError!value.Element {
    if (elem.annotations.len != 0) {
        // For now, ignore annotations in denotation output (conformance tests that need them are elsewhere).
        // This mirrors the "application value" focus of the early conformance tiers.
        _ = elem.annotations;
    }
    return switch (elem.value) {
        .null => |t| blk: {
            if (t == .null) break :blk try makeCtor0(arena, "Null");
            const type_sym = makeElem(arena, .{ .symbol = makeSymbol(arena, @tagName(t)) });
            break :blk try makeCtor1(arena, "Null", type_sym);
        },
        .bool => |b| try makeCtor1(arena, "Bool", makeElem(arena, .{ .bool = b })),
        .int => |i| try makeCtor1(arena, "Int", makeElem(arena, .{ .int = i })),
        .float => |f| try denoteFloat(arena, f),
        .decimal => |d| try denoteDecimal(arena, d),
        .timestamp => |t| makeElem(arena, .{ .timestamp = t }),
        .string => |s| try denoteString(arena, s),
        .symbol => |s| try denoteSymbol(arena, s),
        .blob => |b| makeElem(arena, .{ .blob = b }),
        .clob => |c| makeElem(arena, .{ .clob = c }),
        .list => |l| try denoteListLike(arena, "List", l),
        .sexp => |s| try denoteListLike(arena, "Sexp", s),
        .@"struct" => |st| try denoteStruct(arena, st),
    };
}

fn isCtor(sexp: []const value.Element, name: []const u8) bool {
    if (sexp.len == 0) return false;
    if (sexp[0].value != .symbol) return false;
    const t = sexp[0].value.symbol.text orelse return false;
    return std.mem.eql(u8, t, name);
}

fn decodeSmallByte(e: value.Element) ?u8 {
    if (e.value != .int) return null;
    return switch (e.value.int) {
        .small => |v| if (v >= 0 and v <= 255) @intCast(v) else null,
        .big => null,
    };
}

pub fn evalTextConstructorToString(allocator: std.mem.Allocator, elem: value.Element) DenoteError![]const u8 {
    // Accept:
    // - (text <byte>...)
    // - (String <byte>...)
    // - raw string literal (returned as an owned copy)
    if (elem.value == .string) {
        return allocator.dupe(u8, elem.value.string) catch return DenoteError.OutOfMemory;
    }
    if (elem.value != .sexp) return DenoteError.Unsupported;
    const sx = elem.value.sexp;
    if (isCtor(sx, "text")) {
        var buf = std.ArrayListUnmanaged(u8){};
        defer buf.deinit(allocator);
        for (sx[1..]) |it| {
            const b = decodeSmallByte(it) orelse return DenoteError.Unsupported;
            buf.append(allocator, b) catch return DenoteError.OutOfMemory;
        }
        return buf.toOwnedSlice(allocator) catch return DenoteError.OutOfMemory;
    }
    if (isCtor(sx, "String")) {
        // Shorthand used in some tests: (String) for empty or (String <bytes...>).
        var buf = std.ArrayListUnmanaged(u8){};
        defer buf.deinit(allocator);
        for (sx[1..]) |it| {
            const b = decodeSmallByte(it) orelse return DenoteError.Unsupported;
            buf.append(allocator, b) catch return DenoteError.OutOfMemory;
        }
        return buf.toOwnedSlice(allocator) catch return DenoteError.OutOfMemory;
    }
    return DenoteError.Unsupported;
}

pub fn normalizeDenoteExpected(arena: *value.Arena, expected: value.Element) DenoteError!value.Element {
    // Turns shorthand forms in expected-denotes into the canonical representation produced by `denoteElement`.
    return switch (expected.value) {
        .string => |s| try denoteString(arena, s),
        .bool => |b| try makeCtor1(arena, "Bool", makeElem(arena, .{ .bool = b })),
        .int => |i| try makeCtor1(arena, "Int", makeElem(arena, .{ .int = i })),
        .null => |t| blk: {
            if (t == .null) break :blk try makeCtor0(arena, "Null");
            const type_sym = makeElem(arena, .{ .symbol = makeSymbol(arena, @tagName(t)) });
            break :blk try makeCtor1(arena, "Null", type_sym);
        },
        .float, .decimal, .timestamp, .blob, .clob => expected,
        .symbol => expected,
        .list => |l| blk: {
            var out = std.ArrayListUnmanaged(value.Element){};
            defer out.deinit(arena.allocator());
            for (l) |e| out.append(arena.allocator(), try normalizeDenoteExpected(arena, e)) catch return DenoteError.OutOfMemory;
            break :blk makeElem(arena, .{ .list = out.toOwnedSlice(arena.allocator()) catch return DenoteError.OutOfMemory });
        },
        .sexp => |sx| blk: {
            // (Symbol "foo") and (Symbol (text ...))
            if (isCtor(sx, "Symbol")) {
                if (sx.len != 2) return DenoteError.Unsupported;
                if (sx[1].value == .int) return makeCtor1(arena, "Symbol", sx[1]);
                if (sx[1].value == .sexp and isCtor(sx[1].value.sexp, "absent")) {
                    // Keep `absent` symtok as-is: (Symbol (absent <name> <offset>)).
                    return makeCtor1(arena, "Symbol", sx[1]);
                }
                const str = try evalTextConstructorToString(arena.gpa, sx[1]);
                defer arena.gpa.free(str);
                const bytes_sexp = try makeTextBytesSexp(arena, str);
                return makeCtor1(arena, "Symbol", bytes_sexp);
            }
            // (String ...) shorthand
            if (isCtor(sx, "String")) {
                var bytes = std.ArrayListUnmanaged(u8){};
                defer bytes.deinit(arena.gpa);
                for (sx[1..]) |it| {
                    const b = decodeSmallByte(it) orelse return DenoteError.Unsupported;
                    bytes.append(arena.gpa, b) catch return DenoteError.OutOfMemory;
                }
                const bytes_sexp = try makeTextBytesSexp(arena, bytes.items);
                return makeCtor1(arena, "String", bytes_sexp);
            }
            // (Struct (<field> <value>) ...)
            if (isCtor(sx, "Struct")) {
                var out = std.ArrayListUnmanaged(value.Element){};
                defer out.deinit(arena.allocator());
                out.append(arena.allocator(), sx[0]) catch return DenoteError.OutOfMemory;
                for (sx[1..]) |pair| {
                    if (pair.value != .sexp) return DenoteError.Unsupported;
                    const p = pair.value.sexp;
                    if (p.len != 2) return DenoteError.Unsupported;

                    // Field names are strings or SIDs, not denoted values.
                    const name_elem: value.Element = switch (p[0].value) {
                        .int => p[0],
                        .string => p[0],
                        .sexp => blk2: {
                            const name_str = evalTextConstructorToString(arena.gpa, p[0]) catch return DenoteError.Unsupported;
                            defer arena.gpa.free(name_str);
                            const owned = arena.allocator().dupe(u8, name_str) catch return DenoteError.OutOfMemory;
                            break :blk2 makeElem(arena, .{ .string = owned });
                        },
                        else => return DenoteError.Unsupported,
                    };

                    const val_elem = try normalizeDenoteExpected(arena, p[1]);
                    const new_pair = try makeSexp(arena, &.{ name_elem, val_elem });
                    out.append(arena.allocator(), new_pair) catch return DenoteError.OutOfMemory;
                }
                break :blk makeElem(arena, .{ .sexp = out.toOwnedSlice(arena.allocator()) catch return DenoteError.OutOfMemory });
            }

            if (isCtor(sx, "Bool")) {
                if (sx.len != 2) return DenoteError.Unsupported;
                if (sx[1].value != .bool) return DenoteError.Unsupported;
                return makeCtor1(arena, "Bool", sx[1]);
            }
            if (isCtor(sx, "Int")) {
                if (sx.len != 2) return DenoteError.Unsupported;
                if (sx[1].value != .int) return DenoteError.Unsupported;
                return makeCtor1(arena, "Int", sx[1]);
            }
            if (isCtor(sx, "Null")) {
                if (sx.len == 1) return makeCtor0(arena, "Null");
                if (sx.len != 2) return DenoteError.Unsupported;
                if (sx[1].value != .symbol) return DenoteError.Unsupported;
                return makeCtor1(arena, "Null", sx[1]);
            }

            var out = std.ArrayListUnmanaged(value.Element){};
            defer out.deinit(arena.allocator());
            for (sx) |e| out.append(arena.allocator(), try normalizeDenoteExpected(arena, e)) catch return DenoteError.OutOfMemory;
            break :blk makeElem(arena, .{ .sexp = out.toOwnedSlice(arena.allocator()) catch return DenoteError.OutOfMemory });
        },
        .@"struct" => |st| blk: {
            // Struct in expected denotes should only appear as part of inputs, not as denotes representation.
            var fields = std.ArrayListUnmanaged(value.StructField){};
            defer fields.deinit(arena.allocator());
            for (st.fields) |f| {
                fields.append(arena.allocator(), .{ .name = f.name, .value = try normalizeDenoteExpected(arena, f.value) }) catch return DenoteError.OutOfMemory;
            }
            break :blk makeElem(arena, .{ .@"struct" = .{ .fields = fields.toOwnedSlice(arena.allocator()) catch return DenoteError.OutOfMemory } });
        },
    };
}

pub fn denoteEq(a: value.Element, b: value.Element) bool {
    // Structural equality for the denotation representation.
    // Special case: (Struct ...) is order-insensitive.
    if (a.value == .sexp and b.value == .sexp) {
        const ax = a.value.sexp;
        const bx = b.value.sexp;
        if (isCtor(ax, "Struct") and isCtor(bx, "Struct")) {
            if (ax.len != bx.len) return false;
            var used = std.mem.zeroes([256]bool); // conformance core won't exceed this; fallback below if needed
            if (bx.len > used.len) return denoteEqSlowMultiset(ax[1..], bx[1..]);
            for (ax[1..]) |ae| {
                var found = false;
                for (bx[1..], 0..) |be, idx| {
                    if (used[idx]) continue;
                    if (denoteEq(ae, be)) {
                        used[idx] = true;
                        found = true;
                        break;
                    }
                }
                if (!found) return false;
            }
            return true;
        }
    }

    return switch (a.value) {
        .null => b.value == .null and a.value.null == b.value.null,
        .bool => b.value == .bool and a.value.bool == b.value.bool,
        .int => b.value == .int and ion.eq.ionEqInt(a.value.int, b.value.int),
        .float => b.value == .float and a.value.float == b.value.float,
        .decimal => b.value == .decimal and ion.eq.ionEqDecimal(a.value.decimal, b.value.decimal),
        .timestamp => b.value == .timestamp and ion.eq.ionEqTimestamp(a.value.timestamp, b.value.timestamp),
        .string => b.value == .string and std.mem.eql(u8, a.value.string, b.value.string),
        .symbol => b.value == .symbol and ion.eq.ionEqSymbol(a.value.symbol, b.value.symbol),
        .blob => b.value == .blob and std.mem.eql(u8, a.value.blob, b.value.blob),
        .clob => b.value == .clob and std.mem.eql(u8, a.value.clob, b.value.clob),
        .list => |al| blk: {
            if (b.value != .list) break :blk false;
            const bl = b.value.list;
            if (al.len != bl.len) break :blk false;
            for (al, bl) |ae, be| if (!denoteEq(ae, be)) break :blk false;
            break :blk true;
        },
        .sexp => |asx| blk: {
            if (b.value != .sexp) break :blk false;
            const bsx = b.value.sexp;
            if (asx.len != bsx.len) break :blk false;
            for (asx, bsx) |ae, be| if (!denoteEq(ae, be)) break :blk false;
            break :blk true;
        },
        .@"struct" => |ast| blk: {
            if (b.value != .@"struct") break :blk false;
            // Not used by our denotation output; fall back to Ion equality.
            break :blk ion.eq.ionEqStruct(ast, b.value.@"struct");
        },
    };
}

fn denoteEqSlowMultiset(a_fields: []const value.Element, b_fields: []const value.Element) bool {
    if (a_fields.len != b_fields.len) return false;
    var used = std.heap.page_allocator.alloc(bool, b_fields.len) catch return false;
    defer std.heap.page_allocator.free(used);
    @memset(used, false);
    for (a_fields) |ae| {
        var found = false;
        for (b_fields, 0..) |be, idx| {
            if (used[idx]) continue;
            if (denoteEq(ae, be)) {
                used[idx] = true;
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}
