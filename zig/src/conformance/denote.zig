const std = @import("std");
const ion = @import("../ion.zig");
const value = ion.value;

pub const DenoteError = error{
    OutOfMemory,
    Unsupported,
};

fn makeSymbol(arena: *value.Arena, text: []const u8) DenoteError!value.Symbol {
    return value.makeSymbol(arena, text) catch return DenoteError.OutOfMemory;
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
    const head = makeElem(arena, .{ .symbol = try makeSymbol(arena, name) });
    return makeSexp(arena, &.{head});
}

fn makeCtor1(arena: *value.Arena, name: []const u8, arg: value.Element) DenoteError!value.Element {
    const head = makeElem(arena, .{ .symbol = try makeSymbol(arena, name) });
    return makeSexp(arena, &.{ head, arg });
}

fn makeCtor2(arena: *value.Arena, name: []const u8, a1: value.Element, a2: value.Element) DenoteError!value.Element {
    const head = makeElem(arena, .{ .symbol = try makeSymbol(arena, name) });
    return makeSexp(arena, &.{ head, a1, a2 });
}

fn makeTextBytesSexp(arena: *value.Arena, bytes: []const u8) DenoteError!value.Element {
    var elems = std.ArrayListUnmanaged(value.Element){};
    defer elems.deinit(arena.allocator());
    elems.append(arena.allocator(), makeElem(arena, .{ .symbol = try makeSymbol(arena, "text") })) catch return DenoteError.OutOfMemory;
    for (bytes) |b| {
        elems.append(arena.allocator(), makeElem(arena, .{ .int = .{ .small = @intCast(b) } })) catch return DenoteError.OutOfMemory;
    }
    return makeSexp(arena, elems.items);
}

fn denoteString(arena: *value.Arena, s: []const u8) DenoteError!value.Element {
    // Canonicalize strings as (String <utf8-bytes...>).
    const bytes = s;
    const bytes_sexp = try makeTextBytesSexp(arena, bytes);
    return makeCtor1(arena, "String", bytes_sexp);
}

fn denoteSymbol(arena: *value.Arena, sym: value.Symbol) DenoteError!value.Element {
    const t = sym.text orelse "";
    const bytes_sexp = try makeTextBytesSexp(arena, t);
    return makeCtor1(arena, "Symbol", bytes_sexp);
}

fn denoteListLike(arena: *value.Arena, ctor: []const u8, elems: []const value.Element) DenoteError!value.Element {
    var out = std.ArrayListUnmanaged(value.Element){};
    defer out.deinit(arena.allocator());
    out.append(arena.allocator(), makeElem(arena, .{ .symbol = try makeSymbol(arena, ctor) })) catch return DenoteError.OutOfMemory;
    for (elems) |e| {
        const d = try denoteElement(arena, e);
        out.append(arena.allocator(), d) catch return DenoteError.OutOfMemory;
    }
    return makeSexp(arena, out.items);
}

fn denoteStruct(arena: *value.Arena, st: value.Struct) DenoteError!value.Element {
    var out = std.ArrayListUnmanaged(value.Element){};
    defer out.deinit(arena.allocator());
    out.append(arena.allocator(), makeElem(arena, .{ .symbol = try makeSymbol(arena, "Struct") })) catch return DenoteError.OutOfMemory;

    for (st.fields) |f| {
        const name_elem: value.Element = if (f.name.text) |t| makeElem(arena, .{ .string = t }) else makeElem(arena, .{ .int = .{ .small = @intCast(f.name.sid orelse 0) } });
        const val_elem = try denoteElement(arena, f.value);
        const pair = try makeSexp(arena, &.{ name_elem, val_elem });
        out.append(arena.allocator(), pair) catch return DenoteError.OutOfMemory;
    }

    return makeSexp(arena, out.items);
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
            const type_sym = makeElem(arena, .{ .symbol = try makeSymbol(arena, @tagName(t)) });
            break :blk try makeCtor1(arena, "Null", type_sym);
        },
        .bool => |b| try makeCtor1(arena, "Bool", makeElem(arena, .{ .bool = b })),
        .int => |i| try makeCtor1(arena, "Int", makeElem(arena, .{ .int = i })),
        .float => |f| makeElem(arena, .{ .float = f }),
        .decimal => |d| makeElem(arena, .{ .decimal = d }),
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
            const type_sym = makeElem(arena, .{ .symbol = try makeSymbol(arena, @tagName(t)) });
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
