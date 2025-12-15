const std = @import("std");
const ion = @import("../ion.zig");
const value = ion.value;
const denote = @import("denote.zig");

pub const RunError = error{
    InvalidConformanceDsl,
    Unsupported,
    OutOfMemory,
};

pub const Stats = struct {
    cases: usize = 0,
    branches: usize = 0,
    passed: usize = 0,
    skipped: usize = 0,
};

const Version = enum { document, ion_1_0, ion_1_1 };

const AstEvent = union(enum) {
    value: value.Element,
    ivm: Version,
    ivm_invalid: struct { major: u32, minor: u32 },
};

const State = struct {
    version: Version,
    // Accumulated text fragments (concatenated with whitespace injection).
    text_fragments: std.ArrayListUnmanaged([]const u8) = .{},
    // Accumulated abstract AST fragments (`toplevel`) + abstract IVM markers (`ivm`).
    events: std.ArrayListUnmanaged(AstEvent) = .{},
    // If true, some clause required to evaluate this branch is not yet implemented.
    unsupported: bool = false,

    fn deinit(self: *State, allocator: std.mem.Allocator) void {
        self.text_fragments.deinit(allocator);
        self.events.deinit(allocator);
    }

    fn clone(self: *const State, allocator: std.mem.Allocator) RunError!State {
        var out = self.*;
        out.text_fragments = .{};
        out.events = .{};
        out.text_fragments.appendSlice(allocator, self.text_fragments.items) catch return RunError.OutOfMemory;
        out.events.appendSlice(allocator, self.events.items) catch return RunError.OutOfMemory;
        return out;
    }
};

fn symText(e: value.Element) ?[]const u8 {
    return switch (e.value) {
        .symbol => |s| s.text,
        else => null,
    };
}

fn isSexpHead(e: value.Element, name: []const u8) bool {
    if (e.value != .sexp) return false;
    const sx = e.value.sexp;
    if (sx.len == 0) return false;
    const t = symText(sx[0]) orelse return false;
    return std.mem.eql(u8, t, name);
}

fn getSexpItems(e: value.Element) ?[]const value.Element {
    if (e.value != .sexp) return null;
    return e.value.sexp;
}

fn sysTextForSid(version: Version, sid: u32) ?[]const u8 {
    return switch (version) {
        .ion_1_1 => ion.symtab.SystemSymtab11.textForSid(sid),
        else => ion.symtab.SystemSymtab.textForSid(sid),
    };
}

fn sysMaxId(version: Version) u32 {
    return switch (version) {
        .ion_1_1 => ion.symtab.SystemSymtab11.max_id,
        else => ion.symtab.SystemSymtab.max_id,
    };
}

fn parseDelayedSid(s: value.Symbol) ?u32 {
    const t = s.text orelse return null;
    if (!(t.len >= 3 and t[0] == '#' and t[1] == '$')) return null;
    return std.fmt.parseInt(u32, t[2..], 10) catch null;
}

fn applyTextFragment(state: *State, allocator: std.mem.Allocator, sx: []const value.Element) RunError!void {
    // (text <string?>)
    if (sx.len == 1) {
        state.text_fragments.append(allocator, "") catch return RunError.OutOfMemory;
        return;
    }
    if (sx.len != 2) return RunError.InvalidConformanceDsl;
    if (sx[1].value != .string) return RunError.InvalidConformanceDsl;
    const s = sx[1].value.string;
    if (parseTextIvmToken(s)) |v| {
        switch (v) {
            .valid => |ver| state.events.append(allocator, .{ .ivm = ver }) catch return RunError.OutOfMemory,
            .invalid => |bad| state.events.append(allocator, .{ .ivm_invalid = .{ .major = bad.major, .minor = bad.minor } }) catch return RunError.OutOfMemory,
        }
        return;
    }
    state.text_fragments.append(allocator, s) catch return RunError.OutOfMemory;
}

fn applyTopLevel2(state: *State, allocator: std.mem.Allocator, sx: []const value.Element) RunError!void {
    for (sx[1..]) |e| state.events.append(allocator, .{ .value = e }) catch return RunError.OutOfMemory;
}

fn applyBinaryFragment(state: *State, allocator: std.mem.Allocator, sx: []const value.Element) RunError!void {
    // (binary <byte>*) where <byte> is either 0..255 int or a hex string.
    if (sx.len == 1) return; // empty fragment

    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(allocator);

    for (sx[1..]) |e| {
        switch (e.value) {
            .int => |i| switch (i) {
                .small => |v| {
                    if (v < 0 or v > 255) return RunError.InvalidConformanceDsl;
                    bytes.append(allocator, @intCast(v)) catch return RunError.OutOfMemory;
                },
                else => return RunError.InvalidConformanceDsl,
            },
            .string => |s| {
                var i: usize = 0;
                while (i < s.len) {
                    while (i < s.len and std.ascii.isWhitespace(s[i])) : (i += 1) {}
                    if (i >= s.len) break;
                    if (i + 2 > s.len) return RunError.InvalidConformanceDsl;
                    const hi = std.fmt.charToDigit(s[i], 16) catch return RunError.InvalidConformanceDsl;
                    const lo = std.fmt.charToDigit(s[i + 1], 16) catch return RunError.InvalidConformanceDsl;
                    bytes.append(allocator, @intCast((hi << 4) | lo)) catch return RunError.OutOfMemory;
                    i += 2;
                }
            },
            else => return RunError.InvalidConformanceDsl,
        }
    }

    // Minimal support: recognize the 4-byte binary IVM and convert it to an abstract IVM event.
    if (bytes.items.len != 4 or bytes.items[0] != 0xE0 or bytes.items[3] != 0xEA) {
        state.unsupported = true;
        return;
    }
    const major: u32 = bytes.items[1];
    const minor: u32 = bytes.items[2];
    if (major == 1 and minor == 0) {
        state.events.append(allocator, .{ .ivm = .ion_1_0 }) catch return RunError.OutOfMemory;
        return;
    }
    if (major == 1 and minor == 1) {
        state.events.append(allocator, .{ .ivm = .ion_1_1 }) catch return RunError.OutOfMemory;
        return;
    }
    state.events.append(allocator, .{ .ivm_invalid = .{ .major = major, .minor = minor } }) catch return RunError.OutOfMemory;
}

fn buildTextDocument(allocator: std.mem.Allocator, version: Version, frags: []const []const u8) RunError![]u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    // Prefix with IVM if requested.
    switch (version) {
        .ion_1_0 => out.appendSlice(allocator, "$ion_1_0\n") catch return RunError.OutOfMemory,
        .ion_1_1 => out.appendSlice(allocator, "$ion_1_1\n") catch return RunError.OutOfMemory,
        else => {},
    }

    var first = true;
    for (frags) |f| {
        if (!first) out.append(allocator, ' ') catch return RunError.OutOfMemory;
        first = false;
        out.appendSlice(allocator, f) catch return RunError.OutOfMemory;
    }
    return out.toOwnedSlice(allocator) catch return RunError.OutOfMemory;
}

fn symtabTextForSid(symtab: []const ?[]const u8, symtab_max_id: u32, sid: u32) ?[]const u8 {
    if (sid == 0) return null;
    if (sid < symtab.len) return symtab[@intCast(sid)];
    if (sid <= symtab_max_id) return null;
    return null;
}

fn effectiveSymbolText(symtab: []const ?[]const u8, symtab_max_id: u32, s: value.Symbol) ?[]const u8 {
    if (parseDelayedSid(s)) |sid| return symtabTextForSid(symtab, symtab_max_id, sid);
    if (s.text) |t| return t;
    if (s.sid) |sid| return symtabTextForSid(symtab, symtab_max_id, sid);
    return null;
}

fn resolveDelayedSymbolUsingSymtab(arena: *value.Arena, symtab: []const ?[]const u8, symtab_max_id: u32, s: value.Symbol) RunError!value.Symbol {
    const sid = parseDelayedSid(s) orelse return s;
    if (sid == 0) return value.makeSymbolId(0, null);
    if (sid > symtab_max_id) return RunError.InvalidConformanceDsl;
    const t = symtabTextForSid(symtab, symtab_max_id, sid);
    if (t == null) return value.makeSymbolId(0, null);
    _ = arena;
    return value.makeSymbolId(null, t.?);
}

fn resolveDelayedInElement(arena: *value.Arena, symtab: []const ?[]const u8, symtab_max_id: u32, elem: value.Element) RunError!value.Element {
    var out = elem;
    if (elem.annotations.len != 0) {
        const anns = arena.allocator().dupe(value.Symbol, elem.annotations) catch return RunError.OutOfMemory;
        for (anns) |*a| a.* = try resolveDelayedSymbolUsingSymtab(arena, symtab, symtab_max_id, a.*);
        out.annotations = anns;
    }
    out.value = try resolveDelayedInValue(arena, symtab, symtab_max_id, elem.value);
    return out;
}

fn resolveDelayedInValue(arena: *value.Arena, symtab: []const ?[]const u8, symtab_max_id: u32, v: value.Value) RunError!value.Value {
    return switch (v) {
        .symbol => |s| .{ .symbol = try resolveDelayedSymbolUsingSymtab(arena, symtab, symtab_max_id, s) },
        .list => |l| blk: {
            const out = arena.allocator().alloc(value.Element, l.len) catch return RunError.OutOfMemory;
            for (l, 0..) |e, i| out[i] = try resolveDelayedInElement(arena, symtab, symtab_max_id, e);
            break :blk .{ .list = out };
        },
        .sexp => |sx| blk: {
            const out = arena.allocator().alloc(value.Element, sx.len) catch return RunError.OutOfMemory;
            for (sx, 0..) |e, i| out[i] = try resolveDelayedInElement(arena, symtab, symtab_max_id, e);
            break :blk .{ .sexp = out };
        },
        .@"struct" => |st| blk: {
            const out_fields = arena.allocator().alloc(value.StructField, st.fields.len) catch return RunError.OutOfMemory;
            for (st.fields, 0..) |f, i| {
                out_fields[i] = .{
                    .name = try resolveDelayedSymbolUsingSymtab(arena, symtab, symtab_max_id, f.name),
                    .value = try resolveDelayedInElement(arena, symtab, symtab_max_id, f.value),
                };
            }
            break :blk .{ .@"struct" = .{ .fields = out_fields } };
        },
        else => v,
    };
}

fn isIstStructTopLevel(symtab: []const ?[]const u8, symtab_max_id: u32, elem: value.Element) bool {
    if (!(elem.value == .@"struct" or (elem.value == .null and elem.value.null == .@"struct"))) return false;
    if (elem.annotations.len == 0) return false;
    const first = elem.annotations[0];
    const resolved = effectiveSymbolText(symtab, symtab_max_id, first) orelse return false;
    return std.mem.eql(u8, resolved, "$ion_symbol_table");
}

fn resetSymtabForVersion(allocator: std.mem.Allocator, version: Version, out: *std.ArrayListUnmanaged(?[]const u8), out_max_id: *u32) RunError!void {
    out.clearRetainingCapacity();
    const sys_max: u32 = sysMaxId(version);
    out.ensureTotalCapacity(allocator, sys_max + 1) catch return RunError.OutOfMemory;
    out.items.len = 0;
    out.appendAssumeCapacity(null);
    var sid: u32 = 1;
    while (sid <= sys_max) : (sid += 1) out.appendAssumeCapacity(sysTextForSid(version, sid).?);
    out_max_id.* = sys_max;
}

fn applyIstStruct(version: Version, allocator: std.mem.Allocator, symtab: *std.ArrayListUnmanaged(?[]const u8), symtab_max_id: *u32, elem: value.Element) RunError!void {
    // Only struct-valued `$ion_symbol_table` annotations are symbol tables; other types pass through.
    if (!(elem.value == .@"struct" or (elem.value == .null and elem.value.null == .@"struct"))) return;
    // Successive local symtabs replace earlier ones (reset to system + imports/symbols).
    try resetSymtabForVersion(allocator, version, symtab, symtab_max_id);

    if (elem.value == .null) return;
    const st = elem.value.@"struct";
    // Extract `symbols:[...]` if present and well-formed.
    var i: usize = 0;
    while (i < st.fields.len) : (i += 1) {
        const f = st.fields[i];
        const name_text = effectiveSymbolText(symtab.items, symtab_max_id.*, f.name) orelse continue;
        if (!std.mem.eql(u8, name_text, "symbols")) continue;
        if (f.value.value != .list) return; // malformed, ignore whole field
        const items = f.value.value.list;
        // Append slots for each entry.
        for (items) |it| {
            if (it.value == .string) {
                symtab.append(allocator, it.value.string) catch return RunError.OutOfMemory;
                symtab_max_id.* += 1;
            } else {
                // malformed entry acts like $0 => unknown slot
                symtab.append(allocator, null) catch return RunError.OutOfMemory;
                symtab_max_id.* += 1;
            }
        }
        // Expand max id and dense storage.
        if (symtab.items.len > 0) symtab_max_id.* = @intCast(symtab.items.len - 1);
        return;
    }
    // Missing or malformed symbols field => ignore.
}

fn normalizeExpectedElement(arena: *value.Arena, elem: value.Element) RunError!value.Element {
    // Currently, conformance uses `#$0` in `produces` to denote unknown symbols.
    var out = elem;
    if (elem.annotations.len != 0) {
        const anns = arena.allocator().dupe(value.Symbol, elem.annotations) catch return RunError.OutOfMemory;
        for (anns) |*a| {
            const sid = parseDelayedSid(a.*);
            if (sid != null and sid.? == 0) a.* = value.makeSymbolId(0, null);
        }
        out.annotations = anns;
    }
    out.value = try normalizeExpectedValue(arena, elem.value);
    return out;
}

fn normalizeExpectedValue(arena: *value.Arena, v: value.Value) RunError!value.Value {
    return switch (v) {
        .symbol => |s| blk: {
            const sid = parseDelayedSid(s);
            if (sid != null and sid.? == 0) break :blk .{ .symbol = value.makeSymbolId(0, null) };
            break :blk v;
        },
        .list => |l| blk: {
            const out = arena.allocator().alloc(value.Element, l.len) catch return RunError.OutOfMemory;
            for (l, 0..) |e, i| out[i] = try normalizeExpectedElement(arena, e);
            break :blk .{ .list = out };
        },
        .sexp => |sx| blk: {
            const out = arena.allocator().alloc(value.Element, sx.len) catch return RunError.OutOfMemory;
            for (sx, 0..) |e, i| out[i] = try normalizeExpectedElement(arena, e);
            break :blk .{ .sexp = out };
        },
        .@"struct" => |st| blk: {
            const out_fields = arena.allocator().alloc(value.StructField, st.fields.len) catch return RunError.OutOfMemory;
            for (st.fields, 0..) |f, i| {
                var name = f.name;
                const sid = parseDelayedSid(name);
                if (sid != null and sid.? == 0) name = value.makeSymbolId(0, null);
                out_fields[i] = .{
                    .name = name,
                    .value = try normalizeExpectedElement(arena, f.value),
                };
            }
            break :blk .{ .@"struct" = .{ .fields = out_fields } };
        },
        else => v,
    };
}

const ParsedIvm = union(enum) { valid: Version, invalid: struct { major: u32, minor: u32 } };

fn parseTextIvmToken(raw: []const u8) ?ParsedIvm {
    const s = std.mem.trim(u8, raw, " \t\r\n");
    if (!std.mem.startsWith(u8, s, "$ion_")) return null;
    const rest = s["$ion_".len..];
    const us = std.mem.indexOfScalar(u8, rest, '_') orelse return null;
    const major_s = rest[0..us];
    const minor_s = rest[us + 1 ..];
    const major = std.fmt.parseInt(u32, major_s, 10) catch return null;
    const minor = std.fmt.parseInt(u32, minor_s, 10) catch return null;
    if (major == 1 and minor == 0) return .{ .valid = .ion_1_0 };
    if (major == 1 and minor == 1) return .{ .valid = .ion_1_1 };
    return .{ .invalid = .{ .major = major, .minor = minor } };
}

fn parseAbstractIvmSymbol(s: value.Symbol) ?ParsedIvm {
    const t = s.text orelse return null;
    if (!std.mem.startsWith(u8, t, "#$ion_")) return null;
    const rest = t["#$ion_".len..];
    const us = std.mem.indexOfScalar(u8, rest, '_') orelse return null;
    const major_s = rest[0..us];
    const minor_s = rest[us + 1 ..];
    const major = std.fmt.parseInt(u32, major_s, 10) catch return null;
    const minor = std.fmt.parseInt(u32, minor_s, 10) catch return null;
    if (major == 1 and minor == 0) return .{ .valid = .ion_1_0 };
    if (major == 1 and minor == 1) return .{ .valid = .ion_1_1 };
    return .{ .invalid = .{ .major = major, .minor = minor } };
}

fn evalAbstractDocument(arena: *value.Arena, state: *State) RunError![]value.Element {
    const a = arena.allocator();
    var out = std.ArrayListUnmanaged(value.Element){};
    errdefer out.deinit(a);

    var version_ctx: Version = if (state.version == .document) .ion_1_0 else state.version;
    var symtab = std.ArrayListUnmanaged(?[]const u8){};
    defer symtab.deinit(a);
    var symtab_max_id: u32 = 0;
    try resetSymtabForVersion(a, version_ctx, &symtab, &symtab_max_id);

    for (state.events.items) |ev| {
        switch (ev) {
            .ivm => |v| {
                version_ctx = v;
                try resetSymtabForVersion(a, version_ctx, &symtab, &symtab_max_id);
            },
            .ivm_invalid => |_| return RunError.InvalidConformanceDsl,
            .value => |e| {
                if (e.annotations.len == 0 and e.value == .symbol) {
                    if (parseAbstractIvmSymbol(e.value.symbol)) |ivm| {
                        switch (ivm) {
                            .valid => |v| {
                                version_ctx = v;
                                try resetSymtabForVersion(a, version_ctx, &symtab, &symtab_max_id);
                                continue;
                            },
                            .invalid => |_| return RunError.InvalidConformanceDsl,
                        }
                    }
                }
                if (isIstStructTopLevel(symtab.items, symtab_max_id, e)) {
                    try applyIstStruct(version_ctx, a, &symtab, &symtab_max_id, e);
                    continue;
                }
                const expanded = try resolveDelayedInElement(arena, symtab.items, symtab_max_id, e);
                out.append(a, expanded) catch return RunError.OutOfMemory;
            },
        }
    }
    return out.toOwnedSlice(a) catch return RunError.OutOfMemory;
}

fn runExpectation(
    allocator: std.mem.Allocator,
    state: *State,
    exp: value.Element,
) RunError!bool {
    // Returns true if executed, false if skipped due to unsupported features.
    if (state.unsupported) return false;
    const sx = getSexpItems(exp) orelse return RunError.InvalidConformanceDsl;
    if (sx.len == 0) return RunError.InvalidConformanceDsl;
    const head = symText(sx[0]) orelse return RunError.InvalidConformanceDsl;

    var arena = value.Arena.init(allocator) catch return RunError.OutOfMemory;
    defer arena.deinit();

    var actual: []const value.Element = &.{};
    if (state.text_fragments.items.len != 0) {
        const doc_bytes = try buildTextDocument(allocator, state.version, state.text_fragments.items);
        defer allocator.free(doc_bytes);
        var doc = ion.parseDocument(allocator, doc_bytes) catch |e| {
            if (std.mem.eql(u8, head, "signals")) return true;
            std.debug.print("conformance parse failed unexpectedly: {s}\n", .{@errorName(e)});
            return RunError.InvalidConformanceDsl;
        };
        defer doc.deinit();
        actual = doc.elements;
    } else {
        const abs = evalAbstractDocument(&arena, state) catch |err| {
            if (std.mem.eql(u8, head, "signals")) return true;
            return err;
        };
        actual = abs;
    }

    if (std.mem.eql(u8, head, "signals")) {
        // If we got here, parsing succeeded, which violates the expectation.
        return RunError.InvalidConformanceDsl;
    }

    if (std.mem.eql(u8, head, "produces")) {
        const expected_raw = sx[1..];
        const expected = arena.allocator().alloc(value.Element, expected_raw.len) catch return RunError.OutOfMemory;
        for (expected_raw, 0..) |e, i| expected[i] = try normalizeExpectedElement(&arena, e);
        if (!ion.eq.ionEqElements(actual, expected)) return RunError.InvalidConformanceDsl;
        return true;
    }

    if (std.mem.eql(u8, head, "denotes")) {
        const expected_raw = sx[1..];

        // Compute denotation for actual outputs.
        var den_arena = value.Arena.init(allocator) catch return RunError.OutOfMemory;
        defer den_arena.deinit();
        const denoted = den_arena.allocator().alloc(value.Element, actual.len) catch return RunError.OutOfMemory;
        for (actual, 0..) |e, i| denoted[i] = denote.denoteElement(&den_arena, e) catch return RunError.OutOfMemory;

        // Normalize expected forms into the same representation.
        const expected = den_arena.allocator().alloc(value.Element, expected_raw.len) catch return RunError.OutOfMemory;
        for (expected_raw, 0..) |e, i| {
            expected[i] = denote.normalizeDenoteExpected(&den_arena, e) catch return RunError.Unsupported;
        }

        if (denoted.len != expected.len) {
            const a_dbg = ion.serializeDocument(allocator, .text_pretty, denoted) catch "";
            defer if (a_dbg.len != 0) allocator.free(a_dbg);
            const e_dbg = ion.serializeDocument(allocator, .text_pretty, expected) catch "";
            defer if (e_dbg.len != 0) allocator.free(e_dbg);
            if (a_dbg.len != 0 and e_dbg.len != 0) {
                std.debug.print("denotes length mismatch\nactual:\n{s}\nexpected:\n{s}\n", .{ a_dbg, e_dbg });
            }
            return RunError.InvalidConformanceDsl;
        }
        for (denoted, expected) |a, b| {
            if (!denote.denoteEq(a, b)) {
                const a_dbg = ion.serializeDocument(allocator, .text_pretty, denoted) catch "";
                defer if (a_dbg.len != 0) allocator.free(a_dbg);
                const e_dbg = ion.serializeDocument(allocator, .text_pretty, expected) catch "";
                defer if (e_dbg.len != 0) allocator.free(e_dbg);
                if (a_dbg.len != 0 and e_dbg.len != 0) {
                    std.debug.print("denotes mismatch\nactual:\n{s}\nexpected:\n{s}\n", .{ a_dbg, e_dbg });
                }
                return RunError.InvalidConformanceDsl;
            }
        }
        return true;
    }

    return RunError.Unsupported;
}

fn evalSeq(allocator: std.mem.Allocator, stats: *Stats, state: *State, items: []const value.Element) RunError!void {
    var i: usize = 0;
    while (i < items.len) : (i += 1) {
        const it = items[i];
        const sx = getSexpItems(it) orelse continue; // label/no-op
        if (sx.len == 0) return RunError.InvalidConformanceDsl;
        const head = symText(sx[0]) orelse return RunError.InvalidConformanceDsl;

        if (std.mem.eql(u8, head, "then")) {
            // (then [label...] <clauses...>)
            var child_state = try state.clone(allocator);
            defer child_state.deinit(allocator);
            try evalSeq(allocator, stats, &child_state, sx[1..]);
            continue;
        }

        if (std.mem.eql(u8, head, "each")) {
            // (each (label? fragment)* continuation)
            if (sx.len < 2) return RunError.InvalidConformanceDsl;
            var branch_frags = std.ArrayListUnmanaged(value.Element){};
            defer branch_frags.deinit(allocator);

            var idx: usize = 1;
            while (idx < sx.len) : (idx += 1) {
                if (sx[idx].value != .sexp) continue; // allow non-string "labels" as in core bootstrapping tests
                const frag_sx = sx[idx].value.sexp;
                if (frag_sx.len == 0) return RunError.InvalidConformanceDsl;
                const frag_head = symText(frag_sx[0]) orelse return RunError.InvalidConformanceDsl;
                const is_fragment = std.mem.eql(u8, frag_head, "text") or std.mem.eql(u8, frag_head, "toplevel") or std.mem.eql(u8, frag_head, "ivm") or std.mem.eql(u8, frag_head, "binary");
                if (!is_fragment) break; // start of continuation
                branch_frags.append(allocator, sx[idx]) catch return RunError.OutOfMemory;
            }
            if (idx >= sx.len) return RunError.InvalidConformanceDsl;
            const continuation = sx[idx..];

            if (branch_frags.items.len == 0) {
                // `each` with no branches acts like a single empty `toplevel` branch.
                var branch_state = try state.clone(allocator);
                defer branch_state.deinit(allocator);
                try evalSeq(allocator, stats, &branch_state, continuation);
            } else {
                for (branch_frags.items) |frag_elem| {
                    var branch_state = try state.clone(allocator);
                    defer branch_state.deinit(allocator);
                    try evalSeq(allocator, stats, &branch_state, &.{frag_elem});
                    try evalSeq(allocator, stats, &branch_state, continuation);
                }
            }
            continue;
        }

        // Fragment clauses in the current state
        if (std.mem.eql(u8, head, "text")) {
            try applyTextFragment(state, allocator, sx);
            continue;
        }
        if (std.mem.eql(u8, head, "toplevel")) {
            try applyTopLevel2(state, allocator, sx);
            continue;
        }
        if (std.mem.eql(u8, head, "binary")) {
            try applyBinaryFragment(state, allocator, sx);
            continue;
        }
        if (std.mem.eql(u8, head, "ivm")) {
            if (sx.len != 3) return RunError.InvalidConformanceDsl;
            if (sx[1].value != .int or sx[2].value != .int) return RunError.InvalidConformanceDsl;
            const major: i128 = sx[1].value.int.small;
            const minor: i128 = sx[2].value.int.small;
            if (major < 0 or minor < 0) return RunError.InvalidConformanceDsl;
            const maj_u: u32 = @intCast(major);
            const min_u: u32 = @intCast(minor);
            if (maj_u == 1 and min_u == 0) {
                state.events.append(allocator, .{ .ivm = .ion_1_0 }) catch return RunError.OutOfMemory;
            } else if (maj_u == 1 and min_u == 1) {
                state.events.append(allocator, .{ .ivm = .ion_1_1 }) catch return RunError.OutOfMemory;
            } else {
                state.events.append(allocator, .{ .ivm_invalid = .{ .major = maj_u, .minor = min_u } }) catch return RunError.OutOfMemory;
            }
            continue;
        }

        if (std.mem.eql(u8, head, "produces") or std.mem.eql(u8, head, "signals") or std.mem.eql(u8, head, "denotes")) {
            stats.branches += 1;
            const ok = runExpectation(allocator, state, it) catch |e| switch (e) {
                RunError.Unsupported => {
                    stats.skipped += 1;
                    return;
                },
                else => return e,
            };
            if (ok) stats.passed += 1 else stats.skipped += 1;
            return;
        }

        // Unimplemented clause type: mark this branch unsupported until an expectation is reached.
        state.unsupported = true;
    }
}

pub fn runConformanceFile(allocator: std.mem.Allocator, data: []const u8, stats: *Stats) RunError!void {
    // Parse conformance DSL using Ion text rules *without* adjacent string literal concatenation.
    var arena = value.Arena.init(allocator) catch return RunError.OutOfMemory;
    defer arena.deinit();
    const elements = ion.text.parseTopLevelNoStringConcat(&arena, data) catch return RunError.InvalidConformanceDsl;

    for (elements) |top| {
        if (top.value != .sexp) continue;
        const sx = top.value.sexp;
        if (sx.len == 0) continue;
        const head = symText(sx[0]) orelse continue;
        if (std.mem.eql(u8, head, "ion_1_x")) {
            stats.cases += 1;
            var state_10 = State{ .version = .ion_1_0 };
            defer state_10.deinit(allocator);
            try evalSeq(allocator, stats, &state_10, sx[1..]);

            var state_11 = State{ .version = .ion_1_1 };
            defer state_11.deinit(allocator);
            try evalSeq(allocator, stats, &state_11, sx[1..]);
            continue;
        }

        const version: Version = if (std.mem.eql(u8, head, "ion_1_0")) .ion_1_0 else if (std.mem.eql(u8, head, "ion_1_1")) .ion_1_1 else if (std.mem.eql(u8, head, "document")) .document else continue;

        stats.cases += 1;
        var state = State{ .version = version };
        defer state.deinit(allocator);
        try evalSeq(allocator, stats, &state, sx[1..]);
    }
}
