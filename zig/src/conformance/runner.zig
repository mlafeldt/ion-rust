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

const Version = enum { document, ion_1_0, ion_1_1, ion_1_x };

const State = struct {
    version: Version,
    // If non-null, input is the given AST (from `toplevel`) rather than parsing text/binary fragments.
    toplevel: ?[]const value.Element = null,
    // Accumulated text fragments (concatenated with whitespace injection).
    text_fragments: std.ArrayListUnmanaged([]const u8) = .{},
    // If true, some clause required to evaluate this branch is not yet implemented.
    unsupported: bool = false,

    fn deinit(self: *State, allocator: std.mem.Allocator) void {
        self.text_fragments.deinit(allocator);
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

fn resolveDelayedSidsInSymbol(arena: *value.Arena, version: Version, s: value.Symbol) RunError!value.Symbol {
    const t = s.text orelse return s;
    if (t.len >= 3 and t[0] == '#' and t[1] == '$') {
        const digits = t[2..];
        const sid = std.fmt.parseInt(u32, digits, 10) catch return s;
        if (sid == 0) return value.makeSymbolId(0, null);
        const max_id = sysMaxId(version);
        if (sid > max_id) return RunError.InvalidConformanceDsl;
        const sys = sysTextForSid(version, sid) orelse return RunError.InvalidConformanceDsl;
        return value.makeSymbolId(sid, sys);
    }
    _ = arena;
    return s;
}

fn resolveDelayedSidsInElement(arena: *value.Arena, version: Version, elem: value.Element) RunError!value.Element {
    var out = elem;
    // annotations
    if (elem.annotations.len != 0) {
        const anns = arena.allocator().dupe(value.Symbol, elem.annotations) catch return RunError.OutOfMemory;
        for (anns) |*a| a.* = try resolveDelayedSidsInSymbol(arena, version, a.*);
        out.annotations = anns;
    }
    out.value = try resolveDelayedSidsInValue(arena, version, elem.value);
    return out;
}

fn resolveDelayedSidsInValue(arena: *value.Arena, version: Version, v: value.Value) RunError!value.Value {
    return switch (v) {
        .symbol => |s| .{ .symbol = try resolveDelayedSidsInSymbol(arena, version, s) },
        .list => |l| blk: {
            const out = arena.allocator().alloc(value.Element, l.len) catch return RunError.OutOfMemory;
            for (l, 0..) |e, i| out[i] = try resolveDelayedSidsInElement(arena, version, e);
            break :blk .{ .list = out };
        },
        .sexp => |s| blk: {
            const out = arena.allocator().alloc(value.Element, s.len) catch return RunError.OutOfMemory;
            for (s, 0..) |e, i| out[i] = try resolveDelayedSidsInElement(arena, version, e);
            break :blk .{ .sexp = out };
        },
        .@"struct" => |st| blk: {
            const out_fields = arena.allocator().alloc(value.StructField, st.fields.len) catch return RunError.OutOfMemory;
            for (st.fields, 0..) |f, i| {
                out_fields[i] = .{
                    .name = try resolveDelayedSidsInSymbol(arena, version, f.name),
                    .value = try resolveDelayedSidsInElement(arena, version, f.value),
                };
            }
            break :blk .{ .@"struct" = .{ .fields = out_fields } };
        },
        else => v,
    };
}

fn applyTextFragment(state: *State, allocator: std.mem.Allocator, sx: []const value.Element) RunError!void {
    // (text <string?>)
    if (sx.len == 1) {
        state.text_fragments.append(allocator, "") catch return RunError.OutOfMemory;
        return;
    }
    if (sx.len != 2) return RunError.InvalidConformanceDsl;
    if (sx[1].value != .string) return RunError.InvalidConformanceDsl;
    state.text_fragments.append(allocator, sx[1].value.string) catch return RunError.OutOfMemory;
}

fn applyTopLevel(state: *State, sx: []const value.Element) RunError!void {
    state.toplevel = sx[1..];
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
    if (state.toplevel) |tl| {
        const out = arena.allocator().alloc(value.Element, tl.len) catch return RunError.OutOfMemory;
        for (tl, 0..) |e, i| out[i] = resolveDelayedSidsInElement(&arena, state.version, e) catch |err| {
            if (std.mem.eql(u8, head, "signals")) return true;
            return err;
        };
        actual = out;
    } else if (state.text_fragments.items.len != 0) {
        const doc_bytes = try buildTextDocument(allocator, state.version, state.text_fragments.items);
        defer allocator.free(doc_bytes);
        var doc = ion.parseDocument(allocator, doc_bytes) catch |e| {
            if (std.mem.eql(u8, head, "signals")) return true;
            std.debug.print("conformance parse failed unexpectedly: {s}\n", .{@errorName(e)});
            return RunError.InvalidConformanceDsl;
        };
        defer doc.deinit();
        actual = doc.elements;
        // Copy into arena so we can safely resolve delayed SIDs and reuse for denotation.
        const out = arena.allocator().alloc(value.Element, actual.len) catch return RunError.OutOfMemory;
        for (actual, 0..) |e, i| out[i] = resolveDelayedSidsInElement(&arena, state.version, e) catch |err| {
            if (std.mem.eql(u8, head, "signals")) return true;
            return err;
        };
        actual = out;
    } else {
        actual = &.{};
    }

    if (std.mem.eql(u8, head, "signals")) {
        // If we got here, parsing succeeded, which violates the expectation.
        return RunError.InvalidConformanceDsl;
    }

    if (std.mem.eql(u8, head, "produces")) {
        const expected_raw = sx[1..];
        const expected = arena.allocator().alloc(value.Element, expected_raw.len) catch return RunError.OutOfMemory;
        for (expected_raw, 0..) |e, i| expected[i] = try resolveDelayedSidsInElement(&arena, state.version, e);
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
            var child_state = state.*;
            defer child_state.deinit(allocator);
            // Copy fragments list shallowly.
            child_state.text_fragments = .{};
            child_state.text_fragments.appendSlice(allocator, state.text_fragments.items) catch return RunError.OutOfMemory;
            try evalSeq(allocator, stats, &child_state, sx[1..]);
            continue;
        }

        if (std.mem.eql(u8, head, "each")) {
            // Pattern supported: (each [labels...] (<fragment> ...)* (<expectation ...>))
            if (sx.len < 2) return RunError.InvalidConformanceDsl;

            // Find the last sexp child and treat it as the expectation clause.
            var exp_idx_opt: ?usize = null;
            var j: usize = 1;
            while (j < sx.len) : (j += 1) {
                if (sx[j].value == .sexp) exp_idx_opt = j;
            }
            const exp_idx = exp_idx_opt orelse return RunError.InvalidConformanceDsl;
            const exp = sx[exp_idx];

            var k: usize = 1;
            while (k < exp_idx) : (k += 1) {
                if (sx[k].value != .sexp) continue; // label
                const frag_sx = sx[k].value.sexp;
                if (frag_sx.len == 0) return RunError.InvalidConformanceDsl;
                const frag_head = symText(frag_sx[0]) orelse return RunError.InvalidConformanceDsl;
                if (!(std.mem.eql(u8, frag_head, "text") or std.mem.eql(u8, frag_head, "toplevel"))) {
                    // Defer other fragment types for now.
                    continue;
                }

                var branch_state = state.*;
                defer branch_state.deinit(allocator);
                branch_state.text_fragments = .{};
                branch_state.text_fragments.appendSlice(allocator, state.text_fragments.items) catch return RunError.OutOfMemory;

                if (std.mem.eql(u8, frag_head, "text")) {
                    try applyTextFragment(&branch_state, allocator, frag_sx);
                } else if (std.mem.eql(u8, frag_head, "toplevel")) {
                    try applyTopLevel(&branch_state, frag_sx);
                }

                stats.branches += 1;
                const ok = runExpectation(allocator, &branch_state, exp) catch |e| switch (e) {
                    RunError.Unsupported => {
                        stats.skipped += 1;
                        continue;
                    },
                    else => return e,
                };
                if (ok) stats.passed += 1 else stats.skipped += 1;
            }
            continue;
        }

        // Fragment clauses in the current state
        if (std.mem.eql(u8, head, "text")) {
            try applyTextFragment(state, allocator, sx);
            continue;
        }
        if (std.mem.eql(u8, head, "toplevel")) {
            try applyTopLevel(state, sx);
            continue;
        }

        if (std.mem.eql(u8, head, "produces") or std.mem.eql(u8, head, "signals") or std.mem.eql(u8, head, "denotes")) {
            stats.branches += 1;
            const ok = runExpectation(allocator, state, it) catch |e| switch (e) {
                RunError.Unsupported => {
                    stats.skipped += 1;
                    continue;
                },
                else => return e,
            };
            if (ok) stats.passed += 1 else stats.skipped += 1;
            continue;
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

        const version: Version = if (std.mem.eql(u8, head, "ion_1_0")) .ion_1_0 else if (std.mem.eql(u8, head, "ion_1_1")) .ion_1_1 else if (std.mem.eql(u8, head, "ion_1_x")) .ion_1_x else if (std.mem.eql(u8, head, "document")) .document else continue;

        stats.cases += 1;
        var state = State{ .version = version };
        defer state.deinit(allocator);
        try evalSeq(allocator, stats, &state, sx[1..]);
    }
}
