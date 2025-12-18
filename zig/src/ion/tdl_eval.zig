//! Minimal TDL/template evaluator used to expand conformance macro tables.
//!
//! This is intentionally incomplete and only implements the subset required by
//! `ion-tests/conformance/tdl/*`.
//!
//! Errors:
//! - Return `IonError.Unsupported` for not-yet-implemented surface area (counted as conformance skips).
//! - Return `IonError.InvalidIon` for malformed template bodies / runtime evaluation errors.

const std = @import("std");
const ion = @import("../ion.zig");
const value = @import("value.zig");

const IonError = ion.IonError;

fn headTokenText(e: value.Element) ?[]const u8 {
    return switch (e.value) {
        .symbol => |s| s.text,
        .string => |s| s,
        else => null,
    };
}

fn normalizeMacroRefTokenText(t: []const u8) ?[]const u8 {
    if (!std.mem.startsWith(u8, t, "#$:")) return null;
    var rest = t["#$:".len..];
    if (std.mem.startsWith(u8, rest, "$ion::")) rest = rest["$ion::".len..];
    return rest;
}

fn isSexpHeadToken(sx: []const value.Element, head: []const u8) bool {
    if (sx.len == 0) return false;
    const t = headTokenText(sx[0]) orelse return false;
    return std.mem.eql(u8, t, head);
}

const Env = struct {
    parent: ?*const Env,
    bindings: std.StringHashMapUnmanaged([]const value.Element) = .{},

    fn deinit(self: *Env, allocator: std.mem.Allocator) void {
        self.bindings.deinit(allocator);
    }

    fn get(self: *const Env, name: []const u8) ?[]const value.Element {
        if (self.bindings.get(name)) |v| return v;
        if (self.parent) |p| return p.get(name);
        return null;
    }
};

fn isSymbolText(e: value.Element, text: []const u8) bool {
    if (e.value != .symbol) return false;
    const t = e.value.symbol.text orelse return false;
    return std.mem.eql(u8, t, text);
}

fn symbolText(e: value.Element) ?[]const u8 {
    if (e.value != .symbol) return null;
    return e.value.symbol.text;
}

fn asSexp(e: value.Element) ?[]const value.Element {
    if (e.value != .sexp) return null;
    return e.value.sexp;
}

fn normalizeTemplateMacroHead(head: []const u8) []const u8 {
    var name = head;
    if (name.len != 0 and name[0] == '.') name = name[1..];
    if (std.mem.startsWith(u8, name, "$ion::")) name = name["$ion::".len..];
    return name;
}

fn concatValueSlices(arena: *value.Arena, parts: []const []const value.Element) IonError![]const value.Element {
    var total: usize = 0;
    for (parts) |p| total += p.len;
    if (total == 0) return &.{};
    const out = arena.allocator().alloc(value.Element, total) catch return IonError.OutOfMemory;
    var idx: usize = 0;
    for (parts) |p| {
        if (p.len != 0) {
            @memcpy(out[idx .. idx + p.len], p);
            idx += p.len;
        }
    }
    return out;
}

fn bindParams(
    arena: *value.Arena,
    macro_def: ion.macro.Macro,
    arg_exprs: []const []const value.Element,
) IonError!Env {
    var env: Env = .{ .parent = null };
    errdefer env.deinit(arena.allocator());

    const params = macro_def.params;
    if (params.len == 0) {
        if (arg_exprs.len != 0) return IonError.InvalidIon;
        return env;
    }

    // Rest syntax policy: only the final non-exactly-one parameter can absorb extra expressions.
    const last = params.len - 1;
    const last_is_variadic = params[last].card != .one;
    const max_exprs: usize = if (last_is_variadic) std.math.maxInt(usize) else params.len;
    if (arg_exprs.len > max_exprs) return IonError.InvalidIon;

    var arg_i: usize = 0;
    var p_i: usize = 0;
    while (p_i < params.len) : (p_i += 1) {
        const p = params[p_i];
        const name = p.name;

        const assigned: []const []const value.Element = blk: {
            if (p_i == last and last_is_variadic) {
                break :blk arg_exprs[arg_i..];
            }
            if (arg_i < arg_exprs.len) {
                const one = arena.allocator().alloc([]const value.Element, 1) catch return IonError.OutOfMemory;
                one[0] = arg_exprs[arg_i];
                arg_i += 1;
                break :blk one;
            }
            // Missing argument expression: treat as absent/empty group.
            break :blk &.{&.{}};
        };

        const vals = try concatValueSlices(arena, assigned);
        switch (p.card) {
            .one => if (vals.len != 1) return IonError.InvalidIon,
            .zero_or_one => if (vals.len > 1) return IonError.InvalidIon,
            .one_or_many => if (vals.len == 0) return IonError.InvalidIon,
            .zero_or_many => {},
        }

        // Conformance doesn't depend on parameter encoding in the template evaluator yet.
        _ = p.ty;

        env.bindings.put(arena.allocator(), name, vals) catch return IonError.OutOfMemory;
    }

    if (!last_is_variadic and arg_i != arg_exprs.len) return IonError.InvalidIon;
    return env;
}

fn evalContainerChildren(
    arena: *value.Arena,
    tab: ?*const ion.macro.MacroTable,
    env: *const Env,
    items: []const value.Element,
) IonError![]value.Element {
    var out = std.ArrayListUnmanaged(value.Element){};
    errdefer out.deinit(arena.allocator());
    for (items) |child| {
        const vals = try evalExpr(arena, tab, env, child);
        out.appendSlice(arena.allocator(), vals) catch return IonError.OutOfMemory;
    }
    return out.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
}

fn evalIf(
    arena: *value.Arena,
    tab: ?*const ion.macro.MacroTable,
    env: *const Env,
    kind: enum { if_none, if_some, if_single, if_multi },
    args: []const value.Element,
) IonError![]value.Element {
    // All arguments are optional trailing parameters.
    const test_vals = if (args.len >= 1) try evalExpr(arena, tab, env, args[0]) else &.{};
    const test_len = test_vals.len;

    const cond: bool = switch (kind) {
        .if_none => test_len == 0,
        .if_some => test_len != 0,
        .if_single => test_len == 1,
        .if_multi => test_len > 1,
    };

    if (cond) {
        if (args.len < 2) return &.{};
        return evalExpr(arena, tab, env, args[1]);
    }

    // False branch is implicit rest args: evaluate args[2..] only.
    if (args.len <= 2) return &.{};
    var out = std.ArrayListUnmanaged(value.Element){};
    errdefer out.deinit(arena.allocator());
    for (args[2..]) |e| {
        const vals = try evalExpr(arena, tab, env, e);
        out.appendSlice(arena.allocator(), vals) catch return IonError.OutOfMemory;
    }
    return out.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
}

fn evalFor(
    arena: *value.Arena,
    tab: ?*const ion.macro.MacroTable,
    env: *const Env,
    args: []const value.Element,
) IonError![]value.Element {
    if (args.len < 2) return IonError.InvalidIon;
    const bindings_spec = args[0];
    const body_expr = args[1];
    if (args.len != 2) return IonError.InvalidIon;

    const binding_clauses: []const value.Element = switch (bindings_spec.value) {
        .list => |items| items,
        .sexp => |sx| blk: {
            // Either:
            // - a single binding clause: `(x 1 2 3)` (first item is a symbol), or
            // - a container of binding clauses: `((x 1 2 3) (y 4 5 6))` (first item is a sexp).
            if (sx.len != 0 and sx[0].value == .sexp) break :blk sx;
            break :blk &.{bindings_spec};
        },
        else => return IonError.InvalidIon,
    };

    if (binding_clauses.len == 0) return IonError.InvalidIon;

    const Binding = struct {
        name: []const u8,
        stream: []const value.Element,
    };

    var binds = std.ArrayListUnmanaged(Binding){};
    errdefer binds.deinit(arena.allocator());

    // Evaluate each binding stream in the *outer* environment.
    for (binding_clauses) |cl| {
        const sx = asSexp(cl) orelse return IonError.InvalidIon;
        if (sx.len == 0) return IonError.InvalidIon;
        if (sx[0].annotations.len != 0) return IonError.InvalidIon;
        const name = symbolText(sx[0]) orelse return IonError.InvalidIon;
        if (name.len == 0) return IonError.InvalidIon;
        // Disallow binding name 'null' (conformance wants these rejected).
        if (std.mem.eql(u8, name, "null")) return IonError.InvalidIon;

        // Stream expressions are the remaining expressions in the clause.
        var stream_out = std.ArrayListUnmanaged(value.Element){};
        errdefer stream_out.deinit(arena.allocator());
        for (sx[1..]) |expr| {
            const vals = try evalExpr(arena, tab, env, expr);
            stream_out.appendSlice(arena.allocator(), vals) catch return IonError.OutOfMemory;
        }
        const stream = stream_out.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
        binds.append(arena.allocator(), .{ .name = name, .stream = stream }) catch return IonError.OutOfMemory;
    }

    // Determine iteration count (shortest stream length).
    var iter_count: usize = std.math.maxInt(usize);
    for (binds.items) |b| iter_count = @min(iter_count, b.stream.len);
    if (iter_count == 0 or iter_count == std.math.maxInt(usize)) return &.{};

    var out = std.ArrayListUnmanaged(value.Element){};
    errdefer out.deinit(arena.allocator());

    var idx: usize = 0;
    while (idx < iter_count) : (idx += 1) {
        var frame: Env = .{ .parent = env };
        defer frame.deinit(arena.allocator());

        for (binds.items) |b| {
            const one = arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            one[0] = b.stream[idx];
            frame.bindings.put(arena.allocator(), b.name, one) catch return IonError.OutOfMemory;
        }

        const vals = try evalExpr(arena, tab, &frame, body_expr);
        out.appendSlice(arena.allocator(), vals) catch return IonError.OutOfMemory;
    }

    return out.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
}

fn evalMacroInvocation(
    arena: *value.Arena,
    tab: ?*const ion.macro.MacroTable,
    env: *const Env,
    head_text: []const u8,
    args: []const value.Element,
) IonError![]value.Element {
    const name = normalizeTemplateMacroHead(head_text);

    if (std.mem.eql(u8, name, "literal")) {
        // `.literal` returns its arguments as literal Ion values (no template evaluation).
        if (args.len == 0) return &.{};
        const out = arena.allocator().alloc(value.Element, args.len) catch return IonError.OutOfMemory;
        @memcpy(out, args);
        return out;
    }

    if (std.mem.eql(u8, name, "for")) return evalFor(arena, tab, env, args);
    if (std.mem.eql(u8, name, "if_none")) return evalIf(arena, tab, env, .if_none, args);
    if (std.mem.eql(u8, name, "if_some")) return evalIf(arena, tab, env, .if_some, args);
    if (std.mem.eql(u8, name, "if_single")) return evalIf(arena, tab, env, .if_single, args);
    if (std.mem.eql(u8, name, "if_multi")) return evalIf(arena, tab, env, .if_multi, args);

    // System macros (subset): same semantics as their e-expression counterparts.
    if (std.mem.eql(u8, name, "none")) {
        if (args.len != 0) return IonError.InvalidIon;
        return &.{};
    }
    if (std.mem.eql(u8, name, "values")) {
        var out = std.ArrayListUnmanaged(value.Element){};
        errdefer out.deinit(arena.allocator());
        for (args) |a| {
            const vals = try evalExpr(arena, tab, env, a);
            out.appendSlice(arena.allocator(), vals) catch return IonError.OutOfMemory;
        }
        return out.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
    }
    if (std.mem.eql(u8, name, "default")) {
        // Lazy: return first argument expression that yields any values.
        for (args) |a| {
            const vals = try evalExpr(arena, tab, env, a);
            if (vals.len != 0) return vals;
        }
        return &.{};
    }
    if (std.mem.eql(u8, name, "repeat")) {
        if (args.len != 2) return IonError.InvalidIon;
        const count_vals = try evalExpr(arena, tab, env, args[0]);
        if (count_vals.len != 1) return IonError.InvalidIon;
        if (count_vals[0].value != .int) return IonError.InvalidIon;
        const count_i128: i128 = switch (count_vals[0].value.int) {
            .small => |v| v,
            .big => return IonError.Unsupported,
        };
        if (count_i128 < 0) return IonError.InvalidIon;
        const count: usize = @intCast(count_i128);

        const vals = try evalExpr(arena, tab, env, args[1]);
        if (count == 0 or vals.len == 0) return &.{};

        const total: usize = std.math.mul(usize, count, vals.len) catch return IonError.OutOfMemory;
        const out = arena.allocator().alloc(value.Element, total) catch return IonError.OutOfMemory;
        var idx: usize = 0;
        var k: usize = 0;
        while (k < count) : (k += 1) {
            @memcpy(out[idx .. idx + vals.len], vals);
            idx += vals.len;
        }
        return out;
    }
    if (std.mem.eql(u8, name, "delta")) {
        var deltas = std.ArrayListUnmanaged(i128){};
        defer deltas.deinit(arena.allocator());
        for (args) |a| {
            const vals = try evalExpr(arena, tab, env, a);
            for (vals) |e| {
                if (e.value != .int) return IonError.InvalidIon;
                const v: i128 = switch (e.value.int) {
                    .small => |vv| vv,
                    .big => return IonError.Unsupported,
                };
                deltas.append(arena.allocator(), v) catch return IonError.OutOfMemory;
            }
        }
        if (deltas.items.len == 0) return &.{};

        const out = arena.allocator().alloc(value.Element, deltas.items.len) catch return IonError.OutOfMemory;
        var acc: i128 = 0;
        for (deltas.items, 0..) |d, i| {
            if (i == 0) acc = d else acc = std.math.add(i128, acc, d) catch return IonError.InvalidIon;
            out[i] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = acc } } };
        }
        return out;
    }
    if (std.mem.eql(u8, name, "parse_ion")) {
        if (args.len != 1) return IonError.InvalidIon;
        const arg = args[0];
        if (arg.annotations.len != 0) return IonError.InvalidIon;
        const bytes: []const u8 = switch (arg.value) {
            .string => |s| s,
            .clob => |b| b,
            .blob => |b| b,
            else => return IonError.InvalidIon,
        };
        return parseEmbeddedIon(arena, bytes);
    }
    if (std.mem.eql(u8, name, "make_string") or std.mem.eql(u8, name, "make_symbol")) {
        var buf = std.ArrayListUnmanaged(u8){};
        errdefer buf.deinit(arena.allocator());
        for (args) |a| {
            const vals = try evalExpr(arena, tab, env, a);
            for (vals) |e| {
                switch (e.value) {
                    .string => |s| buf.appendSlice(arena.allocator(), s) catch return IonError.OutOfMemory,
                    .symbol => |s| {
                        const t = s.text orelse return IonError.InvalidIon;
                        buf.appendSlice(arena.allocator(), t) catch return IonError.OutOfMemory;
                    },
                    else => return IonError.InvalidIon,
                }
            }
        }
        const out_text = buf.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
        const out_elem: value.Element = .{
            .annotations = &.{},
            .value = if (std.mem.eql(u8, name, "make_string")) .{ .string = out_text } else .{ .symbol = value.makeSymbolId(null, out_text) },
        };
        const out = arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
        out[0] = out_elem;
        return out;
    }
    if (std.mem.eql(u8, name, "make_field")) {
        if (args.len != 2) return IonError.InvalidIon;
        const name_vals = try evalExpr(arena, tab, env, args[0]);
        const val_vals = try evalExpr(arena, tab, env, args[1]);
        if (name_vals.len != 1 or val_vals.len != 1) return IonError.InvalidIon;
        const name_elem = name_vals[0];
        const val_elem = val_vals[0];
        const name_sym: value.Symbol = switch (name_elem.value) {
            .string => |s| try value.makeSymbol(arena, s),
            .symbol => |s| s,
            else => return IonError.InvalidIon,
        };
        const fields = arena.allocator().alloc(value.StructField, 1) catch return IonError.OutOfMemory;
        fields[0] = .{ .name = name_sym, .value = val_elem };
        const out_elem = value.Element{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = fields } } };
        const out = arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
        out[0] = out_elem;
        return out;
    }
    if (std.mem.eql(u8, name, "annotate")) {
        // (annotate <annotations-expr> <value-expr>)
        if (args.len != 2) return IonError.InvalidIon;
        const ann_vals = try evalExpr(arena, tab, env, args[0]);
        const val_vals = try evalExpr(arena, tab, env, args[1]);
        if (val_vals.len != 1) return IonError.InvalidIon;

        var anns = std.ArrayListUnmanaged(value.Symbol){};
        errdefer anns.deinit(arena.allocator());
        for (ann_vals) |e| {
            // Argument annotations are silently dropped.
            switch (e.value) {
                .string => |s| anns.append(arena.allocator(), try value.makeSymbol(arena, s)) catch return IonError.OutOfMemory,
                .symbol => |s| anns.append(arena.allocator(), s) catch return IonError.OutOfMemory,
                else => return IonError.InvalidIon,
            }
        }

        const v = val_vals[0];
        var all = std.ArrayListUnmanaged(value.Symbol){};
        errdefer all.deinit(arena.allocator());
        all.appendSlice(arena.allocator(), anns.items) catch return IonError.OutOfMemory;
        all.appendSlice(arena.allocator(), v.annotations) catch return IonError.OutOfMemory;

        const out_elem: value.Element = .{ .annotations = all.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory, .value = v.value };
        const out = arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
        out[0] = out_elem;
        return out;
    }
    if (std.mem.eql(u8, name, "make_struct")) {
        // Concatenate fields from each struct argument in order (duplicates preserved).
        var total_fields: usize = 0;
        var structs = std.ArrayListUnmanaged(value.Element){};
        errdefer structs.deinit(arena.allocator());
        for (args) |a| {
            const vals = try evalExpr(arena, tab, env, a);
            structs.appendSlice(arena.allocator(), vals) catch return IonError.OutOfMemory;
        }
        for (structs.items) |e| {
            if (e.value != .@"struct") return IonError.InvalidIon;
            total_fields += e.value.@"struct".fields.len;
        }
        const fields = arena.allocator().alloc(value.StructField, total_fields) catch return IonError.OutOfMemory;
        var idx: usize = 0;
        for (structs.items) |e| {
            const st = e.value.@"struct";
            @memcpy(fields[idx .. idx + st.fields.len], st.fields);
            idx += st.fields.len;
        }
        const out_elem = value.Element{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = fields } } };
        const out = arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
        out[0] = out_elem;
        return out;
    }
    if (std.mem.eql(u8, name, "make_list") or std.mem.eql(u8, name, "make_sexp")) {
        var out_items = std.ArrayListUnmanaged(value.Element){};
        errdefer out_items.deinit(arena.allocator());
        for (args) |a| {
            const vals = try evalExpr(arena, tab, env, a);
            for (vals) |e| {
                switch (e.value) {
                    .list => |items| out_items.appendSlice(arena.allocator(), items) catch return IonError.OutOfMemory,
                    .sexp => |items| out_items.appendSlice(arena.allocator(), items) catch return IonError.OutOfMemory,
                    else => return IonError.InvalidIon,
                }
            }
        }
        const seq = out_items.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
        const out_elem = value.Element{
            .annotations = &.{},
            .value = if (std.mem.eql(u8, name, "make_list")) .{ .list = seq } else .{ .sexp = seq },
        };
        const out = arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
        out[0] = out_elem;
        return out;
    }
    if (std.mem.eql(u8, name, "flatten")) {
        var out = std.ArrayListUnmanaged(value.Element){};
        errdefer out.deinit(arena.allocator());
        for (args) |a| {
            const vals = try evalExpr(arena, tab, env, a);
            for (vals) |e| {
                switch (e.value) {
                    .list => |items| out.appendSlice(arena.allocator(), items) catch return IonError.OutOfMemory,
                    .sexp => |items| out.appendSlice(arena.allocator(), items) catch return IonError.OutOfMemory,
                    else => return IonError.InvalidIon,
                }
            }
        }
        return out.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
    }

    // User macro invocation in a template body.
    if (tab) |t| {
        if (t.macroForName(name)) |m| {
            // Each argument is a template expression.
            const arg_exprs = arena.allocator().alloc([]const value.Element, args.len) catch return IonError.OutOfMemory;
            for (args, 0..) |a, i| arg_exprs[i] = try evalExpr(arena, tab, env, a);
            return expandUserMacro(arena, t, m, arg_exprs);
        }
    }

    return IonError.Unsupported;
}

fn parseEmbeddedIon(arena: *value.Arena, bytes: []const u8) IonError![]value.Element {
    if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x00 and bytes[3] == 0xEA) {
        return ion.binary.parseTopLevel(arena, bytes);
    }
    if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x01 and bytes[3] == 0xEA) {
        return ion.binary11.parseTopLevelWithMacroTable(arena, bytes, null);
    }
    return ion.text.parseTopLevelWithMacroTable(arena, bytes, null);
}

fn evalExpr(arena: *value.Arena, tab: ?*const ion.macro.MacroTable, env: *const Env, expr: value.Element) IonError![]value.Element {
    // Variable expansion: `(%x)` or `(% x)`
    if (expr.value == .sexp) {
        const sx = expr.value.sexp;
        if (expr.annotations.len == 0 and sx.len != 0) {
            // `(%x)` encoded as a single token in conformance DSL.
            if (sx.len == 1 and sx[0].annotations.len == 0 and sx[0].value == .symbol) {
                const t = sx[0].value.symbol.text orelse return IonError.InvalidIon;
                if (t.len >= 2 and t[0] == '%') {
                    const name = t[1..];
                    const bound = env.get(name) orelse return IonError.InvalidIon;
                    return evalBoundExprs(arena, tab, env, bound);
                }
                if (std.mem.eql(u8, t, "..")) {
                    // Expression group `(.. <expr>*)`: concatenate expansions.
                    return @constCast(&.{});
                }
            }
            if (sx.len == 2 and sx[0].annotations.len == 0 and sx[1].annotations.len == 0 and sx[0].value == .symbol and sx[1].value == .symbol) {
                const op = sx[0].value.symbol.text orelse return IonError.InvalidIon;
                const name = sx[1].value.symbol.text orelse return IonError.InvalidIon;
                if (std.mem.eql(u8, op, "%")) {
                    const bound = env.get(name) orelse return IonError.InvalidIon;
                    return evalBoundExprs(arena, tab, env, bound);
                }
            }
        }
    }

    // Conformance abstract syntax can embed e-expressions as sexps whose head is a macro-ref token
    // like `#$:foo` (or `#$:$ion::values`). Treat these as macro invocations during evaluation.
    if (expr.value == .sexp and expr.annotations.len == 0) {
        const sx = expr.value.sexp;
        if (sx.len != 0) {
            if (headTokenText(sx[0])) |t| {
                if (normalizeMacroRefTokenText(t)) |name| {
                    if (std.mem.eql(u8, name, "values")) {
                        var out = std.ArrayListUnmanaged(value.Element){};
                        errdefer out.deinit(arena.allocator());
                        for (sx[1..]) |a| {
                            const vals = try evalExpr(arena, tab, env, a);
                            out.appendSlice(arena.allocator(), vals) catch return IonError.OutOfMemory;
                        }
                        return out.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
                    }

                    if (tab) |tref| {
                        if (tref.macroForName(name)) |m| {
                            const arg_exprs = arena.allocator().alloc([]const value.Element, sx.len - 1) catch return IonError.OutOfMemory;
                            for (sx[1..], 0..) |a, i| {
                                if (a.value == .sexp and isSexpHeadToken(a.value.sexp, "#$::")) {
                                    const gsx = a.value.sexp;
                                    const inner = gsx[1..];
                                    // Evaluate each child as a single-valued expression.
                                    const group_out = arena.allocator().alloc(value.Element, inner.len) catch return IonError.OutOfMemory;
                                    for (inner, 0..) |v, j| {
                                        const one = try evalExpr(arena, tab, env, v);
                                        if (one.len != 1) return IonError.InvalidIon;
                                        group_out[j] = one[0];
                                    }
                                    arg_exprs[i] = group_out;
                                } else {
                                    arg_exprs[i] = try evalExpr(arena, tab, env, a);
                                }
                            }
                            return expandUserMacro(arena, tref, m, arg_exprs);
                        }
                    }

                    return IonError.Unsupported;
                }
            }
        }
    }

    // Expression group: `(.. <expr>*)` concatenates values.
    if (expr.value == .sexp and expr.annotations.len == 0) {
        const sx = expr.value.sexp;
        if (sx.len != 0 and sx[0].annotations.len == 0 and sx[0].value == .symbol) {
            const head_t = sx[0].value.symbol.text orelse return IonError.InvalidIon;
            if (std.mem.eql(u8, head_t, "..")) {
                var out = std.ArrayListUnmanaged(value.Element){};
                errdefer out.deinit(arena.allocator());
                for (sx[1..]) |e| {
                    const vals = try evalExpr(arena, tab, env, e);
                    out.appendSlice(arena.allocator(), vals) catch return IonError.OutOfMemory;
                }
                return out.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
            }
        }
    }

    // Template macro invocation: unquoted s-expression with head starting with '.'.
    if (expr.value == .sexp and expr.annotations.len == 0) {
        const sx = expr.value.sexp;
        if (sx.len != 0 and sx[0].annotations.len == 0 and sx[0].value == .symbol) {
            const head_t = sx[0].value.symbol.text orelse return IonError.InvalidIon;
            if (head_t.len != 0 and head_t[0] == '.') {
                // Ion text tokenization treats `.name` as operator `.` + identifier `name`.
                // Conformance `mactab` parsing allows `.name` as a single token, but macro
                // definitions embedded in ordinary Ion text (e.g. via `(:add_macros ...)`) may
                // arrive here as `(. name ...)`. Support both representations.
                if (std.mem.eql(u8, head_t, ".")) {
                    if (sx.len < 2) return IonError.InvalidIon;
                    if (sx[1].annotations.len != 0 or sx[1].value != .symbol) return IonError.InvalidIon;
                    const name = sx[1].value.symbol.text orelse return IonError.InvalidIon;
                    const combined = arena.allocator().alloc(u8, 1 + name.len) catch return IonError.OutOfMemory;
                    combined[0] = '.';
                    @memcpy(combined[1..], name);
                    return evalMacroInvocation(arena, tab, env, combined, sx[2..]);
                }
                return evalMacroInvocation(arena, tab, env, head_t, sx[1..]);
            }
        }
    }

    // Container literals can contain template expressions that must be evaluated/spliced.
    switch (expr.value) {
        .list => |items| {
            const evaluated = try evalContainerChildren(arena, tab, env, items);
            const out_elem: value.Element = .{ .annotations = expr.annotations, .value = .{ .list = evaluated } };
            const out = arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        },
        .sexp => |items| {
            const evaluated = try evalContainerChildren(arena, tab, env, items);
            const out_elem: value.Element = .{ .annotations = expr.annotations, .value = .{ .sexp = evaluated } };
            const out = arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        },
        .@"struct" => |st| {
            var out_fields = std.ArrayListUnmanaged(value.StructField){};
            errdefer out_fields.deinit(arena.allocator());
            for (st.fields) |f| {
                const vals = try evalExpr(arena, tab, env, f.value);
                if (vals.len == 0) continue; // omit field
                if (vals.len != 1) return IonError.InvalidIon;
                out_fields.append(arena.allocator(), .{ .name = f.name, .value = vals[0] }) catch return IonError.OutOfMemory;
            }
            const out_elem: value.Element = .{ .annotations = expr.annotations, .value = .{ .@"struct" = .{ .fields = out_fields.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory } } };
            const out = arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        },
        else => {
            const out = arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = expr;
            return out;
        },
    }
}

fn evalBoundExprs(
    arena: *value.Arena,
    tab: ?*const ion.macro.MacroTable,
    env: *const Env,
    bound: []const value.Element,
) IonError![]value.Element {
    // Important: variable expansions return value expressions, which may themselves contain
    // e-expressions (in conformance abstract syntax). Evaluate each bound expression in the
    // current environment so nested macro refs are expanded.
    if (bound.len == 0) return &.{};
    var out = std.ArrayListUnmanaged(value.Element){};
    errdefer out.deinit(arena.allocator());
    for (bound) |e| {
        const vals = try evalExpr(arena, tab, env, e);
        out.appendSlice(arena.allocator(), vals) catch return IonError.OutOfMemory;
    }
    return out.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
}

pub fn expandUserMacro(
    arena: *value.Arena,
    tab: *const ion.macro.MacroTable,
    macro_def: ion.macro.Macro,
    arg_exprs: []const []const value.Element,
) IonError![]value.Element {
    var env = try bindParams(arena, macro_def, arg_exprs);
    defer env.deinit(arena.allocator());

    var out = std.ArrayListUnmanaged(value.Element){};
    errdefer out.deinit(arena.allocator());
    for (macro_def.body) |expr| {
        const vals = try evalExpr(arena, tab, &env, expr);
        out.appendSlice(arena.allocator(), vals) catch return IonError.OutOfMemory;
    }
    return out.toOwnedSlice(arena.allocator()) catch return IonError.OutOfMemory;
}
