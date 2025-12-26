//! Ion 1.1 macro table support (minimal).
//!
//! This module exists primarily to support the `ion-tests/conformance` suite, which uses `mactab`
//! clauses and exercises Ion 1.1 binary e-expressions.
//!
//! Scope: only the subset needed by the current conformance progress. Anything unimplemented
//! should return `IonError.Unsupported` so callers can count it as a conformance skip.

const std = @import("std");
const ion = @import("../ion.zig");
const value = @import("value.zig");

const IonError = ion.IonError;

pub const ParamType = enum {
    tagged,
    /// A macro shape (or qualified type name) used as a tagless encoding.
    ///
    /// Conformance/demo macros (e.g. `demos/metaprogramming.ion`) use annotations like:
    /// - `tiny_decimal::vals` (macro shape)
    /// - `$ion::make_decimal::vals` (qualified system macro shape)
    ///
    /// The payload (shape name/module) is stored in `Param.shape`.
    macro_shape,
    flex_sym,
    flex_uint,
    flex_int,
    uint8,
    uint16,
    uint32,
    uint64,
    int8,
    int16,
    int32,
    int64,
    float16,
    float32,
    float64,
};

pub const Cardinality = enum { one, zero_or_one, zero_or_many, one_or_many };

pub const Param = struct {
    ty: ParamType,
    card: Cardinality,
    name: []const u8,
    shape: ?MacroShape = null,
};

pub const MacroShape = struct {
    module: ?[]const u8,
    name: []const u8,
};

pub const Macro = struct {
    /// Null means the macro is address-only.
    name: ?[]const u8,
    params: []Param,
    /// Body expressions as Ion elements (TDL-ish). For now, conformance only needs `%x` expansion.
    body: []const value.Element,
};

pub const MacroTable = struct {
    macros: []Macro,

    pub fn macroForAddress(self: *const MacroTable, addr: usize) ?Macro {
        if (addr >= self.macros.len) return null;
        return self.macros[addr];
    }

    pub fn addressForName(self: *const MacroTable, name: []const u8) ?usize {
        for (self.macros, 0..) |m, idx| {
            if (m.name) |n| {
                if (std.mem.eql(u8, n, name)) return idx;
            }
        }
        return null;
    }

    pub fn macroForName(self: *const MacroTable, name: []const u8) ?Macro {
        for (self.macros) |m| {
            if (m.name) |n| {
                if (std.mem.eql(u8, n, name)) return m;
            }
        }
        return null;
    }
};

pub fn parseMacroTable(allocator: std.mem.Allocator, items: []const value.Element) IonError!MacroTable {
    var out = std.ArrayListUnmanaged(Macro){};
    errdefer out.deinit(allocator);

    for (items) |it| {
        const m = try parseMacroDef(allocator, it);
        try validateMacroDefForConformance(m);
        out.append(allocator, m) catch return IonError.OutOfMemory;
    }

    return .{ .macros = out.toOwnedSlice(allocator) catch return IonError.OutOfMemory };
}

fn parseMacroDef(allocator: std.mem.Allocator, it: value.Element) IonError!Macro {
    if (it.annotations.len != 0) return IonError.InvalidIon;
    if (it.value != .sexp) return IonError.InvalidIon;
    const sx = it.value.sexp;
    // Conformance: macro definitions must include a parameter list *and* at least one body
    // expression.
    if (sx.len < 4) return IonError.InvalidIon;
    if (sx[0].value != .symbol) return IonError.InvalidIon;
    const head = sx[0].value.symbol.text orelse return IonError.InvalidIon;
    if (!std.mem.eql(u8, head, "macro")) return IonError.InvalidIon;

    const name: ?[]const u8 = switch (sx[1].value) {
        .null => null,
        .symbol => |s| s.text orelse return IonError.InvalidIon,
        else => return IonError.InvalidIon,
    };

    if (sx[2].value != .sexp) return IonError.InvalidIon;
    const params_sx = sx[2].value.sexp;
    var params = std.ArrayListUnmanaged(Param){};
    errdefer params.deinit(allocator);
    for (params_sx) |p| {
        // Conformance/demo input sometimes expresses parameter cardinality as a separate token
        // following the parameter name, e.g. `vals *` (instead of `vals*`).
        if (p.annotations.len == 0 and p.value == .symbol) {
            const t = p.value.symbol.text orelse return IonError.InvalidIon;
            if (t.len == 1) {
                const card: ?Cardinality = switch (t[0]) {
                    '?' => .zero_or_one,
                    '*' => .zero_or_many,
                    '+' => .one_or_many,
                    else => null,
                };
                if (card) |c| {
                    if (params.items.len == 0) return IonError.InvalidIon;
                    if (params.items[params.items.len - 1].card != .one) return IonError.InvalidIon;
                    params.items[params.items.len - 1].card = c;
                    continue;
                }
            }
        }

        params.append(allocator, try parseParam(p)) catch return IonError.OutOfMemory;
    }

    return .{
        .name = name,
        .params = params.toOwnedSlice(allocator) catch return IonError.OutOfMemory,
        .body = sx[3..],
    };
}

fn validateMacroDefForConformance(m: Macro) IonError!void {
    // Conformance suite expects some macro table definitions to be rejected as "invalid macro
    // definition" (for example: `system_macros/parse_ion.ion` requires `.parse_ion`'s argument to
    // be a literal). We don't implement a full TDL evaluator, but we do a small amount of
    // validation so these branches can be executed (rather than treated as a hard conformance DSL
    // failure).
    var scope: Scope = .{};
    for (m.params) |p| try scope.add(p.name);

    for (m.body) |expr| {
        try validateTemplateExprForConformance(&scope, expr, false);

        if (expr.value != .sexp) continue;
        const sx = expr.value.sexp;
        if (sx.len == 0) continue;
        if (sx[0].value != .symbol) continue;
        const head = sx[0].value.symbol.text orelse continue;

        const norm = blk: {
            var n = head;
            if (n.len != 0 and n[0] == '.') n = n[1..];
            if (std.mem.startsWith(u8, n, "$ion::")) n = n["$ion::".len..];
            break :blk n;
        };

        if (std.mem.eql(u8, head, ".parse_ion") or std.mem.eql(u8, head, "parse_ion")) {
            if (sx.len != 2) return IonError.InvalidIon;
            // `.parse_ion` requires its argument to be a literal string/clob/blob (not a macro
            // invocation, variable, or special form).
            switch (sx[1].value) {
                .string, .clob, .blob => {},
                else => return IonError.InvalidIon,
            }
        }

        // Conformance: system values may only occur where system values can occur (not inside TDL).
        if (std.mem.eql(u8, norm, "use") or
            std.mem.eql(u8, norm, "set_symbols") or
            std.mem.eql(u8, norm, "add_symbols") or
            std.mem.eql(u8, norm, "set_macros") or
            std.mem.eql(u8, norm, "add_macros"))
        {
            return IonError.InvalidIon;
        }

        // Minimal validation for `.for` used by `ion-tests/conformance/tdl/for.ion`.
        if (std.mem.eql(u8, norm, "for")) {
            try validateForForConformance(m.params, sx);
        }
    }
}

const Scope = struct {
    buf: [128][]const u8 = undefined,
    len: usize = 0,

    fn slice(self: *const @This()) []const []const u8 {
        return self.buf[0..self.len];
    }

    fn contains(self: *const @This(), name: []const u8) bool {
        for (self.slice()) |s| if (std.mem.eql(u8, s, name)) return true;
        return false;
    }

    fn add(self: *@This(), name: []const u8) IonError!void {
        if (self.len >= self.buf.len) return IonError.InvalidIon;
        self.buf[self.len] = name;
        self.len += 1;
    }
};

fn normalizeTemplateHead(head: []const u8) []const u8 {
    var n = head;
    if (n.len != 0 and n[0] == '.') n = n[1..];
    if (std.mem.startsWith(u8, n, "$ion::")) n = n["$ion::".len..];
    return n;
}

fn validateTemplateExprForConformance(scope: *const Scope, expr: value.Element, allow_expr_group: bool) IonError!void {
    // `.literal` can wrap arbitrary Ion-shaped forms that would be invalid TDL syntax.
    // Do not validate inside.
    if (expr.value == .sexp and expr.annotations.len == 0) {
        const sx = expr.value.sexp;
        if (sx.len != 0 and sx[0].value == .symbol and sx[0].annotations.len == 0) {
            if (sx[0].value.symbol.text) |t| {
                if (t.len != 0 and t[0] == '.') {
                    const norm = normalizeTemplateHead(t);
                    if (std.mem.eql(u8, norm, "literal")) return;
                }
            }
        }
    }

    // Expression group validation (`ion-tests/conformance/tdl/expression_groups.ion`).
    if (expr.value == .sexp) {
        const sx = expr.value.sexp;
        if (sx.len != 0 and sx[0].value == .symbol) {
            const head_t = sx[0].value.symbol.text orelse "";
            if (std.mem.eql(u8, head_t, "..")) {
                if (!allow_expr_group) return IonError.InvalidIon;
                if (expr.annotations.len != 0) return IonError.InvalidIon;
                if (sx[0].annotations.len != 0) return IonError.InvalidIon;
                // Conformance disallows expression groups containing other expression groups as
                // direct child expressions (e.g. `(.. (..))`), but allows macro invocations that
                // themselves use expression groups.
                for (sx[1..]) |e| if (isExprGroup(e)) return IonError.InvalidIon;
                for (sx[1..]) |e| try validateTemplateExprForConformance(scope, e, false);
                return;
            }
        }
    }

    // Variable expansion validation (`ion-tests/conformance/tdl/variable_expansion.ion`).
    if (expr.value == .sexp) {
        const sx = expr.value.sexp;
        if (sx.len != 0) {
            // (%x) where `%x` is a single token
            if (sx.len == 1 and sx[0].value == .symbol) {
                if (expr.annotations.len != 0) return IonError.InvalidIon;
                if (sx[0].annotations.len != 0) return IonError.InvalidIon;
                const t = sx[0].value.symbol.text orelse return IonError.InvalidIon;
                if (t.len >= 2 and t[0] == '%') {
                    const name = t[1..];
                    if (!scope.contains(name)) return IonError.InvalidIon;
                    return;
                }
            }
            // (% x)
            if (sx[0].value == .symbol) {
                const op = sx[0].value.symbol.text orelse null;
                if (op != null and std.mem.eql(u8, op.?, "%")) {
                    if (expr.annotations.len != 0) return IonError.InvalidIon;
                    if (sx[0].annotations.len != 0) return IonError.InvalidIon;
                    if (sx.len != 2) return IonError.InvalidIon;
                    const name_elem = sx[1];
                    if (name_elem.annotations.len != 0) return IonError.InvalidIon;
                    if (name_elem.value != .symbol) return IonError.InvalidIon;
                    const name = name_elem.value.symbol.text orelse return IonError.InvalidIon;
                    if (!scope.contains(name)) return IonError.InvalidIon;
                    return;
                }
            }
        }
    }

    // `.for` introduces bindings that can be referenced in the body.
    if (expr.value == .sexp and expr.annotations.len == 0) {
        const sx = expr.value.sexp;
        if (sx.len != 0 and sx[0].value == .symbol and sx[0].annotations.len == 0) {
            const head = sx[0].value.symbol.text orelse "";
            if (head.len != 0 and head[0] == '.') {
                const norm = normalizeTemplateHead(head);
                if (std.mem.eql(u8, norm, "for")) {
                    if (sx.len != 3) return; // arity validated elsewhere
                    const bindings = sx[1];
                    const clauses: []const value.Element = switch (bindings.value) {
                        .list => |items| items,
                        .sexp => |inner| blk: {
                            if (inner.len != 0 and inner[0].value == .sexp) break :blk inner;
                            break :blk &.{bindings};
                        },
                        else => return,
                    };

                    // Validate binding streams in the *outer* scope.
                    for (clauses) |cl| {
                        if (cl.value != .sexp) continue;
                        const csx = cl.value.sexp;
                        if (csx.len <= 1) continue;
                        for (csx[1..]) |e| try validateTemplateExprForConformance(scope, e, false);
                    }

                    // Validate body with extended scope.
                    var body_scope = scope.*;
                    for (clauses) |cl| {
                        if (cl.value != .sexp) continue;
                        const csx = cl.value.sexp;
                        if (csx.len == 0) continue;
                        if (csx[0].annotations.len != 0 or csx[0].value != .symbol) continue;
                        if (csx[0].value.symbol.text) |nm| try body_scope.add(nm);
                    }
                    try validateTemplateExprForConformance(&body_scope, sx[2], false);
                    return;
                }
            }
        }
    }

    // Recurse through containers / sexps.
    switch (expr.value) {
        .list => |items| for (items) |e| try validateTemplateExprForConformance(scope, e, false),
        .@"struct" => |st| for (st.fields) |f| try validateTemplateExprForConformance(scope, f.value, false),
        .sexp => |items| blk: {
            var template_invocation = false;
            if (expr.annotations.len == 0 and items.len != 0 and items[0].value == .symbol) {
                if (items[0].value.symbol.text) |t| {
                    if (t.len != 0 and t[0] == '.') template_invocation = true;
                }
            }
            if (template_invocation) {
                const head = items[0].value.symbol.text orelse "";
                const norm = normalizeTemplateHead(head);
                // Conformance: expression groups may not be used as rest args for `.values`.
                if (std.mem.eql(u8, norm, "values")) {
                    var saw_group = false;
                    for (items[1..]) |a| {
                        if (a.value == .sexp) {
                            const asx = a.value.sexp;
                            if (asx.len != 0 and asx[0].value == .symbol) {
                                if (asx[0].value.symbol.text) |ht| {
                                    if (std.mem.eql(u8, ht, "..")) saw_group = true;
                                }
                            }
                        }
                    }
                    if (saw_group and items.len > 2) return IonError.InvalidIon;
                }
                for (items[1..]) |e| try validateTemplateExprForConformance(scope, e, true);
                break :blk;
            }
            for (items) |e| try validateTemplateExprForConformance(scope, e, false);
        },
        else => {},
    }
}

fn isExprGroup(elem: value.Element) bool {
    if (elem.value != .sexp) return false;
    const sx = elem.value.sexp;
    if (sx.len == 0) return false;
    if (sx[0].value != .symbol) return false;
    const t = sx[0].value.symbol.text orelse return false;
    return std.mem.eql(u8, t, "..");
}

fn validateForForConformance(params: []const Param, sx: []const value.Element) IonError!void {
    // Expected: (.for <bindings> <body>)
    if (sx.len != 3) return IonError.InvalidIon;

    const bindings = sx[1];
    const clauses: []const value.Element = switch (bindings.value) {
        .list => |items| items,
        .sexp => |inner| blk: {
            if (inner.len != 0 and inner[0].value == .sexp) break :blk inner;
            break :blk &.{bindings};
        },
        else => return IonError.InvalidIon,
    };
    if (clauses.len == 0) return IonError.InvalidIon;

    const NameSet = struct {
        buf: [64][]const u8 = undefined,
        len: usize = 0,

        fn slice(self: *const @This()) []const []const u8 {
            return self.buf[0..self.len];
        }

        fn contains(self: *const @This(), name: []const u8) bool {
            for (self.slice()) |s| if (std.mem.eql(u8, s, name)) return true;
            return false;
        }

        fn add(self: *@This(), name: []const u8) IonError!void {
            if (self.len >= self.buf.len) return IonError.InvalidIon;
            self.buf[self.len] = name;
            self.len += 1;
        }
    };

    var seen: NameSet = .{};
    var prior: NameSet = .{};
    var allowed: NameSet = .{};
    for (params) |p| try allowed.add(p.name);

    for (clauses) |cl| {
        if (cl.annotations.len != 0) return IonError.InvalidIon;
        if (cl.value != .sexp) return IonError.InvalidIon;
        const csx = cl.value.sexp;
        if (csx.len == 0) return IonError.InvalidIon;

        const name_elem = csx[0];
        if (name_elem.annotations.len != 0) return IonError.InvalidIon;
        if (name_elem.value != .symbol) return IonError.InvalidIon;
        const name = name_elem.value.symbol.text orelse return IonError.InvalidIon;
        if (name.len == 0) return IonError.InvalidIon;
        if (std.mem.eql(u8, name, "null")) return IonError.InvalidIon;

        if (seen.contains(name)) return IonError.InvalidIon;
        try seen.add(name);

        // Binding streams are evaluated in the outer environment (macro params + outer `for`).
        // Referencing a binding name introduced earlier in the same `.for` clause is only valid
        // if that name was already available from the outer env (notably: macro params).
        if (prior.len != 0) {
            for (csx[1..]) |expr| {
                for (prior.slice()) |bound| {
                    if (!allowed.contains(bound) and containsVarRef(bound, expr)) return IonError.InvalidIon;
                }
            }
        }
        try prior.add(name);
    }
}

fn containsVarRef(name: []const u8, elem: value.Element) bool {
    // Variable expansion forms:
    // - `(%x)` encoded as a single symbol token "%x" inside an s-expression.
    // - `(% x)` encoded as operator "%" followed by symbol "x".
    if (elem.value == .sexp) {
        const sx = elem.value.sexp;
        if (elem.annotations.len == 0 and sx.len != 0) {
            if (sx.len == 1 and sx[0].annotations.len == 0 and sx[0].value == .symbol) {
                const t = sx[0].value.symbol.text orelse return false;
                if (t.len >= 2 and t[0] == '%') {
                    return std.mem.eql(u8, t[1..], name);
                }
            }
            if (sx.len == 2 and sx[0].annotations.len == 0 and sx[1].annotations.len == 0 and sx[0].value == .symbol and sx[1].value == .symbol) {
                const op = sx[0].value.symbol.text orelse return false;
                const nm = sx[1].value.symbol.text orelse return false;
                if (std.mem.eql(u8, op, "%")) return std.mem.eql(u8, nm, name);
            }
        }
        for (sx) |e| if (containsVarRef(name, e)) return true;
        return false;
    }
    return switch (elem.value) {
        .list => |items| blk: {
            for (items) |it| if (containsVarRef(name, it)) break :blk true;
            break :blk false;
        },
        .@"struct" => |st| blk: {
            for (st.fields) |f| {
                if (containsVarRef(name, f.value)) break :blk true;
            }
            break :blk false;
        },
        else => false,
    };
}

fn parseParam(p: value.Element) IonError!Param {
    // Conformance DSL expresses tagless parameter types using Ion annotations:
    //   (uint8::x) is parsed as: annotations=["uint8"], value=symbol("x")
    // Tagged parameters have no annotations:
    //   (x) is parsed as: annotations=[], value=symbol("x")
    if (p.value != .symbol) return IonError.InvalidIon;
    const t = p.value.symbol.text orelse return IonError.InvalidIon;
    if (t.len == 0) return IonError.InvalidIon;

    const card = switch (t[t.len - 1]) {
        '?' => Cardinality.zero_or_one,
        '*' => Cardinality.zero_or_many,
        '+' => Cardinality.one_or_many,
        else => Cardinality.one,
    };
    const name = if (card == .one) t else t[0 .. t.len - 1];
    if (name.len == 0) return IonError.InvalidIon;

    if (p.annotations.len == 0) {
        return .{ .ty = .tagged, .card = card, .name = name, .shape = null };
    }

    if (p.annotations.len == 1) {
        const ann = p.annotations[0].text orelse return IonError.InvalidIon;
        if (parseParamType(ann)) |known| {
            return .{ .ty = known, .card = card, .name = name, .shape = null };
        }
        // Unknown single annotation: treat as a macro-shape reference.
        return .{ .ty = .macro_shape, .card = card, .name = name, .shape = .{ .module = null, .name = ann } };
    }

    if (p.annotations.len == 2) {
        const m = p.annotations[0].text orelse return IonError.InvalidIon;
        const ann = p.annotations[1].text orelse return IonError.InvalidIon;
        // Qualified (module, name) macro shape.
        return .{ .ty = .macro_shape, .card = card, .name = name, .shape = .{ .module = m, .name = ann } };
    }

    return IonError.InvalidIon;
}

fn parseParamType(t: []const u8) ?ParamType {
    return if (std.mem.eql(u8, t, "flex_sym") or std.mem.eql(u8, t, "flex_symbol"))
        .flex_sym
    else if (std.mem.eql(u8, t, "flex_uint"))
        .flex_uint
    else if (std.mem.eql(u8, t, "flex_int"))
        .flex_int
    else if (std.mem.eql(u8, t, "uint8"))
        .uint8
    else if (std.mem.eql(u8, t, "uint16"))
        .uint16
    else if (std.mem.eql(u8, t, "uint32"))
        .uint32
    else if (std.mem.eql(u8, t, "uint64"))
        .uint64
    else if (std.mem.eql(u8, t, "int8"))
        .int8
    else if (std.mem.eql(u8, t, "int16"))
        .int16
    else if (std.mem.eql(u8, t, "int32"))
        .int32
    else if (std.mem.eql(u8, t, "int64"))
        .int64
    else if (std.mem.eql(u8, t, "float16"))
        .float16
    else if (std.mem.eql(u8, t, "float32"))
        .float32
    else if (std.mem.eql(u8, t, "float64"))
        .float64
    else
        null;
}
