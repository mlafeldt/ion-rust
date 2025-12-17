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
    if (sx.len < 3) return IonError.InvalidIon;
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
    for (m.body) |expr| {
        if (expr.value != .sexp) continue;
        const sx = expr.value.sexp;
        if (sx.len == 0) continue;
        if (sx[0].value != .symbol) continue;
        const head = sx[0].value.symbol.text orelse continue;

        if (std.mem.eql(u8, head, ".parse_ion") or std.mem.eql(u8, head, "parse_ion")) {
            if (sx.len != 2) return IonError.InvalidIon;
            // `.parse_ion` requires its argument to be a literal string/clob/blob (not a macro
            // invocation, variable, or special form).
            switch (sx[1].value) {
                .string, .clob, .blob => {},
                else => return IonError.InvalidIon,
            }
        }
    }
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

    const ty: ParamType = if (p.annotations.len == 0) blk: {
        break :blk .tagged;
    } else if (p.annotations.len == 1) blk: {
        const ann = p.annotations[0].text orelse return IonError.InvalidIon;
        break :blk parseParamType(ann) orelse return IonError.InvalidIon;
    } else {
        return IonError.InvalidIon;
    };

    return .{ .ty = ty, .card = card, .name = name };
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
