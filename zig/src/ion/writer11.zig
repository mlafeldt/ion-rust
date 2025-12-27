//! Ion 1.1 binary writer (partial).
//!
//! This started as a value-only writer, but has grown a small set of low-level helpers for
//! emitting Ion 1.1 binary e-expressions (including conformance-driven directive/macro patterns).
//! It is still not a full Ion 1.1 module/macro system implementation.
//! For self-contained output, it can emit a minimal module prelude (`$ion::(module ...)`) so user
//! symbols can be encoded by address without relying on external module state.
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
    /// minimal module prelude via `writeBinary11SelfContained` to make the output
    /// deterministic and self-contained.
    symbol_encoding: enum { inline_text_only, addresses } = .addresses,

    /// Optional mapping from user symbol text -> module address (SID) for emitting symbol addresses.
    /// When present and `symbol_encoding == .addresses`, symbols with matching `text` will be
    /// encoded using E1..E3 (or FlexSym positive addresses) instead of inline text.
    user_symbol_ids: ?*const std.StringHashMapUnmanaged(u32) = null,

    /// Optional macro table for encoding `ParamType.macro_shape` arguments.
    /// When absent, writing `macro_shape` arguments is unsupported.
    mactab: ?*const ion.macro.MacroTable = null,

    /// Overrides the Ion 1.1 system symbol table variant used for:
    /// - mapping system symbol text <-> system symbol addresses (0xEE)
    /// - emitting `$ion::(module ...)` clauses (`symbols` vs `symbol_table`)
    /// - choosing canonical system macro addresses when `writer11` provides both
    ///
    /// When null, the variant is chosen by `symtab.systemSymtab11Variant()` (env-driven in
    /// non-test builds; forced to `ion_tests` in Zig tests).
    sys_symtab11_variant: ?symtab.SystemSymtab11Variant = null,

    /// When emitting a self-contained stream (via `writeBinary11SelfContainedWithOptions`),
    /// controls whether the module directive prelude includes a `(macro_table ...)` clause
    /// derived from `mactab`.
    ///
    /// This is primarily useful for producing standalone binaries that can be decoded without
    /// providing an out-of-band macro table. Note that `writer11` still writes *values*, not a
    /// macro AST; this prelude only makes user macro definitions available to the binary reader
    /// during decoding of e-expressions that follow.
    emit_macro_table_prelude: bool = false,

    /// Controls which container encodings the writer emits.
    ///
    /// - `.delimited` emits streaming-friendly delimited containers (`0xF1`/`0xF2`/`0xF3` ... `0xF0`).
    /// - `.length_prefixed` emits short/long containers with explicit lengths (`B0..BF`/`FB`,
    ///   `C0..CF`/`FC`, `D0..DF`/`FD`).
    ///
    /// Both forms are valid Ion 1.1 binary. Delimited is the default because it avoids buffering
    /// the container body in memory before writing.
    container_encoding: enum { delimited, length_prefixed } = .delimited,

    /// Controls how argument groups (presence code `0b10`) are encoded inside length-prefixed
    /// e-expressions (`0xF5`) and unqualified user macro invocations.
    ///
    /// - `.length_prefixed` writes a FlexUInt length followed by a contiguous payload.
    /// - `.delimited` writes FlexUInt(0) and then uses the spec delimited forms:
    ///   - tagged groups end with `0xF0`
    ///   - tagless groups are chunked (`<flexuint chunk_len> <chunk_bytes>* <flexuint 0>`)
    ///
    /// Both forms are valid Ion 1.1. The delimited form is useful for streaming emitters and for
    /// exercising decoder paths that only appear in delimited group encodings.
    arg_group_encoding: enum { length_prefixed, delimited } = .length_prefixed,

    /// Maximum chunk size (in bytes) when `arg_group_encoding == .delimited` and emitting tagless
    /// argument groups (chunked form). This is a soft limit: a single tagless value may exceed
    /// it, in which case that value is emitted as its own chunk.
    arg_group_chunk_max_bytes: usize = 4096,
};

fn effectiveSystemSymtab11Variant(options: Options) symtab.SystemSymtab11Variant {
    return options.sys_symtab11_variant orelse symtab.systemSymtab11Variant();
}

fn systemSymtab11MaxId(options: Options) u32 {
    return switch (effectiveSystemSymtab11Variant(options)) {
        .ion_tests => symtab.SystemSymtab11.max_id,
        .ion_rust => symtab.SystemSymtab11IonRust.max_id,
    };
}

fn systemSymtab11TextForSid(options: Options, sid: u32) ?[]const u8 {
    return switch (effectiveSystemSymtab11Variant(options)) {
        .ion_tests => symtab.SystemSymtab11.textForSid(sid),
        .ion_rust => symtab.SystemSymtab11IonRust.textForSid(sid),
    };
}

fn systemSymtab11SidForText(options: Options, text: []const u8) ?u32 {
    return switch (effectiveSystemSymtab11Variant(options)) {
        .ion_tests => symtab.SystemSymtab11.sidForText(text),
        .ion_rust => symtab.SystemSymtab11IonRust.sidForText(text),
    };
}

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
    return writeBinary11SelfContainedWithOptions(allocator, doc, .{});
}

pub fn writeBinary11SelfContainedWithOptions(allocator: std.mem.Allocator, doc: []const value.Element, options: Options) IonError![]u8 {
    // Emit a minimal `$ion::(module ...)` prelude so non-system symbols can be encoded by address
    // without external module context.
    //
    // This writer keeps a strict contract: it requires `text` for any non-system symbol. SID-only
    // non-system symbols cannot be serialized deterministically in a self-contained stream because
    // their meaning depends on ambient module state.
    var map = std.StringHashMapUnmanaged(u32){};
    defer map.deinit(allocator);
    var user_texts = std.ArrayListUnmanaged([]const u8){};
    defer user_texts.deinit(allocator);

    try collectUserSymbolTexts(allocator, doc, options, &map, &user_texts);

    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    // Ion 1.1 IVM: E0 01 01 EA
    try appendSlice(&out, allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    if (user_texts.items.len != 0 or (options.emit_macro_table_prelude and options.mactab != null)) {
        const tab = if (options.emit_macro_table_prelude) options.mactab else null;
        try writeIonSystemModuleDirectivePrelude(allocator, &out, user_texts.items, tab, options);
    }

    var opts = options;
    opts.symbol_encoding = .addresses;
    opts.user_symbol_ids = &map;
    for (doc) |e| try writeElement(allocator, &out, opts, e);

    return out.toOwnedSlice(allocator) catch return IonError.OutOfMemory;
}

pub fn writeIonSystemModuleDirectivePrelude(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    user_symbol_texts: []const []const u8,
    mactab: ?*const ion.macro.MacroTable,
    options: Options,
) IonError!void {
    // `$ion::(module _ (<symbols-clause> _ <text-or-null>*))`
    //
    // This is not a full Ion 1.1 module writer. It's just enough structure to let our Ion 1.1
    // binary reader track the symbol address space deterministically for roundtrips.
    const ann = [_]value.Symbol{value.makeSymbolId(null, "$ion")};

    const sym_module: value.Symbol = value.makeSymbolId(null, "module");
    const symbols_clause_name: []const u8 = switch (effectiveSystemSymtab11Variant(options)) {
        .ion_tests => "symbols",
        .ion_rust => "symbol_table",
    };
    const sym_symbols: value.Symbol = value.makeSymbolId(null, symbols_clause_name);
    const sym_underscore: value.Symbol = value.makeSymbolId(null, "_");

    var macro_table_clause_items: ?[]value.Element = null;
    defer if (macro_table_clause_items) |items| allocator.free(items);

    var param_name_bufs = std.ArrayListUnmanaged([]u8){};
    defer {
        for (param_name_bufs.items) |b| allocator.free(b);
        param_name_bufs.deinit(allocator);
    }
    var ann_bufs = std.ArrayListUnmanaged([]value.Symbol){};
    defer {
        for (ann_bufs.items) |b| allocator.free(b);
        ann_bufs.deinit(allocator);
    }
    const MacroAllocs = struct {
        macro_items: []value.Element,
        param_items: []value.Element,
    };
    var macro_allocs = std.ArrayListUnmanaged(MacroAllocs){};
    defer {
        for (macro_allocs.items) |a| {
            allocator.free(a.macro_items);
            allocator.free(a.param_items);
        }
        macro_allocs.deinit(allocator);
    }

    const macro_table_clause = if (mactab) |tab| blk: {
        if (tab.macros.len == 0) break :blk null;

        const mkParamName = struct {
            fn run(allocator0: std.mem.Allocator, bufs: *std.ArrayListUnmanaged([]u8), name: []const u8, card: ion.macro.Cardinality) IonError![]const u8 {
                const suffix: ?u8 = switch (card) {
                    .one => null,
                    .zero_or_one => '?',
                    .zero_or_many => '*',
                    .one_or_many => '+',
                };
                const extra: usize = if (suffix != null) 1 else 0;
                const buf = allocator0.alloc(u8, name.len + extra) catch return IonError.OutOfMemory;
                std.mem.copyForwards(u8, buf[0..name.len], name);
                if (suffix) |c| buf[name.len] = c;
                bufs.append(allocator0, buf) catch return IonError.OutOfMemory;
                return buf;
            }
        }.run;

        const mkParamAnnotations = struct {
            fn run(allocator0: std.mem.Allocator, bufs: *std.ArrayListUnmanaged([]value.Symbol), p: ion.macro.Param) IonError![]const value.Symbol {
                const ty_name: ?[]const u8 = switch (p.ty) {
                    .tagged => null,
                    .macro_shape => null,
                    .flex_sym => "flex_sym",
                    .flex_uint => "flex_uint",
                    .flex_int => "flex_int",
                    .uint8 => "uint8",
                    .uint16 => "uint16",
                    .uint32 => "uint32",
                    .uint64 => "uint64",
                    .int8 => "int8",
                    .int16 => "int16",
                    .int32 => "int32",
                    .int64 => "int64",
                    .float16 => "float16",
                    .float32 => "float32",
                    .float64 => "float64",
                };

                if (ty_name) |t| {
                    const buf = allocator0.alloc(value.Symbol, 1) catch return IonError.OutOfMemory;
                    buf[0] = value.makeSymbolId(null, t);
                    bufs.append(allocator0, buf) catch return IonError.OutOfMemory;
                    return buf;
                }

                if (p.ty == .macro_shape) {
                    const shape = p.shape orelse return IonError.InvalidIon;
                    if (shape.module) |m| {
                        const buf = allocator0.alloc(value.Symbol, 2) catch return IonError.OutOfMemory;
                        buf[0] = value.makeSymbolId(null, m);
                        buf[1] = value.makeSymbolId(null, shape.name);
                        bufs.append(allocator0, buf) catch return IonError.OutOfMemory;
                        return buf;
                    }
                    const buf = allocator0.alloc(value.Symbol, 1) catch return IonError.OutOfMemory;
                    buf[0] = value.makeSymbolId(null, shape.name);
                    bufs.append(allocator0, buf) catch return IonError.OutOfMemory;
                    return buf;
                }

                return &.{};
            }
        }.run;

        var macro_defs = std.ArrayListUnmanaged(value.Element){};
        defer macro_defs.deinit(allocator);

        for (tab.macros) |m| {
            const param_items = allocator.alloc(value.Element, m.params.len) catch return IonError.OutOfMemory;
            for (m.params, 0..) |p, i| {
                const pn = try mkParamName(allocator, &param_name_bufs, p.name, p.card);
                const anns = try mkParamAnnotations(allocator, &ann_bufs, p);
                param_items[i] = .{
                    .annotations = @constCast(anns),
                    .value = .{ .symbol = value.makeSymbolId(null, pn) },
                };
            }
            const params_elem: value.Element = .{ .annotations = &.{}, .value = .{ .sexp = param_items } };

            const macro_items = allocator.alloc(value.Element, 3 + m.body.len) catch return IonError.OutOfMemory;
            macro_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = value.makeSymbolId(null, "macro") } };
            macro_items[1] = if (m.name) |nm|
                .{ .annotations = &.{}, .value = .{ .symbol = value.makeSymbolId(null, nm) } }
            else
                .{ .annotations = &.{}, .value = .{ .null = .null } };
            macro_items[2] = params_elem;
            for (m.body, 0..) |b, i| macro_items[3 + i] = b;

            macro_allocs.append(allocator, .{ .macro_items = macro_items, .param_items = param_items }) catch return IonError.OutOfMemory;
            macro_defs.append(allocator, .{ .annotations = &.{}, .value = .{ .sexp = macro_items } }) catch return IonError.OutOfMemory;
        }

        const clause_items = allocator.alloc(value.Element, 2 + macro_defs.items.len) catch return IonError.OutOfMemory;
        macro_table_clause_items = clause_items;
        clause_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = value.makeSymbolId(null, "macro_table") } };
        clause_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = sym_underscore } };
        for (macro_defs.items, 0..) |d, i| clause_items[2 + i] = d;

        break :blk value.Element{ .annotations = &.{}, .value = .{ .sexp = clause_items } };
    } else null;

    const clause_items = allocator.alloc(value.Element, 2 + user_symbol_texts.len) catch return IonError.OutOfMemory;
    defer allocator.free(clause_items);
    clause_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = sym_symbols } };
    clause_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = sym_underscore } };
    for (user_symbol_texts, 0..) |t, i| {
        clause_items[2 + i] = .{ .annotations = &.{}, .value = .{ .string = t } };
    }
    const clause_elem: value.Element = .{ .annotations = &.{}, .value = .{ .sexp = clause_items } };

    const clause_count: usize = if (macro_table_clause != null) 2 else 1;
    const module_items = allocator.alloc(value.Element, 2 + clause_count) catch return IonError.OutOfMemory;
    defer allocator.free(module_items);
    module_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = sym_module } };
    module_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = sym_underscore } };
    var idx: usize = 2;
    if (macro_table_clause) |mc| {
        module_items[idx] = mc;
        idx += 1;
    }
    module_items[idx] = clause_elem;

    const elem: value.Element = .{ .annotations = @constCast(ann[0..]), .value = .{ .sexp = module_items } };

    // Use system symbol addresses (0xEE) when possible. This keeps the output compact, but note
    // that the Ion 1.1 system symbol table differs between `ion-tests` and ion-rust (see
    // `Options.sys_symtab11_variant` / `symtab.systemSymtab11Variant()` / `ION_ZIG_SYSTEM_SYMTAB11`).
    var opts = options;
    opts.symbol_encoding = .addresses;
    try writeElement(allocator, out, opts, elem);
}

pub fn writeSetSymbolsDirectiveText(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), texts: []const []const u8) IonError!void {
    return writeSetSymbolsDirectiveTextWithOptions(allocator, out, texts, .{});
}

pub fn writeSetSymbolsDirectiveTextWithOptions(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    texts: []const []const u8,
    options: Options,
) IonError!void {
    return writeSymbolsDirectiveTextWithOptions(allocator, out, 19, texts, options);
}

pub fn writeAddSymbolsDirectiveText(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), texts: []const []const u8) IonError!void {
    return writeAddSymbolsDirectiveTextWithOptions(allocator, out, texts, .{});
}

pub fn writeAddSymbolsDirectiveTextWithOptions(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    texts: []const []const u8,
    options: Options,
) IonError!void {
    return writeSymbolsDirectiveTextWithOptions(allocator, out, 20, texts, options);
}

pub fn writeUseDirective(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), key: []const u8, version: ?u32) IonError!void {
    return writeUseDirectiveWithOptions(allocator, out, key, version, .{});
}

pub fn writeUseDirectiveWithOptions(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    key: []const u8,
    version: ?u32,
    options: Options,
) IonError!void {
    // (use <catalog_key> [<version>]) as a length-prefixed system macro invocation (addr 23).
    const params = [_]ion.macro.Param{
        .{ .ty = .tagged, .card = .one, .name = "key", .shape = null },
        .{ .ty = .tagged, .card = .zero_or_one, .name = "version", .shape = null },
    };

    const key_elem: value.Element = .{ .annotations = &.{}, .value = .{ .string = key } };
    const key_list = [_]value.Element{key_elem};

    var ver_list: [1]value.Element = undefined;
    const ver_slice: []const value.Element = if (version) |v| blk: {
        ver_list[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = @intCast(v) } } };
        break :blk ver_list[0..1];
    } else &.{};

    const args_by_param = [_][]const value.Element{ key_list[0..], ver_slice };
    try writeSystemMacroInvocationLengthPrefixedWithParams(allocator, out, 23, params[0..], args_by_param[0..], options);
}

pub fn writeSetMacrosDirective(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), macro_defs: []const value.Element) IonError!void {
    return writeSetMacrosDirectiveWithOptions(allocator, out, macro_defs, .{});
}

pub fn writeSetMacrosDirectiveWithOptions(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    macro_defs: []const value.Element,
    options: Options,
) IonError!void {
    // `set_macros` uses address 21 (overloaded with `meta` in conformance). The decoder selects
    // `set_macros` when all args are macro defs.
    if (macro_defs.len != 0 and !allArgsAreMacroDefs(macro_defs)) return IonError.InvalidIon;
    try writeSystemMacroInvocationLengthPrefixedTaggedVariadicWithOptions(allocator, out, 21, macro_defs, options);
}

pub fn writeAddMacrosDirective(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), macro_defs: []const value.Element) IonError!void {
    return writeAddMacrosDirectiveWithOptions(allocator, out, macro_defs, .{});
}

pub fn writeAddMacrosDirectiveWithOptions(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    macro_defs: []const value.Element,
    options: Options,
) IonError!void {
    // (add_macros <macro_def*>) is address 22.
    if (macro_defs.len != 0 and !allArgsAreMacroDefs(macro_defs)) return IonError.InvalidIon;
    try writeSystemMacroInvocationLengthPrefixedTaggedVariadicWithOptions(allocator, out, 22, macro_defs, options);
}

fn writeElement(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8), options: Options, e: value.Element) IonError!void {
    if (e.annotations.len != 0) {
        try writeAnnotationsSequence(allocator, out, options, e.annotations);
    }
    try writeValue(allocator, out, options, e.value);
}

fn allArgsAreMacroDefs(args: []const value.Element) bool {
    for (args) |d| {
        if (d.annotations.len != 0) return false;
        if (d.value != .sexp) return false;
        const sx = d.value.sexp;
        if (sx.len == 0) return false;
        if (sx[0].value != .symbol) return false;
        const head = sx[0].value.symbol.text orelse return false;
        if (!std.mem.eql(u8, head, "macro")) return false;
    }
    return true;
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
        .list => |items| switch (options.container_encoding) {
            .delimited => try writeDelimitedList(allocator, out, options, items),
            .length_prefixed => try writeSequence(allocator, out, options, 0xB0, 0xFB, items),
        },
        .sexp => |items| switch (options.container_encoding) {
            .delimited => try writeDelimitedSexp(allocator, out, options, items),
            .length_prefixed => try writeSequence(allocator, out, options, 0xC0, 0xFC, items),
        },
        .@"struct" => |st| switch (options.container_encoding) {
            .delimited => try writeDelimitedStruct(allocator, out, options, st),
            .length_prefixed => try writeStruct(allocator, out, options, st),
        },
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
            if (systemSymtab11SidForText(options, t)) |sys_sid| {
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
            if (sid > 0 and sid <= systemSymtab11MaxId(options)) {
                if (systemSymtab11TextForSid(options, sid)) |sys_text| {
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
        if (sid > 0 and sid <= systemSymtab11MaxId(options) and sid <= 0xFF) {
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
    // Avoid emitting the reserved short-struct opcode `0xD1`. For an empty struct, we can emit a
    // zero-length short struct (`0xD0`) with an empty body, which decodes to `{}`.
    if (st.fields.len == 0) {
        try appendByte(out, allocator, 0xD0);
        return;
    }

    // For simplicity, always use FlexSym field-name mode:
    // struct-body := FlexUInt(0) then repeated (FlexSym field-name, value-expr).
    var body = std.ArrayListUnmanaged(u8){};
    defer body.deinit(allocator);

    try writeFlexUIntShift1(&body, allocator, 0);
    for (st.fields) |f| {
        try writeFlexSymSymbol(&body, allocator, options, f.name);
        try writeElement(allocator, &body, options, f.value);
    }

    // Short struct: D0..DF (len in opcode). D1 is reserved, so only use the short form when the
    // computed body length does not map to 0xD1.
    if (body.items.len <= 15 and body.items.len != 1) {
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
            if (systemSymtab11SidForText(options, t)) |sys_sid| {
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
            if (sid > 0 and sid <= systemSymtab11MaxId(options)) {
                const sys_text = systemSymtab11TextForSid(options, sid) orelse return IonError.InvalidIon;
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
    // Encode a length-prefixed system macro invocation:
    //   (:$ion::set_symbols <text*>)
    // using the `0xF5` e-expression form understood by `binary11.readMacroInvocationLengthPrefixed`.
    //
    // This makes the output more spec-aligned than the older conformance-specific `EF 13 <presence>`
    // encoding.
    //
    // In the conformance module model, address 19 is interpreted as `set_symbols` when all args are
    // unannotated text values.
    //
    // Encoding:
    //   F5 <flexuint addr=19> <flexuint args_len> <args_bytes...>
    // where args_bytes encodes bindings for a single variadic tagged param (zero_or_many):
    //   <bitmap:1 byte> [ <value-expr> | <tagged-group> ]
    // and tagged-group is:
    //   <flexuint total_len> <payload bytes...>
    // with payload being a concatenation of tagged value expressions.
    // Build the tagged arg list as a slice of elements.
    var elems = std.ArrayListUnmanaged(value.Element){};
    defer elems.deinit(allocator);
    for (user_texts) |t| {
        elems.append(allocator, .{ .annotations = &.{}, .value = .{ .string = t } }) catch return IonError.OutOfMemory;
    }

    try writeSystemMacroInvocationLengthPrefixedTaggedVariadic(allocator, out, 19, elems.items);
}

fn writeSymbolsDirectiveTextWithOptions(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    addr: u8,
    texts: []const []const u8,
    options: Options,
) IonError!void {
    var elems = std.ArrayListUnmanaged(value.Element){};
    defer elems.deinit(allocator);
    for (texts) |t| {
        elems.append(allocator, .{ .annotations = &.{}, .value = .{ .string = t } }) catch return IonError.OutOfMemory;
    }
    try writeSystemMacroInvocationLengthPrefixedTaggedVariadicWithOptions(allocator, out, addr, elems.items, options);
}

pub fn writeSystemMacroInvocationLengthPrefixedTaggedVariadic(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    addr: u8,
    args: []const value.Element,
) IonError!void {
    return writeSystemMacroInvocationLengthPrefixedTaggedVariadicWithOptions(allocator, out, addr, args, .{});
}

pub fn writeSystemMacroInvocationLengthPrefixedTaggedVariadicWithOptions(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    addr: u8,
    args: []const value.Element,
    options: Options,
) IonError!void {
    // Writes a length-prefixed e-expression (0xF5) for a system macro at `addr` whose signature is:
    //   (<name> <tagged expr*>)
    //
    // This matches the encoding expected by `binary11.readLengthPrefixedSystemValuesArgs` and the
    // `expandSystemMacroLengthPrefixed` cases that use a single variadic tagged parameter.
    var arg_bytes = std.ArrayListUnmanaged(u8){};
    defer arg_bytes.deinit(allocator);
    try encodeSingleVariadicTaggedArgBindings(allocator, &arg_bytes, options, args);

    try appendByte(out, allocator, 0xF5);
    try writeFlexUIntShift1(out, allocator, addr);
    try writeFlexUIntShift1(out, allocator, arg_bytes.items.len);
    try appendSlice(out, allocator, arg_bytes.items);
}

pub fn writeSystemMacroInvocationLengthPrefixedWithParams(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    addr: u8,
    params: []const ion.macro.Param,
    args_by_param: []const []const value.Element,
    options: Options,
) IonError!void {
    return writeMacroInvocationLengthPrefixedWithParams(allocator, out, addr, params, args_by_param, options);
}

pub fn writeSystemMacroInvocationQualifiedWithParams(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    addr: u8,
    params: []const ion.macro.Param,
    args_by_param: []const []const value.Element,
    options: Options,
) IonError!void {
    // Qualified system macro invocation (0xEF <addr>) using the spec signature-driven argument
    // binding encoding (bitmap + required args + arg groups).
    //
    // ion-rust's Ion 1.1 binary writer uses this encoding for qualified system macros. The Zig
    // Ion 1.1 binary decoder only selects this decoding mode when `sys_symtab11_variant` is
    // forced/inferred as `ion_rust` so conformance (which historically uses different encodings)
    // remains green.
    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, addr);
    try encodeArgBindings(allocator, out, params, args_by_param, options);
}

pub fn writeSystemMacroInvocationQualifiedTaggedGroup(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    addr: u8,
    args: []const value.Element,
    options: Options,
) IonError!void {
    // Qualified system macro invocation (0xEF <addr>) using the conformance-style argument
    // encodings that `binary11.readSystemMacroInvocationAt` expects for many system macros.
    //
    // For the common `(<name> <expr*>)` case, conformance uses a 1-byte presence code:
    //   0 => empty / elided group
    //   1 => single tagged value
    //   2 => expression group of tagged values
    //
    // This is distinct from the length-prefixed `0xF5` form; both are supported by the decoder.
    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, addr);

    if (args.len == 0) {
        try appendByte(out, allocator, 0x00);
        return;
    }
    if (args.len == 1) {
        try appendByte(out, allocator, 0x01);
        try writeElement(allocator, out, options, args[0]);
        return;
    }

    try appendByte(out, allocator, 0x02);
    switch (options.arg_group_encoding) {
        .length_prefixed => {
            var payload = std.ArrayListUnmanaged(u8){};
            defer payload.deinit(allocator);
            for (args) |e| try writeElement(allocator, &payload, options, e);
            try writeFlexUIntShift1(out, allocator, payload.items.len);
            try appendSlice(out, allocator, payload.items);
        },
        .delimited => {
            try writeFlexUIntShift1(out, allocator, 0);
            for (args) |e| try writeElement(allocator, out, options, e);
            try appendByte(out, allocator, 0xF0);
        },
    }
}

pub fn writeSystemMacroInvocationQualifiedValues(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    args: []const value.Element,
    options: Options,
) IonError!void {
    // (values <expr*>): system macro address 1.
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 1, args, options);
}

pub fn writeSystemMacroInvocationQualifiedSum(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    a: value.Element,
    b: value.Element,
    options: Options,
) IonError!void {
    // (sum <a> <b>): system macro address 7.
    // Conformance binary encoding is `EF 07` followed by two *tagged* values.
    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, 0x07);
    try writeElement(allocator, out, options, a);
    try writeElement(allocator, out, options, b);
}

pub fn writeSystemMacroInvocationQualifiedDefault(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    a: []const value.Element,
    b: []const value.Element,
    options: Options,
) IonError!void {
    // (default <a> <b*>): system macro address 2.
    //
    // Conformance binary encoding begins with a 1-byte packed presence code:
    //   bits 0..1 => first arg (a)
    //   bits 2..3 => second arg (b)
    //   00 absent, 01 single tagged value, 10 expression group, 11 invalid.
    const code = struct {
        fn groupLen(n: usize) u2 {
            return if (n == 0) 0b00 else if (n == 1) 0b01 else 0b10;
        }

        fn emit(d: u2, dst: *std.ArrayListUnmanaged(u8), alloc: std.mem.Allocator, opts: Options, vals: []const value.Element) IonError!void {
            switch (d) {
                0b00 => {},
                0b01 => try writeElement(alloc, dst, opts, vals[0]),
                0b10 => {
                    var payload = std.ArrayListUnmanaged(u8){};
                    defer payload.deinit(alloc);
                    for (vals) |e| try writeElement(alloc, &payload, opts, e);
                    try writeFlexUIntShift1(dst, alloc, payload.items.len);
                    try appendSlice(dst, alloc, payload.items);
                },
                else => return IonError.InvalidIon,
            }
        }
    };

    const a_code: u2 = code.groupLen(a.len);
    const b_code: u2 = code.groupLen(b.len);
    const p: u8 = @as(u8, a_code) | (@as(u8, b_code) << 2);

    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, 0x02);
    try appendByte(out, allocator, p);
    try code.emit(a_code, out, allocator, options, a);
    try code.emit(b_code, out, allocator, options, b);
}

pub fn writeSystemMacroInvocationQualifiedUse(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    key: []const u8,
    version: ?u32,
    options: Options,
) IonError!void {
    // (use <catalog_key> [<version>]): system macro address 23.
    //
    // Conformance binary encoding begins with a 1-byte presence code for the optional version:
    //   0 => absent (defaults to 1)
    //   1 => tagged integer value
    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, 23);
    try appendByte(out, allocator, if (version == null) 0x00 else 0x01);

    const key_elem: value.Element = .{ .annotations = &.{}, .value = .{ .string = key } };
    try writeElement(allocator, out, options, key_elem);

    if (version) |v| {
        const ver_elem: value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = @intCast(v) } } };
        try writeElement(allocator, out, options, ver_elem);
    }
}

pub fn writeSystemMacroInvocationQualifiedAnnotate(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    annotations: []const value.Element,
    val: value.Element,
    options: Options,
) IonError!void {
    // (annotate <annotations-expr> <value-expr>): system macro address 8.
    //
    // Conformance binary encoding begins with a 1-byte presence code for the annotations arg:
    //   0 => empty annotations group
    //   1 => single tagged value (one annotation)
    //   2 => expression group of tagged values (multiple annotations)
    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, 0x08);

    if (annotations.len == 0) {
        try appendByte(out, allocator, 0x00);
    } else if (annotations.len == 1) {
        try appendByte(out, allocator, 0x01);
        try writeElement(allocator, out, options, annotations[0]);
    } else {
        try appendByte(out, allocator, 0x02);
        var payload = std.ArrayListUnmanaged(u8){};
        defer payload.deinit(allocator);
        for (annotations) |e| try writeElement(allocator, &payload, options, e);
        try writeFlexUIntShift1(out, allocator, payload.items.len);
        try appendSlice(out, allocator, payload.items);
    }

    try writeElement(allocator, out, options, val);
}

pub fn writeSystemMacroInvocationQualifiedMakeDecimal(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    coefficient: value.Element,
    exponent: value.Element,
    options: Options,
) IonError!void {
    // (make_decimal <coefficient> <exponent>): system macro address 11.
    //
    // Conformance binary encoding is `EF 0B` followed by two *tagged* values back-to-back.
    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, 0x0B);
    try writeElement(allocator, out, options, coefficient);
    try writeElement(allocator, out, options, exponent);
}

pub fn writeSystemMacroInvocationQualifiedMakeTimestamp(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    year: value.Element,
    month: ?value.Element,
    day: ?value.Element,
    hour: ?value.Element,
    minute: ?value.Element,
    seconds: ?value.Element,
    offset: ?value.Element,
    options: Options,
) IonError!void {
    // (make_timestamp <year> [<month> [<day> [<hour> <minute> [<seconds> [<offset>]]]]]):
    // system macro address 12.
    //
    // Conformance binary encoding uses a 2-byte (little-endian) packed presence code for optional
    // args, then emits `<year>` as a tagged value, followed by each present optional arg as a
    // tagged value. The decoder also accepts optional args as a 1-element expression group, but
    // this writer uses the simple single-value form.
    if (effectiveSystemSymtab11Variant(options) == .ion_rust) {
        const p = [_]ion.macro.Param{
            .{ .ty = .tagged, .card = .one, .name = "year", .shape = null },
            .{ .ty = .tagged, .card = .zero_or_one, .name = "month", .shape = null },
            .{ .ty = .tagged, .card = .zero_or_one, .name = "day", .shape = null },
            .{ .ty = .tagged, .card = .zero_or_one, .name = "hour", .shape = null },
            .{ .ty = .tagged, .card = .zero_or_one, .name = "minute", .shape = null },
            .{ .ty = .tagged, .card = .zero_or_one, .name = "second", .shape = null },
            .{ .ty = .tagged, .card = .zero_or_one, .name = "offset_minutes", .shape = null },
        };
        const year_list = [_]value.Element{year};
        var month_buf: [1]value.Element = undefined;
        var day_buf: [1]value.Element = undefined;
        var hour_buf: [1]value.Element = undefined;
        var minute_buf: [1]value.Element = undefined;
        var second_buf: [1]value.Element = undefined;
        var offset_buf: [1]value.Element = undefined;
        const optList = struct {
            fn run(buf: *[1]value.Element, v: ?value.Element) []const value.Element {
                if (v) |vv| {
                    buf[0] = vv;
                    return buf[0..1];
                }
                return &.{};
            }
        }.run;
        const args_by_param = [_][]const value.Element{
            year_list[0..],
            optList(&month_buf, month),
            optList(&day_buf, day),
            optList(&hour_buf, hour),
            optList(&minute_buf, minute),
            optList(&second_buf, seconds),
            optList(&offset_buf, offset),
        };
        return writeSystemMacroInvocationQualifiedWithParams(allocator, out, 12, p[0..], args_by_param[0..], options);
    }

    const code = struct {
        fn set(p: *u16, idx: u4, present: bool) void {
            if (!present) return;
            p.* |= (@as(u16, 0b01) << @intCast(@as(u5, idx) * 2));
        }
    };

    var presence: u16 = 0;
    code.set(&presence, 0, month != null);
    code.set(&presence, 1, day != null);
    code.set(&presence, 2, hour != null);
    code.set(&presence, 3, minute != null);
    code.set(&presence, 4, seconds != null);
    code.set(&presence, 5, offset != null);

    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, 0x0C);
    var pres_bytes: [2]u8 = undefined;
    std.mem.writeInt(u16, &pres_bytes, presence, .little);
    try appendSlice(out, allocator, &pres_bytes);

    try writeElement(allocator, out, options, year);
    if (month) |v| try writeElement(allocator, out, options, v);
    if (day) |v| try writeElement(allocator, out, options, v);
    if (hour) |v| try writeElement(allocator, out, options, v);
    if (minute) |v| try writeElement(allocator, out, options, v);
    if (seconds) |v| try writeElement(allocator, out, options, v);
    if (offset) |v| try writeElement(allocator, out, options, v);
}

pub fn writeSystemMacroInvocationQualifiedRepeat(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    count: value.Element,
    exprs: []const value.Element,
    options: Options,
) IonError!void {
    // (repeat <n> <expr>): system macro address 4.
    //
    // Conformance binary encoding begins with a 1-byte presence code for the repetition count,
    // then encodes the repeated expression. The decoder accepts both:
    // - a single tagged value, OR
    // - a presence code (0/1/2) followed by a tagged value or expression group.
    //
    if (effectiveSystemSymtab11Variant(options) == .ion_rust) {
        const p = [_]ion.macro.Param{
            .{ .ty = .tagged, .card = .one, .name = "n", .shape = null },
            .{ .ty = .tagged, .card = .zero_or_many, .name = "expr", .shape = null },
        };
        const count_list = [_]value.Element{count};
        const args_by_param = [_][]const value.Element{ count_list[0..], exprs };
        return writeSystemMacroInvocationQualifiedWithParams(allocator, out, 4, p[0..], args_by_param[0..], options);
    }

    // Conformance encoding: explicit presence codes.
    // This writer always uses the explicit 1-byte presence code for the repeated expression to
    // avoid ambiguity when the first byte of the expression could be 0, 1, or 2.
    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, 0x04);

    // Count: always encode as a single tagged value.
    try appendByte(out, allocator, 0x01);
    try writeElement(allocator, out, options, count);

    // Repeated expression(s): encode as presence + either single tagged value or tagged group.
    if (exprs.len == 0) {
        try appendByte(out, allocator, 0x00);
        return;
    }
    if (exprs.len == 1) {
        try appendByte(out, allocator, 0x01);
        try writeElement(allocator, out, options, exprs[0]);
        return;
    }

    try appendByte(out, allocator, 0x02);
    var payload = std.ArrayListUnmanaged(u8){};
    defer payload.deinit(allocator);
    for (exprs) |e| try writeElement(allocator, &payload, options, e);
    try writeFlexUIntShift1(out, allocator, payload.items.len);
    try appendSlice(out, allocator, payload.items);
}

pub fn writeSystemMacroInvocationQualifiedDelta(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    deltas: []const value.Element,
    options: Options,
) IonError!void {
    // (delta <deltas*>): system macro address 6.
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 0x06, deltas, options);
}

pub fn writeSystemMacroInvocationQualifiedFlatten(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    sequences: []const value.Element,
    options: Options,
) IonError!void {
    // (flatten <sequence*>): conformance uses system macro address 19 (overloaded with set_symbols).
    //
    // If all args are unannotated text values, the decoder will treat address 19 as `set_symbols`.
    //
    // Note: ion-rust's system macro table uses address 5 for `flatten` and address 19 for
    // `set_symbols`. Rejecting the conformance encoding here prevents the writer from emitting
    // ambiguous bytes when `Options.sys_symtab11_variant == .ion_rust`.
    if (effectiveSystemSymtab11Variant(options) == .ion_rust) return IonError.InvalidIon;
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 19, sequences, options);
}

pub fn writeSystemMacroInvocationQualifiedFlattenCanonical(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    sequences: []const value.Element,
    options: Options,
) IonError!void {
    // Canonical (ion-rust): (flatten <sequence*>): system macro address 5.
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 5, sequences, options);
}

pub fn writeSystemMacroInvocationQualifiedFlattenByVariant(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    sequences: []const value.Element,
    options: Options,
) IonError!void {
    return switch (effectiveSystemSymtab11Variant(options)) {
        .ion_tests => writeSystemMacroInvocationQualifiedFlatten(allocator, out, sequences, options),
        .ion_rust => writeSystemMacroInvocationQualifiedFlattenCanonical(allocator, out, sequences, options),
    };
}

pub fn writeSystemMacroInvocationQualifiedSetSymbolsDirectiveText(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    texts: []const []const u8,
    options: Options,
) IonError!void {
    // (set_symbols <text*>): system macro address 19 (overloaded with flatten in conformance).
    //
    // The decoder distinguishes set_symbols vs flatten by argument shape: if all args are
    // unannotated text values (string or symbol-with-text), it treats address 19 as set_symbols.
    var elems = std.ArrayListUnmanaged(value.Element){};
    defer elems.deinit(allocator);
    for (texts) |t| {
        elems.append(allocator, .{ .annotations = &.{}, .value = .{ .string = t } }) catch return IonError.OutOfMemory;
    }
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 19, elems.items, options);
}

pub fn writeSystemMacroInvocationQualifiedAddSymbolsDirectiveText(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    texts: []const []const u8,
    options: Options,
) IonError!void {
    // (add_symbols <text*>): system macro address 20.
    var elems = std.ArrayListUnmanaged(value.Element){};
    defer elems.deinit(allocator);
    for (texts) |t| {
        elems.append(allocator, .{ .annotations = &.{}, .value = .{ .string = t } }) catch return IonError.OutOfMemory;
    }
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 20, elems.items, options);
}

pub fn writeSystemMacroInvocationQualifiedSetMacrosDirective(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    macro_defs: []const value.Element,
    options: Options,
) IonError!void {
    // Conformance uses system macro address 21 for both `meta` and `set_macros`. The decoder
    // selects `set_macros` when all args are macro defs.
    if (macro_defs.len != 0 and !allArgsAreMacroDefs(macro_defs)) return IonError.InvalidIon;
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 21, macro_defs, options);
}

pub fn writeSystemMacroInvocationQualifiedAddMacrosDirective(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    macro_defs: []const value.Element,
    options: Options,
) IonError!void {
    // (add_macros <macro_def*>): system macro address 22.
    if (macro_defs.len != 0 and !allArgsAreMacroDefs(macro_defs)) return IonError.InvalidIon;
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 22, macro_defs, options);
}

pub fn writeSystemMacroInvocationQualifiedMakeString(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    parts: []const value.Element,
    options: Options,
) IonError!void {
    // (make_string <text*>): system macro address 9.
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 0x09, parts, options);
}

pub fn writeSystemMacroInvocationQualifiedMakeSymbol(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    parts: []const value.Element,
    options: Options,
) IonError!void {
    // (make_symbol <text*>): system macro address 10.
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 0x0A, parts, options);
}

pub fn writeSystemMacroInvocationQualifiedMakeBlob(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    parts: []const value.Element,
    options: Options,
) IonError!void {
    // (make_blob <lob*>): system macro address 13.
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 0x0D, parts, options);
}

pub fn writeSystemMacroInvocationQualifiedMakeList(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    sequences: []const value.Element,
    options: Options,
) IonError!void {
    // (make_list <seq*>): system macro address 14.
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 0x0E, sequences, options);
}

pub fn writeSystemMacroInvocationQualifiedMakeSexp(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    sequences: []const value.Element,
    options: Options,
) IonError!void {
    // (make_sexp <seq*>): system macro address 15.
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 0x0F, sequences, options);
}

pub fn writeSystemMacroInvocationQualifiedMakeStruct(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    structs: []const value.Element,
    options: Options,
) IonError!void {
    // (make_struct <struct-or-field*>): system macro address 17.
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 0x11, structs, options);
}

pub fn writeSystemMacroInvocationQualifiedParseIon(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    bytes: value.Element,
    options: Options,
) IonError!void {
    // (parse_ion <bytes>): conformance uses system macro address 16 (overloaded with make_field).
    //
    // Note: address 16 is overloaded with make_field. The decoder selects parse_ion when the
    // first argument is a string/clob/blob value.
    //
    // Note: ion-rust's system macro table uses address 18 for `parse_ion` and address 16 for
    // `make_field`. Rejecting the conformance encoding here prevents the writer from emitting
    // ambiguous bytes when `Options.sys_symtab11_variant == .ion_rust`.
    if (effectiveSystemSymtab11Variant(options) == .ion_rust) return IonError.InvalidIon;
    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, 0x10);
    try writeElement(allocator, out, options, bytes);
}

pub fn writeSystemMacroInvocationQualifiedParseIonCanonical(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    parts: []const value.Element,
    options: Options,
) IonError!void {
    // Canonical (ion-rust): (parse_ion <data*>): system macro address 18.
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 18, parts, options);
}

pub fn writeSystemMacroInvocationQualifiedParseIonByVariant(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    parts: []const value.Element,
    options: Options,
) IonError!void {
    return switch (effectiveSystemSymtab11Variant(options)) {
        .ion_tests => blk: {
            if (parts.len != 1) return IonError.InvalidIon;
            break :blk writeSystemMacroInvocationQualifiedParseIon(allocator, out, parts[0], options);
        },
        .ion_rust => writeSystemMacroInvocationQualifiedParseIonCanonical(allocator, out, parts, options),
    };
}

pub fn writeSystemMacroInvocationQualifiedMakeField(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    name: value.Element,
    val: value.Element,
    options: Options,
) IonError!void {
    // (make_field <name> <value>): system macro address 16.
    //
    // Note: address 16 is overloaded with parse_ion. The decoder selects make_field when the
    // first argument is NOT a string/clob/blob; use a symbol for deterministic encoding.
    if (name.value != .symbol) return IonError.InvalidIon;
    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, 0x10);
    try writeElement(allocator, out, options, name);
    try writeElement(allocator, out, options, val);
}

pub fn writeSystemMacroInvocationQualifiedNone(allocator: std.mem.Allocator, out: *std.ArrayListUnmanaged(u8)) IonError!void {
    // (none): system macro address 0.
    //
    // Decoder expands address 0 without consuming any argument bytes.
    try appendByte(out, allocator, 0xEF);
    try appendByte(out, allocator, 0x00);
}

pub fn writeSystemMacroInvocationQualifiedMeta(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    args: []const value.Element,
    options: Options,
) IonError!void {
    // (meta <expr*>): conformance uses system macro address 21 (overloaded with set_macros).
    //
    // The decoder disambiguates address 21: if all args are macro defs, it treats it as set_macros;
    // otherwise it treats it as meta. This writer does not attempt to validate the meta payload.
    //
    // Note: ion-rust's system macro table uses address 3 for `meta` and address 21 for
    // `set_macros`. Rejecting the conformance encoding here prevents the writer from emitting
    // ambiguous bytes when `Options.sys_symtab11_variant == .ion_rust`.
    if (effectiveSystemSymtab11Variant(options) == .ion_rust) return IonError.InvalidIon;
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 21, args, options);
}

pub fn writeSystemMacroInvocationQualifiedMetaCanonical(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    args: []const value.Element,
    options: Options,
) IonError!void {
    // Canonical (ion-rust): (meta <expr*>): system macro address 3.
    return writeSystemMacroInvocationQualifiedTaggedGroup(allocator, out, 3, args, options);
}

pub fn writeSystemMacroInvocationQualifiedMetaByVariant(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    args: []const value.Element,
    options: Options,
) IonError!void {
    return switch (effectiveSystemSymtab11Variant(options)) {
        .ion_tests => writeSystemMacroInvocationQualifiedMeta(allocator, out, args, options),
        .ion_rust => writeSystemMacroInvocationQualifiedMetaCanonical(allocator, out, args, options),
    };
}

pub fn writeMacroInvocationLengthPrefixedWithParams(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    addr: usize,
    params: []const ion.macro.Param,
    args_by_param: []const []const value.Element,
    options: Options,
) IonError!void {
    // Low-level helper for emitting length-prefixed e-expressions (0xF5) using the same
    // signature-driven argument binding encoding that `binary11.readLengthPrefixedArgBindings`
    // expects.
    if (params.len != args_by_param.len) return IonError.InvalidIon;

    var arg_bytes = std.ArrayListUnmanaged(u8){};
    defer arg_bytes.deinit(allocator);
    try encodeArgBindings(allocator, &arg_bytes, params, args_by_param, options);

    try appendByte(out, allocator, 0xF5);
    try writeFlexUIntShift1(out, allocator, addr);
    try writeFlexUIntShift1(out, allocator, arg_bytes.items.len);
    try appendSlice(out, allocator, arg_bytes.items);
}

pub fn writeUserMacroInvocationAtAddressWithParams(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    addr: usize,
    params: []const ion.macro.Param,
    args_by_param: []const []const value.Element,
    options: Options,
) IonError!void {
    // Writes an unqualified (non-length-prefixed) e-expression whose address is encoded directly
    // in the opcode bytes and whose arguments are encoded using the same signature-driven encoding
    // as the length-prefixed form, just without the outer args length.
    //
    // This corresponds to `binary11.readUserMacroInvocationAt` for user-defined macros.
    try writeEExpAddress(out, allocator, addr);
    try encodeArgBindings(allocator, out, params, args_by_param, options);
}

pub fn writeUserMacroInvocationUnqualifiedByNameWithParams(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    tab: *const ion.macro.MacroTable,
    name: []const u8,
    args_by_param: []const []const value.Element,
    options: Options,
) IonError!void {
    const addr = tab.addressForName(name) orelse return IonError.Unsupported;
    const m = tab.macroForAddress(addr) orelse return IonError.Unsupported;
    try writeUserMacroInvocationAtAddressWithParams(allocator, out, addr, m.params, args_by_param, options);
}

pub fn writeUserMacroInvocationLengthPrefixedByNameWithParams(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    tab: *const ion.macro.MacroTable,
    name: []const u8,
    args_by_param: []const []const value.Element,
    options: Options,
) IonError!void {
    const addr = tab.addressForName(name) orelse return IonError.Unsupported;
    const m = tab.macroForAddress(addr) orelse return IonError.Unsupported;
    try writeMacroInvocationLengthPrefixedWithParams(allocator, out, addr, m.params, args_by_param, options);
}

fn encodeSingleVariadicTaggedArgBindings(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    options: Options,
    args: []const value.Element,
) IonError!void {
    // Single variadic param => 1 bitmap byte (low 2 bits are grouping).
    if (args.len == 0) {
        try appendByte(out, allocator, 0x00); // grouping 00 (absent)
        return;
    }
    if (args.len == 1) {
        try appendByte(out, allocator, 0x01); // grouping 01 (single)
        try writeElement(allocator, out, options, args[0]);
        return;
    }

    try appendByte(out, allocator, 0x02); // grouping 10 (group)
    switch (options.arg_group_encoding) {
        .length_prefixed => {
            var payload = std.ArrayListUnmanaged(u8){};
            defer payload.deinit(allocator);
            for (args) |e| try writeElement(allocator, &payload, options, e);
            try writeFlexUIntShift1(out, allocator, payload.items.len);
            try appendSlice(out, allocator, payload.items);
        },
        .delimited => {
            try writeFlexUIntShift1(out, allocator, 0);
            for (args) |e| try writeElement(allocator, out, options, e);
            try appendByte(out, allocator, 0xF0);
        },
    }
}

fn bitmapSizeInBytesForParams(params: []const ion.macro.Param) usize {
    const bits_per_param: usize = 2;
    const bits_per_byte: usize = 8;
    var variadic: usize = 0;
    for (params) |p| {
        if (p.card != .one) variadic += 1;
    }
    return ((variadic * bits_per_param) + 7) / bits_per_byte;
}

fn encodeArgBindings(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    params: []const ion.macro.Param,
    args_by_param: []const []const value.Element,
    options: Options,
) IonError!void {
    return encodeLengthPrefixedArgBindings(allocator, out, params, args_by_param, options);
}

fn writeEExpAddress(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, addr: usize) IonError!void {
    // Match the address encoding forms that `binary11.Decoder.readValueExpr` supports:
    // - 6-bit: opcode is the address (0x00..0x3F)
    // - 12-bit: 0x40..0x4F + fixed byte, bias 64
    // - 20-bit: 0x50..0x5F + fixed u16, bias 4160
    if (addr <= 0x3F) {
        try appendByte(out, allocator, @intCast(addr));
        return;
    }
    if (addr >= 64 and addr <= 4159) {
        const x: usize = addr - 64;
        const nibble: u8 = @intCast((x >> 8) & 0x0F);
        const fixed: u8 = @intCast(x & 0xFF);
        try appendByte(out, allocator, 0x40 | nibble);
        try appendByte(out, allocator, fixed);
        return;
    }
    if (addr >= 4160 and addr <= 1_052_735) {
        const y: usize = addr - 4160;
        const nibble: u8 = @intCast((y >> 16) & 0x0F);
        const fixed_u16: u16 = @intCast(y & 0xFFFF);
        try appendByte(out, allocator, 0x50 | nibble);
        var buf: [2]u8 = undefined;
        std.mem.writeInt(u16, &buf, fixed_u16, .little);
        try appendSlice(out, allocator, &buf);
        return;
    }
    return IonError.Unsupported;
}

fn encodeLengthPrefixedArgBindingsTagged(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    params: []const ion.macro.Param,
    args_by_param: []const []const value.Element,
    options: Options,
) IonError!void {
    const bitmap_len = bitmapSizeInBytesForParams(params);
    var bitmap = std.ArrayListUnmanaged(u8){};
    defer bitmap.deinit(allocator);
    bitmap.resize(allocator, bitmap_len) catch return IonError.OutOfMemory;
    @memset(bitmap.items, 0);

    var variadic_idx: usize = 0;
    for (params, 0..) |p, idx| {
        if (p.ty != .tagged) return IonError.Unsupported;
        if (p.card == .one) {
            if (args_by_param[idx].len != 1) return IonError.InvalidIon;
            continue;
        }

        const args = args_by_param[idx];
        const grouping: u2 = if (args.len == 0) 0b00 else if (args.len == 1) 0b01 else 0b10;
        if (grouping == 0b00 and p.card == .one_or_many) return IonError.InvalidIon;
        if (grouping == 0b10 and p.card == .zero_or_one) return IonError.InvalidIon;

        const bit: usize = variadic_idx * 2;
        const byte_idx: usize = bit / 8;
        const bit_in_byte: u3 = @intCast(bit % 8);
        if (byte_idx >= bitmap.items.len) return IonError.InvalidIon;
        bitmap.items[byte_idx] |= (@as(u8, grouping) << bit_in_byte);
        variadic_idx += 1;
    }
    try appendSlice(out, allocator, bitmap.items);

    // Emit argument payloads in parameter order.
    variadic_idx = 0;
    for (params, 0..) |p, idx| {
        const args = args_by_param[idx];

        if (p.card == .one) {
            try writeElement(allocator, out, options, args[0]);
            continue;
        }

        const grouping: u2 = if (args.len == 0) 0b00 else if (args.len == 1) 0b01 else 0b10;
        switch (grouping) {
            0b00 => {},
            0b01 => try writeElement(allocator, out, options, args[0]),
            0b10 => {
                var payload = std.ArrayListUnmanaged(u8){};
                defer payload.deinit(allocator);
                for (args) |e| try writeElement(allocator, &payload, options, e);
                try writeFlexUIntShift1(out, allocator, payload.items.len);
                try appendSlice(out, allocator, payload.items);
            },
            else => return IonError.InvalidIon,
        }
        variadic_idx += 1;
    }
}

fn encodeLengthPrefixedArgBindings(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    params: []const ion.macro.Param,
    args_by_param: []const []const value.Element,
    options: Options,
) IonError!void {
    const bitmap_len = bitmapSizeInBytesForParams(params);
    var bitmap = std.ArrayListUnmanaged(u8){};
    defer bitmap.deinit(allocator);
    bitmap.resize(allocator, bitmap_len) catch return IonError.OutOfMemory;
    @memset(bitmap.items, 0);

    var variadic_idx: usize = 0;
    for (params, 0..) |p, idx| {
        if (p.card == .one) {
            if (args_by_param[idx].len != 1) return IonError.InvalidIon;
            continue;
        }

        const args = args_by_param[idx];
        const grouping: u2 = if (args.len == 0) 0b00 else if (args.len == 1) 0b01 else 0b10;
        if (grouping == 0b00 and p.card == .one_or_many) return IonError.InvalidIon;
        if (grouping == 0b10 and p.card == .zero_or_one) return IonError.InvalidIon;

        const bit: usize = variadic_idx * 2;
        const byte_idx: usize = bit / 8;
        const bit_in_byte: u3 = @intCast(bit % 8);
        if (byte_idx >= bitmap.items.len) return IonError.InvalidIon;
        bitmap.items[byte_idx] |= (@as(u8, grouping) << bit_in_byte);
        variadic_idx += 1;
    }
    try appendSlice(out, allocator, bitmap.items);

    for (params, 0..) |p, idx| {
        const args = args_by_param[idx];

        if (p.card == .one) {
            try writeArgValue(allocator, out, options, p, args[0]);
            continue;
        }

        const grouping: u2 = if (args.len == 0) 0b00 else if (args.len == 1) 0b01 else 0b10;
        switch (grouping) {
            0b00 => {},
            0b01 => try writeArgValue(allocator, out, options, p, args[0]),
            0b10 => {
                switch (options.arg_group_encoding) {
                    .length_prefixed => {
                        var payload = std.ArrayListUnmanaged(u8){};
                        defer payload.deinit(allocator);
                        for (args) |e| try writeArgValue(allocator, &payload, options, p, e);
                        try writeFlexUIntShift1(out, allocator, payload.items.len);
                        try appendSlice(out, allocator, payload.items);
                    },
                    .delimited => {
                        // FlexUInt(0) selects the delimited forms:
                        // - tagged groups terminate with `0xF0`
                        // - tagless groups use chunked encoding terminated by FlexUInt(0)
                        try writeFlexUIntShift1(out, allocator, 0);

                        if (p.ty == .tagged) {
                            for (args) |e| try writeArgValue(allocator, out, options, p, e);
                            try appendByte(out, allocator, 0xF0);
                            continue;
                        }

                        // Chunked tagless encoding: write one or more `<flexuint chunk_len>
                        // <chunk_bytes...>` sections followed by `<flexuint 0>`.
                        const max_chunk: usize = @max(@as(usize, 1), options.arg_group_chunk_max_bytes);
                        var chunk = std.ArrayListUnmanaged(u8){};
                        defer chunk.deinit(allocator);
                        var one = std.ArrayListUnmanaged(u8){};
                        defer one.deinit(allocator);

                        const flush = struct {
                            fn run(a: std.mem.Allocator, o: *std.ArrayListUnmanaged(u8), ch: *std.ArrayListUnmanaged(u8)) IonError!void {
                                if (ch.items.len == 0) return;
                                try writeFlexUIntShift1(o, a, ch.items.len);
                                try appendSlice(o, a, ch.items);
                                ch.clearRetainingCapacity();
                            }
                        }.run;

                        for (args) |e| {
                            one.clearRetainingCapacity();
                            try writeArgValue(allocator, &one, options, p, e);

                            if (one.items.len > max_chunk) {
                                try flush(allocator, out, &chunk);
                                try writeFlexUIntShift1(out, allocator, one.items.len);
                                try appendSlice(out, allocator, one.items);
                                continue;
                            }

                            if (chunk.items.len != 0 and (chunk.items.len + one.items.len) > max_chunk) {
                                try flush(allocator, out, &chunk);
                            }
                            try appendSlice(&chunk, allocator, one.items);
                        }
                        try flush(allocator, out, &chunk);
                        try writeFlexUIntShift1(out, allocator, 0);
                    },
                }
            },
            else => return IonError.InvalidIon,
        }
    }
}

fn writeArgValue(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    options: Options,
    p: ion.macro.Param,
    e: value.Element,
) IonError!void {
    return switch (p.ty) {
        .tagged => writeElement(allocator, out, options, e),
        .macro_shape => blk: {
            if (e.annotations.len != 0) return IonError.InvalidIon;
            try writeMacroShapeArg(allocator, out, options, p, e);
            break :blk;
        },
        .flex_uint => blk: {
            if (e.annotations.len != 0) return IonError.InvalidIon;
            if (e.value != .int) return IonError.InvalidIon;
            try writeFlexUIntShift1Int(out, allocator, e.value.int);
            break :blk;
        },
        .flex_int => blk: {
            if (e.annotations.len != 0) return IonError.InvalidIon;
            if (e.value != .int) return IonError.InvalidIon;
            try writeFlexIntShift1Int(out, allocator, e.value.int);
            break :blk;
        },
        .flex_sym => blk: {
            if (e.annotations.len != 0) return IonError.InvalidIon;
            if (e.value != .symbol) return IonError.InvalidIon;
            try writeFlexSymSymbol(out, allocator, options, e.value.symbol);
            break :blk;
        },
        .uint8, .uint16, .uint32, .uint64 => blk: {
            if (e.annotations.len != 0) return IonError.InvalidIon;
            if (e.value != .int) return IonError.InvalidIon;
            const u = try intToU64(e.value.int);
            const n: usize = switch (p.ty) {
                .uint8 => 1,
                .uint16 => 2,
                .uint32 => 4,
                .uint64 => 8,
                else => unreachable,
            };
            if (n == 1) {
                if (u > std.math.maxInt(u8)) return IonError.InvalidIon;
                try appendByte(out, allocator, @intCast(u));
                break :blk;
            }
            var buf: [8]u8 = undefined;
            std.mem.writeInt(u64, &buf, u, .little);
            try appendSlice(out, allocator, buf[0..n]);
            break :blk;
        },
        .int8, .int16, .int32, .int64 => blk: {
            if (e.annotations.len != 0) return IonError.InvalidIon;
            if (e.value != .int) return IonError.InvalidIon;
            const i = try intToI64(e.value.int);
            const n: usize = switch (p.ty) {
                .int8 => 1,
                .int16 => 2,
                .int32 => 4,
                .int64 => 8,
                else => unreachable,
            };
            if (n == 1) {
                if (i < std.math.minInt(i8) or i > std.math.maxInt(i8)) return IonError.InvalidIon;
                try appendByte(out, allocator, @bitCast(@as(i8, @intCast(i))));
                break :blk;
            }
            var buf: [8]u8 = undefined;
            std.mem.writeInt(i64, &buf, i, .little);
            try appendSlice(out, allocator, buf[0..n]);
            break :blk;
        },
        .float16 => blk: {
            if (e.annotations.len != 0) return IonError.InvalidIon;
            if (e.value != .float) return IonError.InvalidIon;
            const f: f16 = @floatCast(e.value.float);
            var buf: [2]u8 = undefined;
            std.mem.writeInt(u16, &buf, @bitCast(f), .little);
            try appendSlice(out, allocator, &buf);
            break :blk;
        },
        .float32 => blk: {
            if (e.annotations.len != 0) return IonError.InvalidIon;
            if (e.value != .float) return IonError.InvalidIon;
            const f: f32 = @floatCast(e.value.float);
            var buf: [4]u8 = undefined;
            std.mem.writeInt(u32, &buf, @bitCast(f), .little);
            try appendSlice(out, allocator, &buf);
            break :blk;
        },
        .float64 => blk: {
            if (e.annotations.len != 0) return IonError.InvalidIon;
            if (e.value != .float) return IonError.InvalidIon;
            var buf: [8]u8 = undefined;
            std.mem.writeInt(u64, &buf, @bitCast(e.value.float), .little);
            try appendSlice(out, allocator, &buf);
            break :blk;
        },
    };
}

fn writeMacroShapeArg(
    allocator: std.mem.Allocator,
    out: *std.ArrayListUnmanaged(u8),
    options: Options,
    p: ion.macro.Param,
    e: value.Element,
) IonError!void {
    const shape = p.shape orelse return IonError.InvalidIon;
    if (e.value != .sexp) return IonError.InvalidIon;
    const args = e.value.sexp;

    // Qualified system macro shape: `$ion::make_decimal`.
    if (shape.module) |m| {
        if (!std.mem.eql(u8, m, "$ion")) return IonError.Unsupported;
        if (std.mem.eql(u8, shape.name, "make_decimal")) {
            if (args.len != 2) return IonError.InvalidIon;
            // Decoder expects two tagged value expressions.
            try writeElement(allocator, out, options, args[0]);
            try writeElement(allocator, out, options, args[1]);
            return;
        }
        if (std.mem.eql(u8, shape.name, "sum")) {
            // Payload encoding matches the qualified system macro invocation encoding (minus the
            // leading `0xEF <addr>`): two tagged values back-to-back.
            if (args.len != 2) return IonError.InvalidIon;
            try writeElement(allocator, out, options, args[0]);
            try writeElement(allocator, out, options, args[1]);
            return;
        }
        if (std.mem.eql(u8, shape.name, "parse_ion")) {
            // Payload encoding matches the qualified system macro invocation encoding (minus the
            // leading `0xEF <addr>`): a single tagged value argument (string/clob/blob).
            if (args.len != 1) return IonError.InvalidIon;
            switch (args[0].value) {
                .string, .clob, .blob => {},
                else => return IonError.InvalidIon,
            }
            try writeElement(allocator, out, options, args[0]);
            return;
        }
        if (std.mem.eql(u8, shape.name, "make_field")) {
            // Payload encoding matches the qualified system macro invocation encoding (minus the
            // leading `0xEF <addr>`): two tagged values back-to-back.
            //
            // Note: system macro address 16 is overloaded with `parse_ion`. The decoder selects
            // `parse_ion` when the first argument is a string/clob/blob, so require a symbol here
            // for deterministic `make_field` encoding.
            if (args.len != 2) return IonError.InvalidIon;
            if (args[0].value != .symbol) return IonError.InvalidIon;
            try writeElement(allocator, out, options, args[0]);
            try writeElement(allocator, out, options, args[1]);
            return;
        }
        if (std.mem.eql(u8, shape.name, "annotate")) {
            // Payload encoding matches the qualified system macro invocation encoding (minus the
            // leading `0xEF <addr>`):
            //   <presence> <annotations...> <value>
            //
            // Represent the arguments as a sexp of N items:
            //   (<annotation>... <value>)
            // where the last element is the value and the preceding elements are annotations.
            if (args.len == 0) return IonError.InvalidIon;

            const val = args[args.len - 1];
            const annotations = args[0 .. args.len - 1];

            if (annotations.len == 0) {
                try appendByte(out, allocator, 0x00);
            } else if (annotations.len == 1) {
                try appendByte(out, allocator, 0x01);
                try writeElement(allocator, out, options, annotations[0]);
            } else {
                try appendByte(out, allocator, 0x02);
                var payload = std.ArrayListUnmanaged(u8){};
                defer payload.deinit(allocator);
                for (annotations) |a| try writeElement(allocator, &payload, options, a);
                try writeFlexUIntShift1(out, allocator, payload.items.len);
                try appendSlice(out, allocator, payload.items);
            }

            try writeElement(allocator, out, options, val);
            return;
        }
        if (std.mem.eql(u8, shape.name, "values") or
            std.mem.eql(u8, shape.name, "meta") or
            std.mem.eql(u8, shape.name, "make_string") or
            std.mem.eql(u8, shape.name, "make_symbol") or
            std.mem.eql(u8, shape.name, "make_blob") or
            std.mem.eql(u8, shape.name, "flatten") or
            std.mem.eql(u8, shape.name, "delta"))
        {
            // Payload encoding matches the qualified system macro invocation encoding (minus the
            // leading `0xEF <addr>`):
            // - 0x00: no args
            // - 0x01: single tagged value
            // - 0x02: tagged expression group (FlexUInt length + bytes)
            if (args.len == 0) {
                try appendByte(out, allocator, 0x00);
                return;
            }
            if (args.len == 1) {
                try appendByte(out, allocator, 0x01);
                try writeElement(allocator, out, options, args[0]);
                return;
            }

            try appendByte(out, allocator, 0x02);
            var payload = std.ArrayListUnmanaged(u8){};
            defer payload.deinit(allocator);
            for (args) |a| try writeElement(allocator, &payload, options, a);
            try writeFlexUIntShift1(out, allocator, payload.items.len);
            try appendSlice(out, allocator, payload.items);
            return;
        }
        if (std.mem.eql(u8, shape.name, "repeat")) {
            // Payload encoding matches the qualified system macro invocation encoding (minus the
            // leading `0xEF <addr>`): a presence byte and tagged value for `<n>`, followed by a
            // single tagged value expression for `<expr>`.
            if (args.len != 2) return IonError.InvalidIon;

            try appendByte(out, allocator, 0x01);
            try writeElement(allocator, out, options, args[0]);
            try writeElement(allocator, out, options, args[1]);
            return;
        }
        if (std.mem.eql(u8, shape.name, "make_list") or
            std.mem.eql(u8, shape.name, "make_sexp") or
            std.mem.eql(u8, shape.name, "make_struct"))
        {
            // Payload encoding matches the qualified system macro invocation encoding (minus the
            // leading `0xEF <addr>`):
            // - 0x00: no args
            // - 0x01: single tagged value
            // - 0x02: tagged expression group (FlexUInt length + bytes)
            if (args.len == 0) {
                try appendByte(out, allocator, 0x00);
                return;
            }
            if (args.len == 1) {
                try appendByte(out, allocator, 0x01);
                try writeElement(allocator, out, options, args[0]);
                return;
            }

            try appendByte(out, allocator, 0x02);
            var payload = std.ArrayListUnmanaged(u8){};
            defer payload.deinit(allocator);
            for (args) |a| try writeElement(allocator, &payload, options, a);
            try writeFlexUIntShift1(out, allocator, payload.items.len);
            try appendSlice(out, allocator, payload.items);
            return;
        }
        if (std.mem.eql(u8, shape.name, "make_timestamp")) {
            // Payload encoding matches the qualified system macro invocation encoding (minus the
            // leading `0xEF <addr>`): 2-byte little-endian presence bitmap, then `<year>` as a
            // tagged value followed by each present optional arg as a tagged value.
            if (args.len < 1 or args.len > 7) return IonError.InvalidIon;

            const year = args[0];
            const month: ?value.Element = if (args.len >= 2) args[1] else null;
            const day: ?value.Element = if (args.len >= 3) args[2] else null;
            const hour: ?value.Element = if (args.len >= 4) args[3] else null;
            const minute: ?value.Element = if (args.len >= 5) args[4] else null;
            const seconds: ?value.Element = if (args.len >= 6) args[5] else null;
            const offset: ?value.Element = if (args.len >= 7) args[6] else null;

            const code = struct {
                fn set(presence: *u16, idx: u4, present: bool) void {
                    if (!present) return;
                    presence.* |= (@as(u16, 0b01) << @intCast(@as(u5, idx) * 2));
                }
            };

            var presence: u16 = 0;
            code.set(&presence, 0, month != null);
            code.set(&presence, 1, day != null);
            code.set(&presence, 2, hour != null);
            code.set(&presence, 3, minute != null);
            code.set(&presence, 4, seconds != null);
            code.set(&presence, 5, offset != null);

            var pres_bytes: [2]u8 = undefined;
            std.mem.writeInt(u16, &pres_bytes, presence, .little);
            try appendSlice(out, allocator, &pres_bytes);

            try writeElement(allocator, out, options, year);
            if (month) |v| try writeElement(allocator, out, options, v);
            if (day) |v| try writeElement(allocator, out, options, v);
            if (hour) |v| try writeElement(allocator, out, options, v);
            if (minute) |v| try writeElement(allocator, out, options, v);
            if (seconds) |v| try writeElement(allocator, out, options, v);
            if (offset) |v| try writeElement(allocator, out, options, v);
            return;
        }
        if (std.mem.eql(u8, shape.name, "default")) {
            // Payload encoding matches the qualified system macro invocation encoding (minus the
            // leading `0xEF <addr>`): a 1-byte packed presence code followed by the present args.
            //
            // Represent the arguments as a sexp of 2 items:
            //   (<a> <b>)
            // where each item is either:
            // - a single (unannotated) value => presence 0b01
            // - an s-expression of 0+ values => presence 0b10 (tagged expression group)
            if (args.len != 2) return IonError.InvalidIon;

            const code = struct {
                fn classify(arg: value.Element) IonError!u2 {
                    if (arg.annotations.len != 0) return IonError.InvalidIon;
                    return switch (arg.value) {
                        .sexp => 0b10,
                        else => 0b01,
                    };
                }
                fn pack(a: u2, b: u2) u8 {
                    return @as(u8, a) | (@as(u8, b) << 2);
                }
            };

            const a_code = try code.classify(args[0]);
            const b_code = try code.classify(args[1]);
            try appendByte(out, allocator, code.pack(a_code, b_code));

            const writeOne = struct {
                fn run(alloc: std.mem.Allocator, o: *std.ArrayListUnmanaged(u8), opt: Options, arg: value.Element) IonError!void {
                    if (arg.annotations.len != 0) return IonError.InvalidIon;
                    if (arg.value == .sexp) return IonError.InvalidIon;
                    try writeValue(alloc, o, opt, arg.value);
                }
            }.run;

            const writeGroup = struct {
                fn run(alloc: std.mem.Allocator, o: *std.ArrayListUnmanaged(u8), opt: Options, arg: value.Element) IonError!void {
                    if (arg.annotations.len != 0) return IonError.InvalidIon;
                    if (arg.value != .sexp) return IonError.InvalidIon;
                    const group = arg.value.sexp;

                    // Use the spec delimited tagged group form: FlexUInt(0) ... 0xF0.
                    try writeFlexUIntShift1(o, alloc, 0);
                    for (group) |g| try writeElement(alloc, o, opt, g);
                    try appendByte(o, alloc, 0xF0);
                }
            }.run;

            if (a_code == 0b01) try writeOne(allocator, out, options, args[0]) else try writeGroup(allocator, out, options, args[0]);
            if (b_code == 0b01) try writeOne(allocator, out, options, args[1]) else try writeGroup(allocator, out, options, args[1]);
            return;
        }
        if (std.mem.eql(u8, shape.name, "none")) {
            if (args.len != 0) return IonError.InvalidIon;
            // `none` produces no values and consumes no argument bytes.
            return;
        }
        return IonError.Unsupported;
    }

    const tab = options.mactab orelse return IonError.Unsupported;
    const m = tab.macroForName(shape.name) orelse return IonError.Unsupported;
    if (args.len != m.params.len) return IonError.InvalidIon;

    for (m.params, 0..) |mp, idx| {
        if (mp.card != .one) return IonError.Unsupported;
        // Match decoder: tagged params are encoded as a value expression; tagless params are
        // encoded using the tagless byte representation.
        try writeArgValue(allocator, out, options, mp, args[idx]);
    }
}

fn intToU64(v: value.Int) IonError!u64 {
    return switch (v) {
        .small => |i| {
            if (i < 0) return IonError.InvalidIon;
            if (i > std.math.maxInt(u64)) return IonError.InvalidIon;
            return @intCast(i);
        },
        .big => |p| p.*.toConst().toInt(u64) catch return IonError.InvalidIon,
    };
}

fn intToI64(v: value.Int) IonError!i64 {
    return switch (v) {
        .small => |i| {
            if (i < std.math.minInt(i64) or i > std.math.maxInt(i64)) return IonError.InvalidIon;
            return @intCast(i);
        },
        .big => |p| p.*.toConst().toInt(i64) catch return IonError.InvalidIon,
    };
}

fn collectUserSymbolTexts(
    allocator: std.mem.Allocator,
    elems: []const value.Element,
    options: Options,
    map: *std.StringHashMapUnmanaged(u32),
    out_texts: *std.ArrayListUnmanaged([]const u8),
) IonError!void {
    var next_sid: u32 = 1;

    const addText = struct {
        fn run(alloc: std.mem.Allocator, opts: Options, m: *std.StringHashMapUnmanaged(u32), texts: *std.ArrayListUnmanaged([]const u8), next: *u32, t: []const u8) IonError!void {
            if (systemSymtab11SidForText(opts, t) != null) return;
            if (m.contains(t)) return;
            m.put(alloc, t, next.*) catch return IonError.OutOfMemory;
            texts.append(alloc, t) catch return IonError.OutOfMemory;
            next.* += 1;
        }
    }.run;

    const validateSidOnly = struct {
        fn run(opts: Options, sym: value.Symbol) IonError!void {
            if (sym.text != null) return;
            if (sym.sid) |sid| {
                // `$0` is a well-known "unknown symbol" sentinel and does not require text.
                if (sid == 0) return;
                // Allow SID-only system symbols; everything else requires text for self-contained output.
                if (sid > 0 and sid <= systemSymtab11MaxId(opts)) return;
                return IonError.InvalidIon;
            }
            return IonError.InvalidIon;
        }
    }.run;

    const walkElement = struct {
        fn run(
            alloc: std.mem.Allocator,
            opts: Options,
            m: *std.StringHashMapUnmanaged(u32),
            texts: *std.ArrayListUnmanaged([]const u8),
            next: *u32,
            e: value.Element,
        ) IonError!void {
            for (e.annotations) |a| {
                if (a.text) |t| try addText(alloc, opts, m, texts, next, t) else try validateSidOnly(opts, a);
            }
            switch (e.value) {
                .symbol => |s| {
                    if (s.text) |t| try addText(alloc, opts, m, texts, next, t) else try validateSidOnly(opts, s);
                },
                .list => |items| for (items) |child| try run(alloc, opts, m, texts, next, child),
                .sexp => |items| for (items) |child| try run(alloc, opts, m, texts, next, child),
                .@"struct" => |st| {
                    for (st.fields) |f| {
                        if (f.name.text) |t| try addText(alloc, opts, m, texts, next, t) else try validateSidOnly(opts, f.name);
                        try run(alloc, opts, m, texts, next, f.value);
                    }
                },
                .null, .bool, .int, .float, .decimal, .timestamp, .string, .blob, .clob => {},
            }
        }
    }.run;

    for (elems) |e| try walkElement(allocator, options, map, out_texts, &next_sid, e);
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

fn writeFlexUIntShift1Int(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, v: value.Int) IonError!void {
    // Generalization of `writeFlexUIntShift1` that supports BigInt inputs.
    switch (v) {
        .small => |i| {
            if (i < 0) return IonError.InvalidIon;
            var tmp = std.math.big.int.Managed.init(allocator) catch return IonError.OutOfMemory;
            defer tmp.deinit();
            tmp.set(@as(u128, @intCast(i))) catch return IonError.OutOfMemory;
            return writeFlexUIntShift1Big(out, allocator, tmp.toConst());
        },
        .big => |p| {
            if (!p.*.toConst().positive) return IonError.InvalidIon;
            return writeFlexUIntShift1Big(out, allocator, p.*.toConst());
        },
    }
}

fn writeFlexUIntShift1Big(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, c: std.math.big.int.Const) IonError!void {
    // FlexUInt encoding uses a tag bit that is the least-significant set bit of the underlying
    // little-endian integer. If the tag bit is at position (N-1), the encoding is N bytes long and
    // the value is obtained by shifting right by N bits.
    if (!c.positive) return IonError.InvalidIon;
    const bits: usize = c.bitCountAbs();
    const n: usize = @max(@as(usize, 1), (bits + 6) / 7);

    var val = std.math.big.int.Managed.init(allocator) catch return IonError.OutOfMemory;
    defer val.deinit();
    val.copy(c) catch return IonError.OutOfMemory;

    var shifted = std.math.big.int.Managed.init(allocator) catch return IonError.OutOfMemory;
    defer shifted.deinit();
    shifted.shiftLeft(&val, n) catch return IonError.OutOfMemory;

    var tag = std.math.big.int.Managed.init(allocator) catch return IonError.OutOfMemory;
    defer tag.deinit();
    tag.set(@as(u8, 1)) catch return IonError.OutOfMemory;
    tag.shiftLeft(&tag, n - 1) catch return IonError.OutOfMemory;

    var raw = std.math.big.int.Managed.init(allocator) catch return IonError.OutOfMemory;
    defer raw.deinit();
    raw.add(&shifted, &tag) catch return IonError.OutOfMemory;

    const buf = allocator.alloc(u8, n) catch return IonError.OutOfMemory;
    defer allocator.free(buf);
    raw.toConst().writeTwosComplement(buf, .little);
    try appendSlice(out, allocator, buf);
}

fn writeFlexIntShift1Int(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, v: value.Int) IonError!void {
    // Generalization of `writeFlexIntShift1` that supports BigInt inputs.
    const c = switch (v) {
        .small => |i| blk: {
            var tmp = std.math.big.int.Managed.init(allocator) catch return IonError.OutOfMemory;
            defer tmp.deinit();
            tmp.set(i) catch return IonError.OutOfMemory;
            break :blk tmp.toConst();
        },
        .big => |p| p.*.toConst(),
    };

    var n: usize = 1;
    while (true) : (n += 1) {
        const width: usize = n * 7;
        if (c.fitsInTwosComp(.signed, width)) break;
        if (n > 1_000_000) return IonError.InvalidIon; // sanity cap
    }

    const width: usize = n * 7;
    const bytes_len: usize = (width + 7) / 8;
    var payload_bytes = std.ArrayListUnmanaged(u8){};
    defer payload_bytes.deinit(allocator);
    payload_bytes.resize(allocator, bytes_len) catch return IonError.OutOfMemory;
    @memset(payload_bytes.items, 0);
    c.writePackedTwosComplement(payload_bytes.items, 0, width, .little);

    var payload_u = std.math.big.int.Managed.init(allocator) catch return IonError.OutOfMemory;
    defer payload_u.deinit();
    payload_u.ensureCapacity((bytes_len * 8 + @bitSizeOf(std.math.big.Limb) - 1) / @bitSizeOf(std.math.big.Limb)) catch return IonError.OutOfMemory;
    var m = payload_u.toMutable();
    m.readTwosComplement(payload_bytes.items, bytes_len * 8, .little, .unsigned);
    payload_u.setMetadata(true, m.len);

    var shifted = std.math.big.int.Managed.init(allocator) catch return IonError.OutOfMemory;
    defer shifted.deinit();
    shifted.shiftLeft(&payload_u, n) catch return IonError.OutOfMemory;

    var tag = std.math.big.int.Managed.init(allocator) catch return IonError.OutOfMemory;
    defer tag.deinit();
    tag.set(@as(u8, 1)) catch return IonError.OutOfMemory;
    tag.shiftLeft(&tag, n - 1) catch return IonError.OutOfMemory;

    var raw = std.math.big.int.Managed.init(allocator) catch return IonError.OutOfMemory;
    defer raw.deinit();
    raw.add(&shifted, &tag) catch return IonError.OutOfMemory;

    const buf = allocator.alloc(u8, n) catch return IonError.OutOfMemory;
    defer allocator.free(buf);
    raw.toConst().writeTwosComplement(buf, .little);
    try appendSlice(out, allocator, buf);
}

fn appendByte(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, b: u8) IonError!void {
    out.append(allocator, b) catch return IonError.OutOfMemory;
}

fn appendSlice(out: *std.ArrayListUnmanaged(u8), allocator: std.mem.Allocator, bytes: []const u8) IonError!void {
    out.appendSlice(allocator, bytes) catch return IonError.OutOfMemory;
}

test "writer11 FlexUInt encodings match ion-rust" {
    const alloc = std.testing.allocator;

    const Case = struct { v: usize, enc: []const u8 };
    const cases = [_]Case{
        .{ .v = 0, .enc = &.{0b00000001} },
        .{ .v = 1, .enc = &.{0b00000011} },
        .{ .v = 2, .enc = &.{0b00000101} },
        .{ .v = 3, .enc = &.{0b00000111} },
        .{ .v = 4, .enc = &.{0b00001001} },
        .{ .v = 5, .enc = &.{0b00001011} },
        .{ .v = 14, .enc = &.{0b00011101} },
        .{ .v = 63, .enc = &.{0b01111111} },
        .{ .v = 64, .enc = &.{0b10000001} },
        .{ .v = 127, .enc = &.{0b11111111} },
        .{ .v = 128, .enc = &.{ 0b00000010, 0b00000010 } },
        .{ .v = 729, .enc = &.{ 0b01100110, 0b00001011 } },
        .{ .v = 16383, .enc = &.{ 0b11111110, 0b11111111 } },
        .{ .v = 16384, .enc = &.{ 0b00000100, 0b00000000, 0b00000010 } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(alloc);

    for (cases) |c| {
        out.clearRetainingCapacity();
        try writeFlexUIntShift1(&out, alloc, c.v);
        try std.testing.expectEqualSlices(u8, c.enc, out.items);
    }
}

test "writer11 FlexInt encodings match ion-rust" {
    const alloc = std.testing.allocator;

    const Case = struct { v: i64, enc: []const u8 };
    const cases = [_]Case{
        .{ .v = 0, .enc = &.{0b00000001} },
        .{ .v = 1, .enc = &.{0b00000011} },
        .{ .v = 63, .enc = &.{0b01111111} },
        .{ .v = 64, .enc = &.{ 0b00000010, 0b00000001 } },
        .{ .v = 729, .enc = &.{ 0b01100110, 0b00001011 } },
        .{ .v = 9223372036854775807, .enc = &.{ 0b00000000, 0b11111110, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b11111111, 0b00000001 } },
        .{ .v = -1, .enc = &.{0b11111111} },
        .{ .v = -2, .enc = &.{0b11111101} },
        .{ .v = -64, .enc = &.{0b10000001} },
        .{ .v = -65, .enc = &.{ 0b11111110, 0b11111110 } },
        .{ .v = -729, .enc = &.{ 0b10011110, 0b11110100 } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(alloc);

    for (cases) |c| {
        out.clearRetainingCapacity();
        try writeFlexIntShift1(&out, alloc, c.v);
        try std.testing.expectEqualSlices(u8, c.enc, out.items);
    }
}
