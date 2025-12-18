//! Ion text parser.
//!
//! Features implemented for the ion-tests corpus:
//! - Top-level stream parsing with comment/whitespace handling (including HT/VT/FF/CR/LF).
//! - Containers: list (`[...]`), sexp (`(...)`), struct (`{...}`).
//! - Literals: nulls, bools, ints, floats (`nan`, `±inf`), decimals, timestamps, strings, symbols, clobs/blobs.
//! - Minimal local symbol table handling via `$ion_symbol_table::{symbols:[...]}`.

const std = @import("std");
const ion = @import("../ion.zig");
const value = @import("value.zig");
const symtab = @import("symtab.zig");
const tdl_eval = @import("tdl_eval.zig");

const IonError = ion.IonError;

const SharedSymtab = struct {
    name: []const u8,
    version: u32,
    // Index 0 corresponds to the shared table's SID 1 (shared table SIDs are 1-based).
    symbols: []const ?[]const u8,
};

/// Parses an Ion text stream into a top-level sequence of `value.Element`s.
///
/// All returned slices are allocated in `arena` and valid until the arena is deinited.
pub fn parseTopLevel(arena: *value.Arena, bytes: []const u8) IonError![]value.Element {
    var parser = try Parser.init(arena, bytes, null);
    return parser.parseTopLevel();
}

/// Parses an Ion text stream, optionally using a conformance-provided Ion 1.1 macro table.
///
/// This is currently used by the conformance runner to evaluate `(:foo ...)` calls where the macro
/// definitions are supplied out-of-band via `(mactab ...)`.
pub fn parseTopLevelWithMacroTable(arena: *value.Arena, bytes: []const u8, mactab: ?*const ion.macro.MacroTable) IonError![]value.Element {
    var parser = try Parser.init(arena, bytes, mactab);
    return parser.parseTopLevel();
}

/// Parses an Ion text stream, but does NOT concatenate adjacent string literals.
/// Intended for the Ion 1.1 conformance DSL, which uses sexps for clauses and may need
/// to represent multiple string arguments without Ion's normal string literal concatenation.
pub fn parseTopLevelNoStringConcat(arena: *value.Arena, bytes: []const u8) IonError![]value.Element {
    var parser = try Parser.initWithOptions(arena, bytes, null, false, false);
    return parser.parseTopLevel();
}

/// Parses the Ion 1.1 conformance DSL (not strict Ion text), but does NOT concatenate adjacent
/// string literals.
///
/// The conformance DSL is "Ion-shaped" but includes tokens that are not valid Ion identifiers,
/// such as `x?` / `x*` / `x+`, plus TDL-ish forms like `.literal` and `%x`.
pub fn parseTopLevelConformanceDslNoStringConcat(arena: *value.Arena, bytes: []const u8) IonError![]value.Element {
    var parser = try Parser.initWithOptions(arena, bytes, null, false, true);
    return parser.parseTopLevel();
}

/// Debug helper: on error, writes the parser byte offset into `err_index`.
/// Intended for ad-hoc repro tooling; normal callers should use `parseTopLevel`.
///
/// All returned slices are allocated in `arena` and valid until the arena is deinited.
pub fn parseTopLevelWithErrorIndex(arena: *value.Arena, bytes: []const u8, err_index: *usize) IonError![]value.Element {
    var parser = try Parser.init(arena, bytes, null);
    return parser.parseTopLevel() catch |e| {
        err_index.* = parser.i;
        return e;
    };
}

const Parser = struct {
    arena: *value.Arena,
    input: []const u8,
    i: usize = 0,
    version: enum { v1_0, v1_1 } = .v1_0,
    concat_string_literals: bool = true,
    conformance_dsl_mode: bool = false,
    mactab: ?*const ion.macro.MacroTable = null,
    st: symtab.SymbolTable,
    shared: std.StringHashMapUnmanaged(SharedSymtab) = .{},

    fn init(arena: *value.Arena, input: []const u8, mactab: ?*const ion.macro.MacroTable) IonError!Parser {
        return initWithOptions(arena, input, mactab, true, false);
    }

    fn initWithOptions(
        arena: *value.Arena,
        input: []const u8,
        mactab: ?*const ion.macro.MacroTable,
        concat_string_literals: bool,
        conformance_dsl_mode: bool,
    ) IonError!Parser {
        return .{
            .arena = arena,
            .input = input,
            .i = 0,
            .version = .v1_0,
            .concat_string_literals = concat_string_literals,
            .conformance_dsl_mode = conformance_dsl_mode,
            .mactab = mactab,
            .st = try symtab.SymbolTable.init(arena),
            .shared = .{},
        };
    }

    fn parseTopLevel(self: *Parser) IonError![]value.Element {
        defer self.st.deinit();
        defer self.shared.deinit(self.arena.allocator());

        var out = std.ArrayListUnmanaged(value.Element){};
        errdefer out.deinit(self.arena.allocator());

        while (true) {
            try self.skipWsComments();
            if (self.eof()) break;

            if (try self.hasMacroInvocationStart()) {
                const expanded = try self.parseMacroInvocationElems();
                for (expanded) |elem| {
                    // Ion 1.1 e-expressions expand to user values; do not treat expansion results
                    // as system values, even if they look like `$ion_symbol_table::{...}`.
                    const is_literal = hasIonLiteralAnnotation(elem.annotations);
                    const stripped = if (is_literal) try stripIonLiteralAnnotation(self.arena, elem) else elem;
                    out.append(self.arena.allocator(), stripped) catch return IonError.OutOfMemory;
                }
                continue;
            }

            // Ion Version Marker in text: $ion_1_0 at top-level (not annotated) is a system value.
            // It can also appear as a normal symbol if annotated/inside containers; we only treat
            // it as IVM if it's the next token at top-level with no annotations.
            const before = self.i;
            const elem = try self.parseElement(.top);
            const is_literal = hasIonLiteralAnnotation(elem.annotations);
            if (elem.annotations.len == 0 and elem.value == .symbol) {
                if (elem.value.symbol.text) |t| {
                    if (std.mem.startsWith(u8, t, "$ion_")) {
                        const rest = t["$ion_".len..];
                        if (std.mem.indexOfScalar(u8, rest, '_')) |u| {
                            // Only treat $ion_<major>_<minor> as a version marker if both sides are digits.
                            const major_str = rest[0..u];
                            const minor_str = rest[u + 1 ..];
                            if (major_str.len != 0 and minor_str.len != 0) {
                                var major_all_digits = true;
                                for (major_str) |c| {
                                    if (!std.ascii.isDigit(c)) major_all_digits = false;
                                }
                                var minor_all_digits = true;
                                for (minor_str) |c| {
                                    if (!std.ascii.isDigit(c)) minor_all_digits = false;
                                }
                                if (major_all_digits and minor_all_digits and !std.mem.eql(u8, t, "$ion_1_0") and !std.mem.eql(u8, t, "$ion_1_1")) {
                                    return IonError.InvalidIon;
                                }
                            }
                        }
                    }
                }
            }
            if (isSystemValue(elem) and !is_literal) {
                // Apply symbol table if present, otherwise ignore.
                if (elem.annotations.len == 0 and elem.value == .symbol) {
                    if (elem.value.symbol.text) |t| {
                        if (std.mem.eql(u8, t, "$ion_1_1")) {
                            self.version = .v1_1;
                        } else if (std.mem.eql(u8, t, "$ion_1_0")) {
                            self.version = .v1_0;
                        }
                    }
                }
                try self.maybeConsumeSymbolTable(elem);
            } else {
                const stripped = if (is_literal) try stripIonLiteralAnnotation(self.arena, elem) else elem;
                out.append(self.arena.allocator(), stripped) catch return IonError.OutOfMemory;
            }

            // Prevent infinite loops on malformed inputs.
            if (self.i == before) return IonError.InvalidIon;
        }

        return out.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
    }

    fn hasMacroInvocationStart(self: *Parser) IonError!bool {
        // Ion 1.0 does not allow macro invocations (and ':' is not a valid token start there).
        // Only enable `(:...)` parsing after seeing `$ion_1_1`.
        if (self.version != .v1_1) return false;
        if (!self.startsWith("(")) return false;
        const save = self.i;
        self.consume(1);
        // Macros are sexp-like; allow whitespace/comments after '('.
        self.skipWsComments() catch {
            self.i = save;
            return false;
        };
        const yes = !self.eof() and self.peek().? == ':';
        self.i = save;
        return yes;
    }

    fn parseMacroInvocationElems(self: *Parser) IonError![]value.Element {
        if (!self.startsWith("(")) return IonError.InvalidIon;
        self.consume(1);
        try self.skipWsComments();

        if (self.eof() or self.peek().? != ':') return IonError.InvalidIon;
        self.consume(1);
        if (self.eof()) return IonError.Incomplete;

        // Expression group: `(:: <expr>*)` evaluates each expression and inlines its values.
        // The conformance suite uses this heavily to feed multi-valued expressions into macros.
        if (self.peek().? == ':') {
            self.consume(1);
            var out = std.ArrayListUnmanaged(value.Element){};
            errdefer out.deinit(self.arena.allocator());
            while (true) {
                try self.skipWsComments();
                if (self.eof()) return IonError.Incomplete;
                const c = self.peek().?;
                if (c == ')') {
                    self.consume(1);
                    break;
                }
                if (c == ',') return IonError.InvalidIon;

                if (try self.hasMacroInvocationStart()) {
                    const expanded = try self.parseMacroInvocationElems();
                    out.appendSlice(self.arena.allocator(), expanded) catch return IonError.OutOfMemory;
                    continue;
                }

                const elem = try self.parseElement(.sexp);
                out.append(self.arena.allocator(), elem) catch return IonError.OutOfMemory;
            }
            return out.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
        }

        // Macro identifier: either a name (`values`) or an address (`1`), optionally qualified as
        // `$ion::...` (as used by the conformance suite for system macro invocations).
        var macro_addr: ?u32 = null;
        const id_start = self.i;
        if (self.startsWith("$ion::")) {
            self.consume("$ion::".len);
        }
        if (self.eof()) return IonError.Incomplete;
        if (std.ascii.isDigit(self.peek().?)) {
            var v: u32 = 0;
            while (!self.eof() and std.ascii.isDigit(self.peek().?)) {
                v = std.math.mul(u32, v, 10) catch return IonError.InvalidIon;
                v = std.math.add(u32, v, @intCast(self.peek().? - '0')) catch return IonError.InvalidIon;
                self.consume(1);
            }
            macro_addr = v;
        } else {
            if (!std.ascii.isAlphabetic(self.peek().?) and self.peek().? != '_') return IonError.InvalidIon;
            self.consume(1);
            while (!self.eof()) {
                const c = self.peek().?;
                if (std.ascii.isAlphanumeric(c) or c == '_') {
                    self.consume(1);
                    continue;
                }
                break;
            }
        }
        const macro_id = self.input[id_start..self.i];

        const MacroKind = enum {
            none,
            values,
            default,
            meta,
            annotate,
            repeat,
            delta,
            sum,
            make_string,
            make_symbol,
            make_list,
            make_sexp,
            make_decimal,
            make_timestamp,
            flatten,
            make_field,
            make_struct,
            parse_ion,
        };

        const kind: ?MacroKind = blk: {
            if (macro_addr) |addr| {
                break :blk switch (addr) {
                    0 => .none,
                    1 => .values,
                    2 => .default,
                    4 => .repeat,
                    6 => .delta,
                    7 => .sum,
                    8 => .annotate,
                    9 => .make_string,
                    10 => .make_symbol,
                    11 => .make_decimal,
                    12 => .make_timestamp,
                    14 => .make_list,
                    15 => .make_sexp,
                    16 => .make_field,
                    17 => .make_struct,
                    19 => .flatten,
                    else => null,
                };
            }
            if (std.mem.eql(u8, macro_id, "none") or std.mem.eql(u8, macro_id, "$ion::none")) break :blk .none;
            if (std.mem.eql(u8, macro_id, "values") or std.mem.eql(u8, macro_id, "$ion::values")) break :blk .values;
            if (std.mem.eql(u8, macro_id, "default") or std.mem.eql(u8, macro_id, "$ion::default")) break :blk .default;
            if (std.mem.eql(u8, macro_id, "meta") or std.mem.eql(u8, macro_id, "$ion::meta")) break :blk .meta;
            if (std.mem.eql(u8, macro_id, "annotate") or std.mem.eql(u8, macro_id, "$ion::annotate")) break :blk .annotate;
            if (std.mem.eql(u8, macro_id, "repeat") or std.mem.eql(u8, macro_id, "$ion::repeat")) break :blk .repeat;
            if (std.mem.eql(u8, macro_id, "delta") or std.mem.eql(u8, macro_id, "$ion::delta")) break :blk .delta;
            if (std.mem.eql(u8, macro_id, "sum") or std.mem.eql(u8, macro_id, "$ion::sum")) break :blk .sum;
            if (std.mem.eql(u8, macro_id, "make_string") or std.mem.eql(u8, macro_id, "$ion::make_string")) break :blk .make_string;
            if (std.mem.eql(u8, macro_id, "make_symbol") or std.mem.eql(u8, macro_id, "$ion::make_symbol")) break :blk .make_symbol;
            if (std.mem.eql(u8, macro_id, "make_decimal") or std.mem.eql(u8, macro_id, "$ion::make_decimal")) break :blk .make_decimal;
            if (std.mem.eql(u8, macro_id, "make_timestamp") or std.mem.eql(u8, macro_id, "$ion::make_timestamp")) break :blk .make_timestamp;
            if (std.mem.eql(u8, macro_id, "make_list") or std.mem.eql(u8, macro_id, "$ion::make_list")) break :blk .make_list;
            if (std.mem.eql(u8, macro_id, "make_sexp") or std.mem.eql(u8, macro_id, "$ion::make_sexp")) break :blk .make_sexp;
            if (std.mem.eql(u8, macro_id, "flatten") or std.mem.eql(u8, macro_id, "$ion::flatten")) break :blk .flatten;
            if (std.mem.eql(u8, macro_id, "make_field") or std.mem.eql(u8, macro_id, "$ion::make_field")) break :blk .make_field;
            if (std.mem.eql(u8, macro_id, "make_struct") or std.mem.eql(u8, macro_id, "$ion::make_struct")) break :blk .make_struct;
            if (std.mem.eql(u8, macro_id, "parse_ion") or std.mem.eql(u8, macro_id, "$ion::parse_ion")) break :blk .parse_ion;
            break :blk null;
        };

        // `parse_ion` is a special form: it requires a single *literal* string/clob/blob argument
        // and does not allow expression groups or nested e-expressions.
        if (kind != null and kind.? == .parse_ion) {
            const arg_v = try self.parseParseIonLiteralArg();
            try self.skipWsComments();
            if (self.eof() or self.peek().? != ')') return IonError.InvalidIon;
            self.consume(1);
            return self.expandParseIon(arg_v);
        }

        // Conformance uses `(:16 "true")` for `parse_ion` and `(:16 foo 0)` for `make_field`.
        // Attempt to parse the `parse_ion` special form first and backtrack on failure.
        if (macro_addr != null and macro_addr.? == 16 and kind != null and kind.? == .make_field) {
            const save = self.i;
            if (self.parseParseIonLiteralArg()) |arg_v| {
                try self.skipWsComments();
                if (!self.eof() and self.peek().? == ')') {
                    self.consume(1);
                    return self.expandParseIon(arg_v);
                }
            } else |_| {}
            self.i = save;
        }

        const parseOneExpr = struct {
            fn run(p: *Parser) IonError![]const value.Element {
                try p.skipWsComments();
                if (p.eof()) return IonError.Incomplete;
                const c = p.peek().?;
                if (c == ')' or c == ',') return IonError.InvalidIon;
                if (try p.hasMacroInvocationStart()) {
                    return p.parseMacroInvocationElems();
                }
                const elem = try p.parseElement(.sexp);
                const one = p.arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
                one[0] = elem;
                return one;
            }
        }.run;

        if (kind != null and kind.? == .default) {
            // Lazy semantics: if the first argument produces any values, later argument expressions
            // are not expanded/evaluated.
            try self.skipWsComments();
            if (self.eof()) return IonError.Incomplete;
            if (self.peek().? == ')') {
                self.consume(1);
                return &.{};
            }

            const first = try parseOneExpr(self);

            if (first.len != 0) {
                // Skip remaining expressions without caring whether they are valid.
                while (true) {
                    try self.skipWsComments();
                    if (self.eof()) return IonError.Incomplete;
                    const c = self.peek().?;
                    if (c == ')') {
                        self.consume(1);
                        break;
                    }
                    _ = parseOneExpr(self) catch {};
                }
                return @constCast(first);
            }

            var out = std.ArrayListUnmanaged(value.Element){};
            errdefer out.deinit(self.arena.allocator());
            while (true) {
                try self.skipWsComments();
                if (self.eof()) return IonError.Incomplete;
                const c = self.peek().?;
                if (c == ')') {
                    self.consume(1);
                    break;
                }
                const vals = try parseOneExpr(self);
                out.appendSlice(self.arena.allocator(), vals) catch return IonError.OutOfMemory;
            }
            return out.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
        }

        // Collect argument expressions as separate result slices so macros can distinguish between:
        // - an argument expression that produces multiple values (e.g. `(:: 1 2)`), and
        // - multiple argument expressions that each produce one value.
        //
        // This is required for macros like `annotate`/`make_timestamp`, where argument position and
        // multiplicity affects semantics.
        var exprs = std.ArrayListUnmanaged([]const value.Element){};
        errdefer exprs.deinit(self.arena.allocator());

        while (true) {
            try self.skipWsComments();
            if (self.eof()) return IonError.Incomplete;
            const c = self.peek().?;
            if (c == ')') {
                self.consume(1);
                break;
            }
            if (c == ',') return IonError.InvalidIon;

            const vals = try parseOneExpr(self);
            exprs.append(self.arena.allocator(), vals) catch return IonError.OutOfMemory;
        }

        if (kind != null and kind.? == .none) {
            // `(:none)` takes no arguments, even if an argument expression would expand to nothing.
            if (exprs.items.len != 0) return IonError.InvalidIon;
            return &.{};
        }

        if (kind != null and kind.? == .values) {
            var out = std.ArrayListUnmanaged(value.Element){};
            errdefer out.deinit(self.arena.allocator());
            for (exprs.items) |res| out.appendSlice(self.arena.allocator(), res) catch return IonError.OutOfMemory;
            return out.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
        }

        if (kind != null and kind.? == .repeat) {
            if (exprs.items.len != 2) return IonError.InvalidIon;
            if (exprs.items[0].len != 1) return IonError.InvalidIon;
            const count_elem = exprs.items[0][0];
            if (count_elem.value != .int) return IonError.InvalidIon;
            const count_i128: i128 = switch (count_elem.value.int) {
                .small => |v| v,
                .big => return IonError.Unsupported,
            };
            if (count_i128 < 0) return IonError.InvalidIon;
            const count: usize = @intCast(count_i128);
            const vals = exprs.items[1];
            if (count == 0 or vals.len == 0) return &.{};

            const total: usize = std.math.mul(usize, count, vals.len) catch return IonError.OutOfMemory;
            const out = self.arena.allocator().alloc(value.Element, total) catch return IonError.OutOfMemory;
            var idx: usize = 0;
            var k: usize = 0;
            while (k < count) : (k += 1) {
                @memcpy(out[idx .. idx + vals.len], vals);
                idx += vals.len;
            }
            return out;
        }

        if (kind != null and kind.? == .sum) {
            if (exprs.items.len != 2) return IonError.InvalidIon;
            if (exprs.items[0].len != 1 or exprs.items[1].len != 1) return IonError.InvalidIon;
            const a = exprs.items[0][0];
            const b = exprs.items[1][0];
            if (a.value != .int or b.value != .int) return IonError.InvalidIon;
            const ai: i128 = switch (a.value.int) {
                .small => |v| v,
                .big => return IonError.Unsupported,
            };
            const bi: i128 = switch (b.value.int) {
                .small => |v| v,
                .big => return IonError.Unsupported,
            };
            const s = std.math.add(i128, ai, bi) catch return IonError.InvalidIon;
            const out_elem = value.Element{ .annotations = &.{}, .value = .{ .int = .{ .small = s } } };
            const out = self.arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        }

        if (kind != null and kind.? == .delta) {
            var deltas = std.ArrayListUnmanaged(i128){};
            errdefer deltas.deinit(self.arena.allocator());
            for (exprs.items) |res| {
                for (res) |e| {
                    if (e.value != .int) return IonError.InvalidIon;
                    const v: i128 = switch (e.value.int) {
                        .small => |vv| vv,
                        .big => return IonError.Unsupported,
                    };
                    deltas.append(self.arena.allocator(), v) catch return IonError.OutOfMemory;
                }
            }
            if (deltas.items.len == 0) return &.{};

            const out = self.arena.allocator().alloc(value.Element, deltas.items.len) catch return IonError.OutOfMemory;
            var acc: i128 = 0;
            for (deltas.items, 0..) |d, i| {
                if (i == 0) acc = d else acc = std.math.add(i128, acc, d) catch return IonError.InvalidIon;
                out[i] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = acc } } };
            }
            return out;
        }

        if (kind != null and kind.? == .make_string) {
            var buf = std.ArrayListUnmanaged(u8){};
            errdefer buf.deinit(self.arena.allocator());
            for (exprs.items) |res| {
                for (res) |e| {
                    // Argument annotations are silently dropped.
                    switch (e.value) {
                        .string => |s| buf.appendSlice(self.arena.allocator(), s) catch return IonError.OutOfMemory,
                        .symbol => |s| {
                            const t = s.text orelse return IonError.InvalidIon;
                            buf.appendSlice(self.arena.allocator(), t) catch return IonError.OutOfMemory;
                        },
                        else => return IonError.InvalidIon,
                    }
                }
            }
            const out_str = buf.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
            const out_elem = value.Element{ .annotations = &.{}, .value = .{ .string = out_str } };
            const out = self.arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        }

        if (kind != null and kind.? == .make_symbol) {
            var buf = std.ArrayListUnmanaged(u8){};
            errdefer buf.deinit(self.arena.allocator());
            for (exprs.items) |res| {
                for (res) |e| {
                    // Argument annotations are silently dropped.
                    switch (e.value) {
                        .string => |s| buf.appendSlice(self.arena.allocator(), s) catch return IonError.OutOfMemory,
                        .symbol => |s| {
                            const t = s.text orelse return IonError.InvalidIon;
                            buf.appendSlice(self.arena.allocator(), t) catch return IonError.OutOfMemory;
                        },
                        else => return IonError.InvalidIon,
                    }
                }
            }
            const out_text = buf.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
            const out_elem = value.Element{ .annotations = &.{}, .value = .{ .symbol = value.makeSymbolId(null, out_text) } };
            const out = self.arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        }

        if (kind != null and (kind.? == .make_list or kind.? == .make_sexp)) {
            var out_items = std.ArrayListUnmanaged(value.Element){};
            errdefer out_items.deinit(self.arena.allocator());
            for (exprs.items) |res| {
                for (res) |e| {
                    // Argument annotations are silently dropped.
                    switch (e.value) {
                        .list => |items| out_items.appendSlice(self.arena.allocator(), items) catch return IonError.OutOfMemory,
                        .sexp => |items| out_items.appendSlice(self.arena.allocator(), items) catch return IonError.OutOfMemory,
                        else => return IonError.InvalidIon,
                    }
                }
            }
            const seq = out_items.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
            const out_elem = value.Element{
                .annotations = &.{},
                .value = if (kind.? == .make_list) .{ .list = seq } else .{ .sexp = seq },
            };
            const out = self.arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        }

        if (kind != null and kind.? == .flatten) {
            var out = std.ArrayListUnmanaged(value.Element){};
            errdefer out.deinit(self.arena.allocator());
            for (exprs.items) |res| {
                for (res) |e| {
                    // Argument annotations are silently dropped.
                    switch (e.value) {
                        .list => |items| out.appendSlice(self.arena.allocator(), items) catch return IonError.OutOfMemory,
                        .sexp => |items| out.appendSlice(self.arena.allocator(), items) catch return IonError.OutOfMemory,
                        else => return IonError.InvalidIon,
                    }
                }
            }
            return out.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
        }

        if (kind != null and kind.? == .meta) {
            // `meta` produces no values regardless of its argument expressions.
            return &.{};
        }

        if (kind != null and kind.? == .make_decimal) {
            if (exprs.items.len != 2) return IonError.InvalidIon;
            if (exprs.items[0].len != 1) return IonError.InvalidIon;
            if (exprs.items[1].len != 1) return IonError.InvalidIon;

            const coeff_elem = exprs.items[0][0];
            const exp_elem = exprs.items[1][0];

            if (coeff_elem.value != .int) return IonError.InvalidIon;
            if (exp_elem.value != .int) return IonError.InvalidIon;

            const exp_i128: i128 = switch (exp_elem.value.int) {
                .small => |v| v,
                .big => return IonError.Unsupported,
            };
            if (exp_i128 < std.math.minInt(i32) or exp_i128 > std.math.maxInt(i32)) return IonError.InvalidIon;

            var is_negative: bool = false;
            var magnitude: value.Int = undefined;
            switch (coeff_elem.value.int) {
                .small => |v| {
                    if (v < 0) {
                        if (v == std.math.minInt(i128)) return IonError.Unsupported;
                        is_negative = true;
                        magnitude = .{ .small = @intCast(@abs(v)) };
                    } else {
                        magnitude = .{ .small = v };
                    }
                },
                .big => |_| {
                    return IonError.Unsupported;
                },
            }

            // Negative zero is not representable as an int; ensure we don't emit it.
            const coeff_is_zero = switch (magnitude) {
                .small => |v| v == 0,
                .big => |v| v.eqlZero(),
            };
            if (coeff_is_zero) is_negative = false;

            const out_elem = value.Element{
                .annotations = &.{},
                .value = .{ .decimal = .{ .is_negative = is_negative, .coefficient = magnitude, .exponent = @intCast(exp_i128) } },
            };
            const out = self.arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        }

        if (kind != null and kind.? == .make_field) {
            if (exprs.items.len != 2) return IonError.InvalidIon;
            if (exprs.items[0].len != 1) return IonError.InvalidIon;
            if (exprs.items[1].len != 1) return IonError.InvalidIon;
            const name_elem = exprs.items[0][0];
            const val_elem = exprs.items[1][0];

            const name_sym: value.Symbol = switch (name_elem.value) {
                .string => |s| try value.makeSymbol(self.arena, s),
                .symbol => |s| s,
                else => return IonError.InvalidIon,
            };

            const fields = self.arena.allocator().alloc(value.StructField, 1) catch return IonError.OutOfMemory;
            fields[0] = .{ .name = name_sym, .value = val_elem };
            const out_elem = value.Element{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = fields } } };
            const out = self.arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        }

        if (kind != null and kind.? == .make_struct) {
            // Concatenate fields from each struct argument in order (duplicates preserved).
            var total_fields: usize = 0;
            for (exprs.items) |res| {
                for (res) |e| {
                    if (e.value != .@"struct") return IonError.InvalidIon;
                    total_fields += e.value.@"struct".fields.len;
                }
            }
            const fields = self.arena.allocator().alloc(value.StructField, total_fields) catch return IonError.OutOfMemory;
            var idx: usize = 0;
            for (exprs.items) |res| {
                for (res) |e| {
                    const st = e.value.@"struct";
                    @memcpy(fields[idx .. idx + st.fields.len], st.fields);
                    idx += st.fields.len;
                }
            }
            const out_elem = value.Element{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = fields } } };
            const out = self.arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        }

        if (kind != null and kind.? == .annotate) {
            // (annotate <annotations-expr> <value-expr>)
            if (exprs.items.len != 2) return IonError.InvalidIon;
            const ann_vals = exprs.items[0];
            const val_vals = exprs.items[1];
            if (val_vals.len != 1) return IonError.InvalidIon;

            // Convert produced text values into annotations. The conformance suite accepts:
            // - strings (treated as annotation symbol text)
            // - symbols (including unknown text)
            var anns = std.ArrayListUnmanaged(value.Symbol){};
            errdefer anns.deinit(self.arena.allocator());
            for (ann_vals) |e| {
                switch (e.value) {
                    .string => |s| anns.append(self.arena.allocator(), try value.makeSymbol(self.arena, s)) catch return IonError.OutOfMemory,
                    .symbol => |s| anns.append(self.arena.allocator(), s) catch return IonError.OutOfMemory,
                    else => return IonError.InvalidIon,
                }
            }

            const v = val_vals[0];
            var all = std.ArrayListUnmanaged(value.Symbol){};
            errdefer all.deinit(self.arena.allocator());
            all.appendSlice(self.arena.allocator(), anns.items) catch return IonError.OutOfMemory;
            all.appendSlice(self.arena.allocator(), v.annotations) catch return IonError.OutOfMemory;

            const out_elem = value.Element{
                .annotations = all.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory,
                .value = v.value,
            };
            const out = self.arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        }

        if (kind != null and kind.? == .make_timestamp) {
            // (make_timestamp <year> [<month> [<day> [<hour> <minute> [<seconds> [<offset>]]]]])
            //
            // Each argument is an expression; an elided expression group `(::)` is treated as absent.
            if (exprs.items.len < 1 or exprs.items.len > 7) return IonError.InvalidIon;

            const getOptSingle = struct {
                fn run(expr: []const value.Element) IonError!?value.Element {
                    if (expr.len == 0) return null;
                    if (expr.len != 1) return IonError.InvalidIon;
                    return expr[0];
                }
            }.run;

            const year_elem = (try getOptSingle(exprs.items[0])) orelse return IonError.InvalidIon;
            if (year_elem.value != .int) return IonError.InvalidIon;
            const year_i128: i128 = switch (year_elem.value.int) {
                .small => |v| v,
                .big => return IonError.Unsupported,
            };
            if (year_i128 < 1 or year_i128 > 9999) return IonError.InvalidIon;
            const year: i32 = @intCast(year_i128);

            const month_elem: ?value.Element = if (exprs.items.len >= 2) try getOptSingle(exprs.items[1]) else null;
            const day_elem: ?value.Element = if (exprs.items.len >= 3) try getOptSingle(exprs.items[2]) else null;
            const hour_elem: ?value.Element = if (exprs.items.len >= 4) try getOptSingle(exprs.items[3]) else null;
            const minute_elem: ?value.Element = if (exprs.items.len >= 5) try getOptSingle(exprs.items[4]) else null;
            const seconds_elem: ?value.Element = if (exprs.items.len >= 6) try getOptSingle(exprs.items[5]) else null;
            const offset_elem: ?value.Element = if (exprs.items.len >= 7) try getOptSingle(exprs.items[6]) else null;

            if (day_elem != null and month_elem == null) return IonError.InvalidIon;
            if (hour_elem != null and (day_elem == null or month_elem == null)) return IonError.InvalidIon;
            if (minute_elem != null and hour_elem == null) return IonError.InvalidIon;
            if (seconds_elem != null and minute_elem == null) return IonError.InvalidIon;
            if (offset_elem != null and minute_elem == null) return IonError.InvalidIon;

            var ts: value.Timestamp = .{
                .year = year,
                .month = null,
                .day = null,
                .hour = null,
                .minute = null,
                .second = null,
                .fractional = null,
                .offset_minutes = null,
                .precision = .year,
            };

            if (month_elem) |me| {
                if (me.value != .int) return IonError.InvalidIon;
                const m_i128: i128 = switch (me.value.int) {
                    .small => |v| v,
                    .big => return IonError.Unsupported,
                };
                if (m_i128 < 1 or m_i128 > 12) return IonError.InvalidIon;
                ts.month = @intCast(m_i128);
                ts.precision = .month;
            }

            if (day_elem) |de| {
                if (de.value != .int) return IonError.InvalidIon;
                const d_i128: i128 = switch (de.value.int) {
                    .small => |v| v,
                    .big => return IonError.Unsupported,
                };
                if (d_i128 < 1) return IonError.InvalidIon;
                const max_day: i128 = @intCast(daysInMonth(year, ts.month orelse return IonError.InvalidIon));
                if (d_i128 > max_day) return IonError.InvalidIon;
                ts.day = @intCast(d_i128);
                ts.precision = .day;
            }

            if (hour_elem) |he| {
                if (minute_elem == null) return IonError.InvalidIon;
                if (he.value != .int) return IonError.InvalidIon;
                const h_i128: i128 = switch (he.value.int) {
                    .small => |v| v,
                    .big => return IonError.Unsupported,
                };
                if (h_i128 < 0 or h_i128 >= 24) return IonError.InvalidIon;
                ts.hour = @intCast(h_i128);

                const mn = minute_elem.?;
                if (mn.value != .int) return IonError.InvalidIon;
                const min_i128: i128 = switch (mn.value.int) {
                    .small => |v| v,
                    .big => return IonError.Unsupported,
                };
                if (min_i128 < 0 or min_i128 >= 60) return IonError.InvalidIon;
                ts.minute = @intCast(min_i128);
                ts.precision = .minute;

                // Seconds are optional, but if absent the offset still defaults to unknown (-00:00).
                if (seconds_elem) |se| {
                    switch (se.value) {
                        .int => |ii| {
                            const s_i128: i128 = switch (ii) {
                                .small => |v| v,
                                .big => return IonError.Unsupported,
                            };
                            if (s_i128 < 0 or s_i128 >= 60) return IonError.InvalidIon;
                            ts.second = @intCast(s_i128);
                            ts.precision = .second;
                        },
                        .decimal => |d| {
                            // Accept -0 as zero.
                            const coeff_is_zero = switch (d.coefficient) {
                                .small => |v| v == 0,
                                .big => |v| v.eqlZero(),
                            };
                            if (d.is_negative and !coeff_is_zero) return IonError.InvalidIon;

                            const exp: i32 = d.exponent;
                            const coeff_u128: u128 = switch (d.coefficient) {
                                .small => |v| if (v < 0) return IonError.InvalidIon else @intCast(v),
                                .big => return IonError.Unsupported,
                            };

                            if (exp >= 0) {
                                var scaled: u128 = coeff_u128;
                                var k: u32 = @intCast(exp);
                                while (k != 0) : (k -= 1) {
                                    scaled = std.math.mul(u128, scaled, 10) catch return IonError.InvalidIon;
                                }
                                if (scaled >= 60) return IonError.InvalidIon;
                                ts.second = @intCast(scaled);
                                ts.precision = .second;
                            } else {
                                const digits: u32 = @intCast(-exp);
                                var pow10: u128 = 1;
                                var k: u32 = digits;
                                while (k != 0) : (k -= 1) {
                                    pow10 = std.math.mul(u128, pow10, 10) catch return IonError.InvalidIon;
                                }
                                const sec_u128: u128 = coeff_u128 / pow10;
                                const frac_u128: u128 = coeff_u128 % pow10;
                                if (sec_u128 >= 60) return IonError.InvalidIon;
                                ts.second = @intCast(sec_u128);
                                ts.precision = .second;
                                if (frac_u128 != 0) {
                                    // Preserve the original fractional precision by keeping the exponent as-is.
                                    const frac_coeff: value.Int = .{ .small = @intCast(frac_u128) };
                                    ts.fractional = .{ .is_negative = false, .coefficient = frac_coeff, .exponent = exp };
                                    ts.precision = .fractional;
                                } else if (exp < 0 and (coeff_u128 % pow10 == 0) and (coeff_u128 != 0)) {
                                    // Exact integer value but written with fractional digits (e.g. 6.0).
                                    // The conformance suite treats 60.0 as invalid, but 6.0 should still
                                    // denote second precision with no fractional component.
                                }
                            }
                        },
                        else => return IonError.InvalidIon,
                    }
                }

                // Offset: when absent, indicates unknown offset for time-precision timestamps.
                if (offset_elem) |oe| {
                    if (oe.value != .int) return IonError.InvalidIon;
                    const off_i128: i128 = switch (oe.value.int) {
                        .small => |v| v,
                        .big => return IonError.Unsupported,
                    };
                    if (off_i128 <= -1440 or off_i128 >= 1440) return IonError.InvalidIon;
                    const off_i16: i16 = @intCast(off_i128);
                    ts.offset_minutes = off_i16;

                    // Reject offsets that would push the UTC year out of [0001, 9999].
                    if (ts.month != null and ts.day != null) {
                        const days_before = blk: {
                            var doy: i32 = 0;
                            var m: u8 = 1;
                            while (m < ts.month.?) : (m += 1) {
                                doy += @intCast(daysInMonth(year, m));
                            }
                            doy += (@as(i32, @intCast(ts.day.?)) - 1);
                            break :blk doy;
                        };
                        const local_minutes: i32 = days_before * 1440 + @as(i32, @intCast(ts.hour.?)) * 60 + @as(i32, @intCast(ts.minute.?));
                        const days_in_year: i32 = if (isLeapYear(year)) 366 else 365;
                        const total_minutes_in_year: i32 = days_in_year * 1440;
                        if (year == 1 and off_i16 > 0 and off_i16 > local_minutes) return IonError.InvalidIon;
                        if (year == 9999 and off_i16 < 0 and local_minutes + @as(i32, @intCast(-off_i16)) >= total_minutes_in_year) return IonError.InvalidIon;
                    }
                } else {
                    ts.offset_minutes = null;
                }
            }

            const out_elem = value.Element{ .annotations = &.{}, .value = .{ .timestamp = ts } };
            const out = self.arena.allocator().alloc(value.Element, 1) catch return IonError.OutOfMemory;
            out[0] = out_elem;
            return out;
        }

        // User macros (conformance `(mactab ...)`) are only callable by name/address, not by `$ion::...`.
        if (self.mactab) |tab| {
            if (macro_addr) |addr| {
                if (tab.macroForAddress(addr)) |m| return tdl_eval.expandUserMacro(self.arena, tab, m, exprs.items);
            } else {
                if (tab.macroForName(macro_id)) |m| return tdl_eval.expandUserMacro(self.arena, tab, m, exprs.items);
            }
        }

        // `if_*`, `for`, and `literal` are special forms in templates and are not legal as e-expressions.
        if (std.mem.eql(u8, macro_id, "if_none") or std.mem.eql(u8, macro_id, "$ion::if_none") or
            std.mem.eql(u8, macro_id, "if_some") or std.mem.eql(u8, macro_id, "$ion::if_some") or
            std.mem.eql(u8, macro_id, "if_single") or std.mem.eql(u8, macro_id, "$ion::if_single") or
            std.mem.eql(u8, macro_id, "if_multi") or std.mem.eql(u8, macro_id, "$ion::if_multi") or
            std.mem.eql(u8, macro_id, "for") or std.mem.eql(u8, macro_id, "$ion::for") or
            std.mem.eql(u8, macro_id, "literal") or std.mem.eql(u8, macro_id, "$ion::literal"))
        {
            return IonError.InvalidIon;
        }

        return IonError.Unsupported;
    }

    fn parseParseIonLiteralArg(self: *Parser) IonError!value.Value {
        // Disable macro invocations while parsing the argument so `(:: ...)` and `(:values ...)`
        // are rejected structurally (rather than being expanded and potentially accepted).
        const saved_ver = self.version;
        self.version = .v1_0;
        defer self.version = saved_ver;

        try self.skipWsComments();
        if (self.eof()) return IonError.Incomplete;
        if (self.peek().? == ')') return IonError.InvalidIon;

        const elem = try self.parseElement(.sexp);
        if (elem.annotations.len != 0) return IonError.InvalidIon;
        return switch (elem.value) {
            .string, .clob, .blob => elem.value,
            else => IonError.InvalidIon,
        };
    }

    fn expandParseIon(self: *Parser, v: value.Value) IonError![]value.Element {
        const bytes: []const u8 = switch (v) {
            .string => |s| s,
            .clob => |b| b,
            .blob => |b| b,
            else => return IonError.InvalidIon,
        };

        // Parse the embedded Ion stream in a fresh encoding context (no inherited symbols/macros).
        // System values in the embedded stream still apply as normal unless `$ion_literal` is used.
        if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x00 and bytes[3] == 0xEA) {
            return ion.binary.parseTopLevel(self.arena, bytes);
        }
        if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x01 and bytes[3] == 0xEA) {
            return ion.binary11.parseTopLevelWithMacroTable(self.arena, bytes, null);
        }
        return parseTopLevelWithMacroTable(self.arena, bytes, null);
    }

    fn eof(self: *const Parser) bool {
        return self.i >= self.input.len;
    }

    fn peek(self: *const Parser) ?u8 {
        if (self.eof()) return null;
        return self.input[self.i];
    }

    fn startsWith(self: *const Parser, s: []const u8) bool {
        return self.i + s.len <= self.input.len and std.mem.eql(u8, self.input[self.i .. self.i + s.len], s);
    }

    fn consume(self: *Parser, n: usize) void {
        self.i += n;
    }

    fn skipWsComments(self: *Parser) IonError!void {
        while (true) {
            while (self.i < self.input.len) : (self.i += 1) {
                const c = self.input[self.i];
                if (c != ' ' and c != '\t' and c != '\n' and c != '\r' and c != 0x0B and c != 0x0C) break;
            }
            if (self.startsWith("//")) {
                self.consume(2);
                while (self.i < self.input.len and self.input[self.i] != '\n' and self.input[self.i] != '\r') : (self.i += 1) {}
                continue;
            }
            if (self.startsWith("/*")) {
                try self.consumeBlockComment();
                continue;
            }
            break;
        }
    }

    fn skipWsOnly(self: *Parser) void {
        while (self.i < self.input.len) : (self.i += 1) {
            const c = self.input[self.i];
            if (c != ' ' and c != '\t' and c != '\n' and c != '\r' and c != 0x0B and c != 0x0C) break;
        }
    }

    fn consumeBlockComment(self: *Parser) IonError!void {
        // Support nested block comments.
        if (!self.startsWith("/*")) return IonError.InvalidIon;
        self.consume(2);
        var depth: usize = 1;
        while (self.i < self.input.len) : (self.i += 1) {
            if (self.startsWith("/*")) {
                depth += 1;
                self.consume(2);
                continue;
            }
            if (self.startsWith("*/")) {
                depth -= 1;
                self.consume(2);
                if (depth == 0) return;
                continue;
            }
        }
        return IonError.Incomplete;
    }

    const Context = enum { top, list, sexp, @"struct", clob };

    fn parseElement(self: *Parser, ctx: Context) IonError!value.Element {
        var ann = std.ArrayListUnmanaged(value.Symbol){};
        errdefer ann.deinit(self.arena.allocator());

        while (true) {
            const save = self.i;
            // Operator symbols are allowed as values in S-expressions, but annotations always use
            // the regular symbol token syntax and must be quoted if they are operators.
            const sym = self.parseSymbolToken(.top) catch {
                self.i = save;
                break;
            };
            try self.skipWsComments();
            if (!self.startsWith("::")) {
                self.i = save;
                break;
            }
            if (sym.text == null and sym.sid == null) return IonError.InvalidIon;
            self.consume(2);
            ann.append(self.arena.allocator(), sym) catch return IonError.OutOfMemory;
            try self.skipWsComments();
        }

        const annotations = ann.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
        const v = try self.parseValue(ctx);

        return .{ .annotations = annotations, .value = v };
    }

    fn parseValue(self: *Parser, ctx: Context) IonError!value.Value {
        try self.skipWsComments();
        if (self.eof()) return IonError.Incomplete;

        // Conformance DSL / TDL: allow `.name` and `%name` tokens as symbol identifiers inside
        // s-expressions. These are not valid Ion tokens, so keep this scoped to DSL mode.
        if (self.conformance_dsl_mode and ctx == .sexp and (self.peek().? == '.' or self.peek().? == '%')) {
            if (self.i + 1 < self.input.len and isIdentStart(self.input[self.i + 1])) {
                const start = self.i;
                self.i += 2; // prefix + first ident char
                // Allow `:` here so conformance DSL can represent qualified names like
                // `.$ion::make_symbol` and `.$ion::if_some` as a single token.
                while (!self.eof()) : (self.i += 1) {
                    const c = self.peek().?;
                    if (isIdentContConformanceDsl(c) or c == ':') continue;
                    break;
                }
                const tok = self.input[start..self.i];
                return value.Value{ .symbol = try value.makeSymbol(self.arena, tok) };
            }
        }

        // Special float keywords that begin with '+'/'-'
        if (self.startsWith("+inf") and isTokenBoundary(self.input, self.i + 4)) {
            self.consume(4);
            return value.Value{ .float = std.math.inf(f64) };
        }
        if (self.startsWith("-inf") and isTokenBoundary(self.input, self.i + 4)) {
            self.consume(4);
            return value.Value{ .float = -std.math.inf(f64) };
        }

        // Containers
        if (self.startsWith("[")) return self.parseList();
        if (self.startsWith("(")) return self.parseSExp();
        if (self.startsWith("{{")) return self.parseLob();
        if (self.startsWith("{")) return self.parseStruct();

        // Strings/symbols
        if (self.startsWith("\"")) {
            const text_bytes = if (self.concat_string_literals) try self.parseStringConcat(false) else try self.parseShortString(false);
            return value.Value{ .string = text_bytes };
        }
        if (self.startsWith("'''")) {
            const text_bytes = if (self.concat_string_literals) try self.parseLongStringConcat(false) else try self.parseLongString(false);
            return value.Value{ .string = text_bytes };
        }
        if (self.startsWith("'")) return value.Value{ .symbol = try self.parseQuotedSymbol() };

        // Keywords / identifiers / numbers / timestamps / nulls
        // Symbol ID like $10 (must be handled before identifier parsing, since '$' can start both)
        if (self.peek().? == '$' and self.i + 1 < self.input.len and std.ascii.isDigit(self.input[self.i + 1])) {
            return value.Value{ .symbol = try self.parseSymbolId() };
        }

        // Try null/boolean/specials/identifier first.
        if (isIdentStart(self.peek().?)) {
            const token = try self.parseIdentifierToken();
            if (std.mem.eql(u8, token, "true")) return value.Value{ .bool = true };
            if (std.mem.eql(u8, token, "false")) return value.Value{ .bool = false };
            if (std.mem.eql(u8, token, "nan")) return value.Value{ .float = std.math.nan(f64) };

            if (std.mem.eql(u8, token, "null")) {
                if (!self.eof() and self.peek().? == '.') {
                    self.consume(1);
                    const typed = try self.parseIdentifierToken();
                    const t = parseNullType(typed) orelse return IonError.InvalidIon;
                    return value.Value{ .null = t };
                }
                return value.Value{ .null = .null };
            }

            // Timestamp can start with digits, so only identifiers here.
            return value.Value{ .symbol = try value.makeSymbol(self.arena, token) };
        }

        // Numbers / timestamps start with '-' or digit
        if (self.peek().? == '-' or std.ascii.isDigit(self.peek().?)) {
            // In sexp, '-' is numeric only if followed by digit.
            if (ctx == .sexp and self.peek().? == '-' and !(self.i + 1 < self.input.len and std.ascii.isDigit(self.input[self.i + 1]))) {
                const op = try self.parseOperatorToken();
                return value.Value{ .symbol = try value.makeSymbol(self.arena, op) };
            }

            // Timestamp always begins with YYYY-...
            if (looksLikeTimestamp(self.input[self.i..])) {
                const ts = try self.parseTimestamp();
                // After a timestamp token, we require a token boundary or the start of a comment.
                if (!self.eof() and !isTokenBoundary(self.input, self.i) and !self.startsWith("//") and !self.startsWith("/*")) {
                    return IonError.InvalidIon;
                }
                return value.Value{ .timestamp = ts };
            }

            return try self.parseNumber();
        }

        // Sexp-only operator symbols.
        if (ctx == .sexp and isOperatorStart(self.peek().?)) {
            const op = try self.parseOperatorToken();
            return value.Value{ .symbol = try value.makeSymbol(self.arena, op) };
        }

        return IonError.InvalidIon;
    }

    fn parseList(self: *Parser) IonError!value.Value {
        if (!self.startsWith("[")) return IonError.InvalidIon;
        self.consume(1);
        try self.skipWsComments();
        var elems = std.ArrayListUnmanaged(value.Element){};
        errdefer elems.deinit(self.arena.allocator());
        var expect_value = true;
        while (true) {
            try self.skipWsComments();
            if (self.eof()) return IonError.Incomplete;
            const c = self.peek().?;
            if (c == ']') {
                self.consume(1);
                break;
            }
            if (c == ',') {
                // Commas are allowed only after a value (including as a trailing comma).
                if (expect_value) return IonError.InvalidIon;
                self.consume(1);
                expect_value = true;
                continue;
            }
            if (!expect_value) return IonError.InvalidIon;

            if (try self.hasMacroInvocationStart()) {
                const expanded = try self.parseMacroInvocationElems();
                elems.appendSlice(self.arena.allocator(), expanded) catch return IonError.OutOfMemory;
            } else {
                const elem = try self.parseElement(.list);
                elems.append(self.arena.allocator(), elem) catch return IonError.OutOfMemory;
            }
            expect_value = false;
        }
        return value.Value{ .list = elems.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory };
    }

    fn parseSExp(self: *Parser) IonError!value.Value {
        if (!self.startsWith("(")) return IonError.InvalidIon;
        self.consume(1);
        try self.skipWsComments();
        var elems = std.ArrayListUnmanaged(value.Element){};
        errdefer elems.deinit(self.arena.allocator());
        while (true) {
            try self.skipWsComments();
            if (self.eof()) return IonError.Incomplete;
            const c = self.peek().?;
            if (c == ')') {
                self.consume(1);
                break;
            }
            if (c == ',') return IonError.InvalidIon;
            if (try self.hasMacroInvocationStart()) {
                const expanded = try self.parseMacroInvocationElems();
                elems.appendSlice(self.arena.allocator(), expanded) catch return IonError.OutOfMemory;
            } else {
                const elem = try self.parseElement(.sexp);
                elems.append(self.arena.allocator(), elem) catch return IonError.OutOfMemory;
            }
        }
        return value.Value{ .sexp = elems.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory };
    }

    fn parseStruct(self: *Parser) IonError!value.Value {
        if (!self.startsWith("{")) return IonError.InvalidIon;
        self.consume(1);
        try self.skipWsComments();
        var fields = std.ArrayListUnmanaged(value.StructField){};
        errdefer fields.deinit(self.arena.allocator());
        while (true) {
            try self.skipWsComments();
            if (self.eof()) return IonError.Incomplete;
            const c = self.peek().?;
            if (c == '}') {
                self.consume(1);
                break;
            }

            if (try self.hasMacroInvocationStart()) {
                const expanded = try self.parseMacroInvocationElems();
                for (expanded) |e| {
                    if (e.annotations.len != 0) return IonError.InvalidIon;
                    switch (e.value) {
                        .@"struct" => |st| {
                            fields.appendSlice(self.arena.allocator(), st.fields) catch return IonError.OutOfMemory;
                        },
                        else => return IonError.InvalidIon,
                    }
                }
            } else {
                const name = try self.parseFieldName();
                try self.skipWsComments();
                if (self.eof() or self.peek().? != ':') return IonError.InvalidIon;
                self.consume(1);
                try self.skipWsComments();
                if (try self.hasMacroInvocationStart()) {
                    const expanded = try self.parseMacroInvocationElems();
                    for (expanded) |e| {
                        fields.append(self.arena.allocator(), .{ .name = name, .value = e }) catch return IonError.OutOfMemory;
                    }
                } else {
                    const v = try self.parseElement(.@"struct");
                    fields.append(self.arena.allocator(), .{ .name = name, .value = v }) catch return IonError.OutOfMemory;
                }
            }

            // After a field (or injected fields), the next token must be either ',' or '}'.
            // Whitespace is not a valid separator between fields.
            try self.skipWsComments();
            if (self.eof()) return IonError.Incomplete;
            const sep = self.peek().?;
            if (sep == ',') {
                self.consume(1);
                continue;
            }
            if (sep == '}') {
                self.consume(1);
                break;
            }
            return IonError.InvalidIon;
        }
        return value.Value{ .@"struct" = .{ .fields = fields.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory } };
    }

    fn parseFieldName(self: *Parser) IonError!value.Symbol {
        try self.skipWsComments();
        // Long strings start with three quotes, which also matches the quoted symbol prefix.
        // Check for long strings first.
        if (self.startsWith("'''")) {
            const text_bytes = if (self.concat_string_literals) try self.parseLongStringConcat(false) else try self.parseLongString(false);
            return value.makeSymbolId(null, text_bytes);
        }
        if (self.startsWith("'")) return self.parseQuotedSymbol();
        if (self.startsWith("\"")) {
            const text_bytes = if (self.concat_string_literals) try self.parseStringConcat(false) else try self.parseShortString(false);
            return value.makeSymbolId(null, text_bytes);
        }
        if (self.peek() == null) return IonError.Incomplete;
        if (self.peek().? == '$') {
            if (self.i + 1 < self.input.len and std.ascii.isDigit(self.input[self.i + 1])) {
                const s = try self.parseSymbolId();
                return s;
            }
        }
        if (isIdentStart(self.peek().?)) {
            const token = try self.parseIdentifierToken();
            if (isReservedSymbolIdentifier(token)) return IonError.InvalidIon;
            return try value.makeSymbol(self.arena, token);
        }
        return IonError.InvalidIon;
    }

    fn parseLob(self: *Parser) IonError!value.Value {
        if (!self.startsWith("{{")) return IonError.InvalidIon;
        self.consume(2);
        // Comments are not allowed inside LOB bodies in the ion-tests corpus.
        self.skipWsOnly();
        if (self.startsWith("}}")) {
            self.consume(2);
            return value.Value{ .blob = &.{} };
        }
        if (self.startsWith("\"")) {
            // clob with a short string literal: must be a single segment.
            const seg = try self.parseShortString(true);
            self.skipWsOnly();
            if (!self.startsWith("}}")) return IonError.InvalidIon;
            self.consume(2);
            return value.Value{ .clob = seg };
        }
        if (self.startsWith("'''")) {
            // clob: concatenation of long string segments only (no short string segments).
            var buf = std.ArrayListUnmanaged(u8){};
            errdefer buf.deinit(self.arena.allocator());
            while (true) {
                self.skipWsOnly();
                if (self.startsWith("}}")) break;
                if (!self.startsWith("'''")) return IonError.InvalidIon;
                const seg = try self.parseLongString(true);
                buf.appendSlice(self.arena.allocator(), seg) catch return IonError.OutOfMemory;
                self.skipWsOnly();
            }
            if (!self.startsWith("}}")) return IonError.Incomplete;
            self.consume(2);
            const owned = buf.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
            return value.Value{ .clob = owned };
        }

        // blob base64
        const start = self.i;
        while (!self.eof() and !self.startsWith("}}")) : (self.i += 1) {}
        if (self.eof()) return IonError.Incomplete;
        const raw = self.input[start..self.i];
        self.consume(2);

        // Ion blob base64 may contain arbitrary whitespace; strip it and pad to a multiple of 4.
        var filtered = std.ArrayListUnmanaged(u8){};
        defer filtered.deinit(self.arena.allocator());
        for (raw) |c| {
            if (c == ' ' or c == '\t' or c == '\r' or c == '\n') continue;
            filtered.append(self.arena.allocator(), c) catch return IonError.OutOfMemory;
        }
        const rem = filtered.items.len % 4;
        if (rem == 1) return IonError.InvalidIon;
        if (rem == 2) {
            filtered.appendSlice(self.arena.allocator(), "==") catch return IonError.OutOfMemory;
        } else if (rem == 3) {
            filtered.append(self.arena.allocator(), '=') catch return IonError.OutOfMemory;
        }

        const decoder = std.base64.standard.Decoder;
        const out_len = decoder.calcSizeForSlice(filtered.items) catch return IonError.InvalidIon;
        const out = self.arena.allocator().alloc(u8, out_len) catch return IonError.OutOfMemory;
        decoder.decode(out, filtered.items) catch return IonError.InvalidIon;
        // arena owns out
        return value.Value{ .blob = out };
    }

    fn parseQuotedSymbolBytesAsString(self: *Parser) IonError![]const u8 {
        // For clobs, allow {{'...'}} treating like a string segment.
        const sym = try self.parseQuotedSymbol();
        return sym.text orelse "";
    }

    fn parseStringConcat(self: *Parser, as_bytes: bool) IonError![]const u8 {
        var buf = std.ArrayListUnmanaged(u8){};
        errdefer buf.deinit(self.arena.allocator());
        while (true) {
            if (!self.startsWith("\"")) break;
            const seg = try self.parseShortString(as_bytes);
            buf.appendSlice(self.arena.allocator(), seg) catch return IonError.OutOfMemory;
            const save = self.i;
            try self.skipWsComments();
            // Another adjacent string literal?
            if (!self.startsWith("\"")) {
                self.i = save;
                break;
            }
        }
        return buf.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
    }

    fn parseLongStringConcat(self: *Parser, as_bytes: bool) IonError![]const u8 {
        var buf = std.ArrayListUnmanaged(u8){};
        errdefer buf.deinit(self.arena.allocator());
        while (true) {
            if (!self.startsWith("'''")) break;
            const seg = try self.parseLongString(as_bytes);
            buf.appendSlice(self.arena.allocator(), seg) catch return IonError.OutOfMemory;
            const save = self.i;
            try self.skipWsComments();
            if (!self.startsWith("'''")) {
                self.i = save;
                break;
            }
        }
        return buf.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
    }

    fn parseShortString(self: *Parser, as_bytes: bool) IonError![]const u8 {
        if (!self.startsWith("\"")) return IonError.InvalidIon;
        self.consume(1);
        var buf = std.ArrayListUnmanaged(u8){};
        errdefer buf.deinit(self.arena.allocator());
        while (true) {
            if (self.eof()) return IonError.Incomplete;
            const c = self.peek().?;
            if (c == '"') {
                self.consume(1);
                break;
            }
            if (c == '\\') {
                self.consume(1);
                try decodeEscape(self, &buf, as_bytes);
                continue;
            }
            // Control characters are invalid in short strings.
            if (c < 0x20 and c != '\t' and c != 0x0B and c != 0x0C) return IonError.InvalidIon;
            // CLOBs are byte strings and are limited to ASCII in the ion-tests corpus.
            if (as_bytes and c >= 0x80) return IonError.InvalidIon;
            self.consume(1);
            buf.append(self.arena.allocator(), c) catch return IonError.OutOfMemory;
        }
        const out = buf.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
        if (!as_bytes) {
            // validate UTF-8
            if (!std.unicode.utf8ValidateSlice(out)) return IonError.InvalidIon;
        }
        return out;
    }

    fn parseLongString(self: *Parser, as_bytes: bool) IonError![]const u8 {
        if (!self.startsWith("'''")) return IonError.InvalidIon;
        self.consume(3);
        var buf = std.ArrayListUnmanaged(u8){};
        errdefer buf.deinit(self.arena.allocator());
        while (true) {
            if (self.eof()) return IonError.Incomplete;
            if (self.startsWith("'''")) {
                self.consume(3);
                break;
            }
            const c = self.peek().?;
            if (!as_bytes and c < 0x20 and c != '\n' and c != '\t' and c != '\r' and c != 0x0B and c != 0x0C) return IonError.InvalidIon;
            if (as_bytes and c >= 0x80) return IonError.InvalidIon;
            // Normalize CR and CRLF to LF in long strings/clobs.
            if (c == '\r') {
                self.consume(1);
                if (!self.eof() and self.peek().? == '\n') self.consume(1);
                buf.append(self.arena.allocator(), '\n') catch return IonError.OutOfMemory;
                continue;
            }
            if (c == '\\') {
                // line continuation: backslash followed by newline (CRLF/LF/CR) is removed.
                if (self.i + 1 < self.input.len and (self.input[self.i + 1] == '\n' or self.input[self.i + 1] == '\r')) {
                    self.consume(1);
                    if (self.startsWith("\r\n")) self.consume(2) else self.consume(1);
                    continue;
                }
                self.consume(1);
                try decodeEscape(self, &buf, as_bytes);
                continue;
            }
            self.consume(1);
            buf.append(self.arena.allocator(), c) catch return IonError.OutOfMemory;
        }
        const out = buf.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
        if (!as_bytes) {
            if (!std.unicode.utf8ValidateSlice(out)) return IonError.InvalidIon;
        }
        return out;
    }

    fn parseQuotedSymbol(self: *Parser) IonError!value.Symbol {
        if (!self.startsWith("'")) return IonError.InvalidIon;
        self.consume(1);
        var buf = std.ArrayListUnmanaged(u8){};
        errdefer buf.deinit(self.arena.allocator());
        while (true) {
            if (self.eof()) return IonError.Incomplete;
            const c = self.peek().?;
            if (c == '\'') {
                self.consume(1);
                break;
            }
            if (c == '\\') {
                self.consume(1);
                try decodeEscape(self, &buf, false);
                continue;
            }
            // ion-tests allows certain ASCII whitespace/control characters directly in quoted symbols.
            if (c < 0x20 and c != '\t' and c != 0x0B and c != 0x0C) return IonError.InvalidIon;
            self.consume(1);
            buf.append(self.arena.allocator(), c) catch return IonError.OutOfMemory;
        }
        const text = buf.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
        if (!std.unicode.utf8ValidateSlice(text)) return IonError.InvalidIon;
        return value.makeSymbolId(null, text);
    }

    fn parseSymbolId(self: *Parser) IonError!value.Symbol {
        if (self.peek() != '$') return IonError.InvalidIon;
        self.consume(1);
        if (self.eof()) return IonError.Incomplete;
        const start = self.i;
        while (!self.eof() and std.ascii.isDigit(self.peek().?)) : (self.i += 1) {}
        if (self.i == start) return IonError.InvalidIon;
        const digits = self.input[start..self.i];
        const sid = std.fmt.parseInt(u32, digits, 10) catch return IonError.InvalidIon;
        if (sid == 0) return value.unknownSymbol();
        const slot = self.st.slotForSid(sid) orelse return IonError.InvalidIon;
        if (slot) |txt| return value.makeSymbolId(sid, txt);
        return value.makeSymbolId(sid, null);
    }

    fn parseIdentifierToken(self: *Parser) IonError![]const u8 {
        const start = self.i;
        if (self.eof()) return IonError.Incomplete;
        if (!isIdentStart(self.peek().?)) return IonError.InvalidIon;
        self.i += 1;
        while (!self.eof() and (if (self.conformance_dsl_mode) isIdentContConformanceDsl(self.peek().?) else isIdentCont(self.peek().?))) : (self.i += 1) {}
        return self.input[start..self.i];
    }

    fn parseOperatorToken(self: *Parser) IonError![]const u8 {
        const start = self.i;
        while (!self.eof() and isOperatorChar(self.peek().?)) : (self.i += 1) {}
        if (self.i == start) return IonError.InvalidIon;
        return self.input[start..self.i];
    }

    fn parseSymbolToken(self: *Parser, ctx: Context) IonError!value.Symbol {
        try self.skipWsComments();
        if (self.eof()) return IonError.Incomplete;
        if (self.startsWith("'")) return self.parseQuotedSymbol();
        if (self.peek().? == '$') {
            // Either symbol id or identifier starting with $.
            // Peek next char to decide: $ followed by digit => id, else identifier.
            if (self.i + 1 < self.input.len and std.ascii.isDigit(self.input[self.i + 1])) {
                return self.parseSymbolId();
            }
        }
        if (self.conformance_dsl_mode and ctx == .sexp and (self.peek().? == '.' or self.peek().? == '%')) {
            // In s-expressions, treat `.name` and `%name` as identifiers (TDL-ish) rather than as
            // operator tokens. This is required for parsing conformance macro definitions like:
            //   (macro foo () (.literal 1))
            // and variable expansions like:
            //   (macro foo (x) (%x))
            if (self.i + 1 < self.input.len and isIdentStart(self.input[self.i + 1])) {
                const start = self.i;
                self.i += 2; // prefix + first ident char
                while (!self.eof() and isIdentContConformanceDsl(self.peek().?)) : (self.i += 1) {}
                const tok = self.input[start..self.i];
                return try value.makeSymbol(self.arena, tok);
            }
        }
        if (isIdentStart(self.peek().?)) {
            const tok = try self.parseIdentifierToken();
            if (isReservedSymbolIdentifier(tok)) return IonError.InvalidIon;
            return try value.makeSymbol(self.arena, tok);
        }
        if (ctx == .sexp and isOperatorStart(self.peek().?)) {
            const op = try self.parseOperatorToken();
            return try value.makeSymbol(self.arena, op);
        }
        return IonError.InvalidIon;
    }

    fn parseNumber(self: *Parser) IonError!value.Value {
        // No leading '+'. '-' allowed.
        const start = self.i;
        if (self.peek().? == '+') return IonError.InvalidIon;

        // Hex int 0x...
        var neg = false;
        if (self.peek().? == '-') {
            neg = true;
            self.i += 1;
        }
        if (self.startsWith("0x") or self.startsWith("0X")) {
            self.consume(2);
            const digits_start = self.i;
            while (!self.eof() and (std.ascii.isHex(self.peek().?) or self.peek().? == '_')) : (self.i += 1) {}
            if (!self.eof() and !isTokenBoundary(self.input, self.i) and !self.startsWith("//") and !self.startsWith("/*")) {
                return IonError.InvalidIon;
            }
            const raw = self.input[digits_start..self.i];
            try validateUnderscoresHex(raw);
            const digits = try stripUnderscores(self.arena.gpa, raw);
            defer self.arena.gpa.free(digits);
            const mag_u128 = std.fmt.parseInt(u128, digits, 16) catch |e| switch (e) {
                error.Overflow => null,
                else => return IonError.InvalidIon,
            };
            if (mag_u128) |mag| {
                if (mag > @as(u128, std.math.maxInt(i128))) {
                    // Fall through to BigInt handling.
                } else {
                    const signed: i128 = @intCast(mag);
                    return value.Value{ .int = .{ .small = if (neg) -signed else signed } };
                }
            }

            const bi = try self.arena.makeBigInt();
            bi.setString(16, digits) catch return IonError.InvalidIon;
            if (neg) bi.negate();
            return value.Value{ .int = .{ .big = bi } };
        }
        if (self.startsWith("0b") or self.startsWith("0B")) {
            self.consume(2);
            const digits_start = self.i;
            while (!self.eof()) {
                const c = self.peek().?;
                if (c == '0' or c == '1' or c == '_') {
                    self.i += 1;
                    continue;
                }
                break;
            }
            if (!self.eof() and !isTokenBoundary(self.input, self.i) and !self.startsWith("//") and !self.startsWith("/*")) {
                return IonError.InvalidIon;
            }
            const raw = self.input[digits_start..self.i];
            try validateUnderscoresBinary(raw);
            const digits = try stripUnderscores(self.arena.gpa, raw);
            defer self.arena.gpa.free(digits);
            const mag_u128 = std.fmt.parseInt(u128, digits, 2) catch |e| switch (e) {
                error.Overflow => null,
                else => return IonError.InvalidIon,
            };
            if (mag_u128) |mag| {
                if (mag > @as(u128, std.math.maxInt(i128))) {
                    // Fall through to BigInt handling.
                } else {
                    const signed: i128 = @intCast(mag);
                    return value.Value{ .int = .{ .small = if (neg) -signed else signed } };
                }
            }

            const bi = try self.arena.makeBigInt();
            bi.setString(2, digits) catch return IonError.InvalidIon;
            if (neg) bi.negate();
            return value.Value{ .int = .{ .big = bi } };
        }

        // Decimal / float / decimal with d exponent.
        // Scan token characters.
        self.i = start;
        while (!self.eof()) {
            const c = self.peek().?;
            if (std.ascii.isAlphanumeric(c) or c == '.' or c == '-' or c == '+' or c == '_') {
                self.i += 1;
                continue;
            }
            break;
        }
        // After a number token, require a token boundary or the start of a comment.
        if (!self.eof() and !isTokenBoundary(self.input, self.i) and !self.startsWith("//") and !self.startsWith("/*")) {
            return IonError.InvalidIon;
        }
        const tok_raw = self.input[start..self.i];
        try validateUnderscoresDecimal(tok_raw);
        const tok = try stripUnderscores(self.arena.gpa, tok_raw);
        defer self.arena.gpa.free(tok);

        try validateNoLeadingZero(tok);

        // Decimal with 'd' exponent. The mantissa may also contain a decimal point (e.g. 123.0d0, 123.d7).
        if (std.mem.indexOfScalar(u8, tok, 'd') orelse std.mem.indexOfScalar(u8, tok, 'D')) |pos| {
            const mant_str = tok[0..pos];
            const exp_str = tok[pos + 1 ..];
            if (mant_str.len == 0 or exp_str.len == 0) return IonError.InvalidIon;
            const exp_adjust = std.fmt.parseInt(i32, exp_str, 10) catch return IonError.InvalidIon;

            var coeff_neg = false;
            var s = mant_str;
            if (s.len == 0) return IonError.InvalidIon;
            if (s[0] == '-') {
                coeff_neg = true;
                s = s[1..];
            } else if (s[0] == '+') {
                return IonError.InvalidIon;
            }
            if (s.len == 0) return IonError.InvalidIon;

            const dot_opt = std.mem.indexOfScalar(u8, s, '.');
            const left = if (dot_opt) |dot| s[0..dot] else s;
            const right = if (dot_opt) |dot| s[dot + 1 ..] else s[s.len..s.len];
            if (left.len == 0) return IonError.InvalidIon;
            for (left) |c| if (!std.ascii.isDigit(c)) return IonError.InvalidIon;
            for (right) |c| if (!std.ascii.isDigit(c)) return IonError.InvalidIon;

            var tmp_buf = std.ArrayListUnmanaged(u8){};
            defer tmp_buf.deinit(self.arena.gpa);
            tmp_buf.appendSlice(self.arena.gpa, left) catch return IonError.OutOfMemory;
            tmp_buf.appendSlice(self.arena.gpa, right) catch return IonError.OutOfMemory;
            const digits = tmp_buf.items;
            const mag: value.Int = blk: {
                if (digits.len == 0) break :blk .{ .small = 0 };
                const mag_i128 = std.fmt.parseInt(i128, digits, 10) catch |e| switch (e) {
                    error.Overflow => null,
                    else => return IonError.InvalidIon,
                };
                if (mag_i128) |m| {
                    if (m < 0) return IonError.InvalidIon;
                    break :blk .{ .small = m };
                }
                const bi = try self.arena.makeBigInt();
                try value.setBigIntFromUnsignedDecimalDigitsFast(bi, digits);
                break :blk .{ .big = bi };
            };
            const base_exp: i32 = -@as(i32, @intCast(right.len));
            return value.Value{ .decimal = .{ .is_negative = coeff_neg, .coefficient = mag, .exponent = base_exp + exp_adjust } };
        }

        // Float if contains 'e'/'E'.
        if (std.mem.indexOfAny(u8, tok, "eE") != null) {
            const f = std.fmt.parseFloat(f64, tok) catch return IonError.InvalidIon;
            return value.Value{ .float = f };
        }

        // Decimal if contains a decimal point.
        if (std.mem.indexOfScalar(u8, tok, '.')) |_| {
            var coeff_neg = false;
            var s = tok;
            if (s.len == 0) return IonError.InvalidIon;
            if (s[0] == '-') {
                coeff_neg = true;
                s = s[1..];
            } else if (s[0] == '+') {
                return IonError.InvalidIon;
            }
            const dot = std.mem.indexOfScalar(u8, s, '.') orelse return IonError.InvalidIon;
            const left = s[0..dot];
            const right = s[dot + 1 ..];
            if (left.len == 0) return IonError.InvalidIon;
            for (left) |c| if (!std.ascii.isDigit(c)) return IonError.InvalidIon;
            for (right) |c| if (!std.ascii.isDigit(c)) return IonError.InvalidIon;

            var tmp_buf = std.ArrayListUnmanaged(u8){};
            defer tmp_buf.deinit(self.arena.gpa);
            tmp_buf.appendSlice(self.arena.gpa, left) catch return IonError.OutOfMemory;
            tmp_buf.appendSlice(self.arena.gpa, right) catch return IonError.OutOfMemory;
            const digits = tmp_buf.items;
            const mag: value.Int = blk: {
                if (digits.len == 0) break :blk .{ .small = 0 };
                const mag_i128 = std.fmt.parseInt(i128, digits, 10) catch |e| switch (e) {
                    error.Overflow => null,
                    else => return IonError.InvalidIon,
                };
                if (mag_i128) |m| {
                    if (m < 0) return IonError.InvalidIon;
                    break :blk .{ .small = m };
                }
                const bi = try self.arena.makeBigInt();
                try value.setBigIntFromUnsignedDecimalDigitsFast(bi, digits);
                break :blk .{ .big = bi };
            };
            const exp: i32 = -@as(i32, @intCast(right.len));
            return value.Value{ .decimal = .{ .is_negative = coeff_neg, .coefficient = mag, .exponent = exp } };
        }

        // Int base-10
        if (tok.len == 0) return IonError.InvalidIon;
        if (tok[0] == '+') return IonError.InvalidIon;
        const v_i128 = std.fmt.parseInt(i128, tok, 10) catch |e| switch (e) {
            error.Overflow => null,
            else => return IonError.InvalidIon,
        };
        if (v_i128) |v| return value.Value{ .int = .{ .small = v } };

        var neg2 = false;
        var digits2 = tok;
        if (digits2[0] == '-') {
            neg2 = true;
            digits2 = digits2[1..];
        }
        const bi = try self.arena.makeBigInt();
        try value.setBigIntFromUnsignedDecimalDigitsFast(bi, digits2);
        if (neg2) bi.negate();
        return value.Value{ .int = .{ .big = bi } };
    }

    fn parseTimestamp(self: *Parser) IonError!value.Timestamp {
        // Very strict timestamp parser tailored to ion-tests corpus.
        // YYYY(-MM(-DD([Tt]hh:mm(:ss(.fff)?)?([Zz]|(+|-)hh:mm| -00:00)? )?)?)?
        const start = self.i;

        const year = try self.parseFixedDigits(4);
        if (year == 0) return IonError.InvalidIon;
        var ts: value.Timestamp = .{
            .year = @intCast(year),
            .month = null,
            .day = null,
            .hour = null,
            .minute = null,
            .second = null,
            .fractional = null,
            .offset_minutes = null,
            .precision = .year,
        };

        if (!self.eof() and (self.peek().? == 'T' or self.peek().? == 't')) {
            // Year precision timestamps must end with a trailing 'T'.
            if (self.i + 1 < self.input.len and std.ascii.isDigit(self.input[self.i + 1])) return IonError.InvalidIon;
            self.consume(1);
            return ts;
        }
        if (self.eof() or self.peek().? != '-') return IonError.InvalidIon;
        self.consume(1);
        const month = try self.parseFixedDigits(2);
        if (month == 0 or month > 12) return IonError.InvalidIon;
        ts.month = @intCast(month);
        ts.precision = .month;

        if (!self.eof() and (self.peek().? == 'T' or self.peek().? == 't')) {
            // Month precision timestamps must end with a trailing 'T'.
            if (self.i + 1 < self.input.len and std.ascii.isDigit(self.input[self.i + 1])) return IonError.InvalidIon;
            self.consume(1);
            return ts;
        }
        if (self.eof() or self.peek().? != '-') return IonError.InvalidIon;
        self.consume(1);
        const day = try self.parseFixedDigits(2);
        if (day == 0 or day > daysInMonth(@intCast(ts.year), @intCast(month))) return IonError.InvalidIon;
        ts.day = @intCast(day);
        ts.precision = .day;

        if (self.eof()) return ts;
        const t = self.peek().?;
        if (t != 'T' and t != 't') return ts;
        self.consume(1);
        if (self.eof()) return ts;
        // Day precision timestamp may end with a trailing 'T' (no time component).
        if (!std.ascii.isDigit(self.peek().?)) return ts;

        const hour = try self.parseFixedDigits(2);
        if (hour > 23) return IonError.InvalidIon;
        if (self.eof() or self.peek().? != ':') return IonError.InvalidIon;
        self.consume(1);
        const minute = try self.parseFixedDigits(2);
        if (minute > 59) return IonError.InvalidIon;
        ts.hour = @intCast(hour);
        ts.minute = @intCast(minute);
        ts.precision = .minute;

        if (self.eof()) return ts;
        if (self.peek().? == ':') {
            self.consume(1);
            const sec = try self.parseFixedDigits(2);
            if (sec > 59) return IonError.InvalidIon;
            ts.second = @intCast(sec);
            ts.precision = .second;

            if (!self.eof() and self.peek().? == '.') {
                self.consume(1);
                const frac_start = self.i;
                while (!self.eof() and std.ascii.isDigit(self.peek().?)) : (self.i += 1) {}
                if (self.i == frac_start) return IonError.InvalidIon;
                const frac_digits = self.input[frac_start..self.i];
                const mag: value.Int = blk: {
                    const mag_i128 = std.fmt.parseInt(i128, frac_digits, 10) catch |e| switch (e) {
                        error.Overflow => null,
                        else => return IonError.InvalidIon,
                    };
                    if (mag_i128) |m| break :blk .{ .small = m };
                    const bi = try self.arena.makeBigInt();
                    try value.setBigIntFromUnsignedDecimalDigitsFast(bi, frac_digits);
                    break :blk .{ .big = bi };
                };
                const exp: i32 = -@as(i32, @intCast(frac_digits.len));
                ts.fractional = .{ .is_negative = false, .coefficient = mag, .exponent = exp };
                ts.precision = .fractional;
            }
        }

        // For timestamps with time components, an explicit offset is required (including -00:00 for unknown).
        if (self.eof()) return IonError.InvalidIon;
        // Offset
        if (self.peek().? == 'Z') {
            self.consume(1);
            ts.offset_minutes = 0;
            return ts;
        }
        if (self.peek().? == '+' or self.peek().? == '-') {
            const sign = self.peek().?;
            self.consume(1);
            const off_h = try self.parseFixedDigits(2);
            if (off_h > 23) return IonError.InvalidIon;
            if (self.eof() or self.peek().? != ':') return IonError.InvalidIon;
            self.consume(1);
            const off_m = try self.parseFixedDigits(2);
            if (off_m > 59) return IonError.InvalidIon;
            var minutes: i16 = @intCast(off_h * 60 + off_m);
            if (sign == '-') minutes = -minutes;
            // Unknown offset is encoded in text as -00:00. Keep as null.
            if (minutes == 0 and sign == '-') {
                ts.offset_minutes = null;
            } else {
                ts.offset_minutes = minutes;
            }
            return ts;
        }

        // If offset isn't present, this is invalid for time-precision timestamps.
        _ = start;
        return IonError.InvalidIon;
    }

    fn parseFixedDigits(self: *Parser, n: usize) IonError!u32 {
        if (self.i + n > self.input.len) return IonError.Incomplete;
        var v: u32 = 0;
        var j: usize = 0;
        while (j < n) : (j += 1) {
            const c = self.input[self.i + j];
            if (!std.ascii.isDigit(c)) return IonError.InvalidIon;
            v = v * 10 + (c - '0');
        }
        self.i += n;
        return v;
    }

    fn maybeConsumeSymbolTable(self: *Parser, elem: value.Element) IonError!void {
        if (elem.annotations.len == 0) return;
        const ann = elem.annotations[0].text orelse return;
        if (elem.value != .@"struct") return;
        const st_val = elem.value.@"struct";

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
                    const out = self.arena.allocator().alloc(?[]const u8, items.len) catch return IonError.OutOfMemory;
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
            const key = std.fmt.allocPrint(self.arena.allocator(), "{s}:{d}", .{ n, v }) catch return IonError.OutOfMemory;
            self.shared.put(self.arena.allocator(), key, .{ .name = n, .version = v, .symbols = syms }) catch return IonError.OutOfMemory;
            return;
        }

        if (!std.mem.eql(u8, ann, "$ion_symbol_table")) return;

        const applyImport = struct {
            fn run(p: *Parser, import_name: []const u8, import_version: u32, import_max_id: u32) IonError!void {
                if (import_max_id == 0) return;

                const key = std.fmt.allocPrint(p.arena.allocator(), "{s}:{d}", .{ import_name, import_version }) catch return IonError.OutOfMemory;
                if (p.shared.get(key)) |shared_st| {
                    try p.st.addImport(shared_st.symbols, import_max_id);
                } else {
                    try p.st.addImport(&.{}, import_max_id);
                }
            }
        }.run;

        const parseImportStruct = struct {
            fn run(p: *Parser, imp_st: value.Struct) IonError!struct { name: []const u8, version: u32, max_id: u32 } {
                var name: ?[]const u8 = null;
                var version: u32 = 1;
                var max_id: ?u32 = null;

                for (imp_st.fields) |ff| {
                    const nn = ff.name.text orelse continue;
                    if (std.mem.eql(u8, nn, "name")) {
                        if (ff.value.value != .string) return IonError.InvalidIon;
                        name = ff.value.value.string;
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
                    const key = std.fmt.allocPrint(p.arena.allocator(), "{s}:{d}", .{ n, version }) catch return IonError.OutOfMemory;
                    if (p.shared.get(key)) |shared_st| break :blk @as(u32, @intCast(shared_st.symbols.len));
                    break :blk 0;
                };

                return .{ .name = n, .version = version, .max_id = m };
            }
        }.run;

        var imports_value: ?value.Value = null;
        var symbols_list: ?[]const value.Element = null;
        for (st_val.fields) |f| {
            const fname = f.name.text orelse continue;
            if (std.mem.eql(u8, fname, "imports")) {
                if (imports_value != null) return IonError.InvalidIon;
                imports_value = f.value.value;
            } else if (std.mem.eql(u8, fname, "symbols")) {
                if (symbols_list != null) return IonError.InvalidIon;
                if (f.value.value != .list) return IonError.InvalidIon;
                symbols_list = f.value.value.list;
            }
        }

        const imports = imports_value orelse value.Value{ .null = .null };
        const preserve_current = switch (imports) {
            .symbol => |s| blk: {
                const t = s.text orelse break :blk false;
                break :blk std.mem.eql(u8, t, "$ion_symbol_table");
            },
            else => false,
        };

        if (!preserve_current) {
            self.st.deinit();
            self.st = try symtab.SymbolTable.init(self.arena);
        }

        switch (imports) {
            .null => {},
            .symbol => |s| {
                const t = s.text orelse return IonError.InvalidIon;
                if (!std.mem.eql(u8, t, "$ion_symbol_table")) return IonError.InvalidIon;
            },
            .list => |imports_list| {
                for (imports_list) |imp_elem| {
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

        if (symbols_list) |syms| {
            for (syms) |sym_elem| {
                if (sym_elem.value == .string) {
                    _ = try self.st.addSymbolText(sym_elem.value.string);
                } else {
                    _ = try self.st.addNullSlot();
                }
            }
        }
    }
};

fn isSystemValue(elem: value.Element) bool {
    // Text IVM ($ion_1_0) is returned by parseValue as a symbol unless it appears as a plain
    // top-level symbol with no annotations; treat that as system.
    if (elem.annotations.len == 0 and elem.value == .symbol) {
        const t = elem.value.symbol.text orelse return false;
        return std.mem.eql(u8, t, "$ion_1_0") or std.mem.eql(u8, t, "$ion_1_1");
    }
    // Local symbol table struct is system.
    if (elem.annotations.len >= 1 and elem.value == .@"struct") {
        const t = elem.annotations[0].text orelse return false;
        return std.mem.eql(u8, t, "$ion_symbol_table") or std.mem.eql(u8, t, "$ion_shared_symbol_table");
    }
    return false;
}

fn hasIonLiteralAnnotation(annotations: []const value.Symbol) bool {
    for (annotations) |a| {
        const t = a.text orelse continue;
        if (std.mem.eql(u8, t, "$ion_literal")) return true;
    }
    return false;
}

fn stripIonLiteralAnnotation(arena: *value.Arena, elem: value.Element) IonError!value.Element {
    // Keep value/field storage; only rewrite annotations slice.
    var count: usize = 0;
    for (elem.annotations) |a| {
        const t = a.text orelse "";
        if (std.mem.eql(u8, t, "$ion_literal")) continue;
        count += 1;
    }
    if (count == elem.annotations.len) return elem;
    const out_anns = arena.allocator().alloc(value.Symbol, count) catch return IonError.OutOfMemory;
    var i: usize = 0;
    for (elem.annotations) |a| {
        const t = a.text orelse "";
        if (std.mem.eql(u8, t, "$ion_literal")) continue;
        out_anns[i] = a;
        i += 1;
    }
    return .{ .annotations = out_anns, .value = elem.value };
}

fn parseNullType(text: []const u8) ?value.IonType {
    return if (std.mem.eql(u8, text, "null")) .null else if (std.mem.eql(u8, text, "bool")) .bool else if (std.mem.eql(u8, text, "int")) .int else if (std.mem.eql(u8, text, "float")) .float else if (std.mem.eql(u8, text, "decimal")) .decimal else if (std.mem.eql(u8, text, "timestamp")) .timestamp else if (std.mem.eql(u8, text, "symbol")) .symbol else if (std.mem.eql(u8, text, "string")) .string else if (std.mem.eql(u8, text, "clob")) .clob else if (std.mem.eql(u8, text, "blob")) .blob else if (std.mem.eql(u8, text, "list")) .list else if (std.mem.eql(u8, text, "sexp")) .sexp else if (std.mem.eql(u8, text, "struct")) .@"struct" else null;
}

fn isIdentStart(c: u8) bool {
    // Note: ':' is intentionally excluded; Ion 1.1 macro invocations are handled separately.
    return std.ascii.isAlphabetic(c) or c == '_' or c == '$';
}

fn isIdentCont(c: u8) bool {
    return std.ascii.isAlphanumeric(c) or c == '_' or c == '$';
}

fn isIdentContConformanceDsl(c: u8) bool {
    // Conformance DSL uses suffix operators in identifiers (e.g. `x?`, `x*`, `x+`).
    // Keep this scoped to DSL parsing so we don't change Ion tokenization rules (e.g. `a-1`).
    return isIdentCont(c) or c == '?' or c == '*' or c == '+';
}

fn isOperatorStart(c: u8) bool {
    return isOperatorChar(c);
}

fn isOperatorChar(c: u8) bool {
    return switch (c) {
        '`', '~', '!', '@', '#', '$', '%', '^', '&', '*', '-', '+', '=', '|', ';', '<', '>', '?', '.', '/' => true,
        else => false,
    };
}

fn isLeapYear(year: i32) bool {
    // Proleptic Gregorian calendar.
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

fn looksLikeTimestamp(s: []const u8) bool {
    // YYYY-... or YYYYT...
    if (s.len < 5) return false;
    if (!(std.ascii.isDigit(s[0]) and std.ascii.isDigit(s[1]) and std.ascii.isDigit(s[2]) and std.ascii.isDigit(s[3]))) return false;
    return s[4] == '-' or s[4] == 'T' or s[4] == 't';
}

fn isTokenBoundary(input: []const u8, index: usize) bool {
    if (index >= input.len) return true;
    const c = input[index];
    return c == ' ' or c == '\t' or c == '\n' or c == '\r' or c == 0x0B or c == 0x0C or c == ',' or c == ']' or c == ')' or c == '}' or c == ':';
}

fn isReservedSymbolIdentifier(token: []const u8) bool {
    if (std.mem.eql(u8, token, "null")) return true;
    if (std.mem.eql(u8, token, "true")) return true;
    if (std.mem.eql(u8, token, "false")) return true;
    if (std.mem.eql(u8, token, "nan")) return true;
    if (std.mem.startsWith(u8, token, "null.")) return true;
    return false;
}

fn validateUnderscoresDecimal(raw: []const u8) IonError!void {
    // Underscores are only allowed between digits for base-10 numerics.
    var i: usize = 0;
    while (i < raw.len) : (i += 1) {
        if (raw[i] != '_') continue;
        if (i == 0 or i + 1 >= raw.len) return IonError.InvalidIon;
        if (!std.ascii.isDigit(raw[i - 1]) or !std.ascii.isDigit(raw[i + 1])) return IonError.InvalidIon;
    }
}

fn validateUnderscoresHex(raw: []const u8) IonError!void {
    var i: usize = 0;
    while (i < raw.len) : (i += 1) {
        if (raw[i] != '_') continue;
        if (i == 0 or i + 1 >= raw.len) return IonError.InvalidIon;
        if (!std.ascii.isHex(raw[i - 1]) or !std.ascii.isHex(raw[i + 1])) return IonError.InvalidIon;
    }
}

fn validateUnderscoresBinary(raw: []const u8) IonError!void {
    var i: usize = 0;
    while (i < raw.len) : (i += 1) {
        if (raw[i] != '_') continue;
        if (i == 0 or i + 1 >= raw.len) return IonError.InvalidIon;
        const a = raw[i - 1];
        const b = raw[i + 1];
        if (!((a == '0' or a == '1') and (b == '0' or b == '1'))) return IonError.InvalidIon;
    }
}

fn validateNoLeadingZero(tok: []const u8) IonError!void {
    // Ion base-10 numerics must not have leading zeros in the integer component.
    // Examples:
    // - OK: 0, -0, 0.3, 0e1, 0d0
    // - BAD: 00, -00, 04, 04.3, 04e1, 04d0
    if (tok.len == 0) return IonError.InvalidIon;
    var i: usize = 0;
    if (tok[0] == '+') return IonError.InvalidIon;
    if (tok[0] == '-') {
        i = 1;
        if (i >= tok.len) return IonError.InvalidIon;
    }

    // Scan the initial digit run (integer component) until '.', 'eE', or 'dD'.
    const start = i;
    while (i < tok.len and std.ascii.isDigit(tok[i])) : (i += 1) {}
    if (i == start) return IonError.InvalidIon;
    if (tok[start] == '0' and i - start > 1) return IonError.InvalidIon;
}

fn stripUnderscores(allocator: std.mem.Allocator, s: []const u8) ![]u8 {
    if (std.mem.indexOfScalar(u8, s, '_') == null) return allocator.dupe(u8, s);
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);
    for (s) |c| {
        if (c == '_') continue;
        try out.append(allocator, c);
    }
    return out.toOwnedSlice(allocator);
}

fn decodeEscape(self: *Parser, out: *std.ArrayListUnmanaged(u8), as_bytes: bool) IonError!void {
    if (self.eof()) return IonError.Incomplete;
    const c = self.peek().?;
    self.consume(1);
    switch (c) {
        '0' => try appendByte(self, out, 0),
        'a' => try appendByte(self, out, 0x07),
        'b' => try appendByte(self, out, 0x08),
        't' => try appendByte(self, out, 0x09),
        'n' => try appendByte(self, out, 0x0A),
        'f' => try appendByte(self, out, 0x0C),
        'r' => try appendByte(self, out, 0x0D),
        'v' => try appendByte(self, out, 0x0B),
        '"' => try appendByte(self, out, '"'),
        '\'' => try appendByte(self, out, '\''),
        '?' => try appendByte(self, out, '?'),
        '\\' => try appendByte(self, out, '\\'),
        '/' => try appendByte(self, out, '/'),
        'x' => {
            const b = try parseHexByte(self);
            if (as_bytes) {
                try appendByte(self, out, b);
            } else {
                try appendUtf8(self, out, @intCast(b));
            }
        },
        'u' => {
            if (as_bytes) return IonError.InvalidIon;
            const hi = try parseHexN(self, 4);
            // UTF-16 surrogate pairs are allowed in Ion escape sequences.
            if (hi >= 0xD800 and hi <= 0xDBFF) {
                // Expect a following \\uXXXX for the low surrogate.
                if (self.eof()) return IonError.Incomplete;
                if (self.peek().? != '\\') return IonError.InvalidIon;
                self.consume(1);
                if (self.eof()) return IonError.Incomplete;
                if (self.peek().? != 'u') return IonError.InvalidIon;
                self.consume(1);
                const lo = try parseHexN(self, 4);
                if (lo < 0xDC00 or lo > 0xDFFF) return IonError.InvalidIon;
                const cp: u32 = 0x10000 + (((hi - 0xD800) << 10) | (lo - 0xDC00));
                try appendUtf8(self, out, @intCast(cp));
            } else if (hi >= 0xDC00 and hi <= 0xDFFF) {
                return IonError.InvalidIon;
            } else {
                try appendUtf8(self, out, @intCast(hi));
            }
        },
        'U' => {
            if (as_bytes) return IonError.InvalidIon;
            const cp = try parseHexN(self, 8);
            try appendUtf8(self, out, @intCast(cp));
        },
        '\r' => {
            // Escaped newlines are line continuations in long strings; here just normalize.
            if (self.startsWith("\n")) self.consume(1);
        },
        '\n' => {},
        else => return IonError.InvalidIon,
    }
}

fn appendByte(self: *Parser, out: *std.ArrayListUnmanaged(u8), b: u8) IonError!void {
    out.append(self.arena.allocator(), b) catch return IonError.OutOfMemory;
}

fn appendUtf8(self: *Parser, out: *std.ArrayListUnmanaged(u8), cp: u21) IonError!void {
    var buf: [4]u8 = undefined;
    const len = std.unicode.utf8Encode(cp, &buf) catch return IonError.InvalidIon;
    out.appendSlice(self.arena.allocator(), buf[0..len]) catch return IonError.OutOfMemory;
}

fn parseHexByte(self: *Parser) IonError!u8 {
    const v = try parseHexN(self, 2);
    return @intCast(v);
}

fn parseHexN(self: *Parser, n: usize) IonError!u32 {
    if (self.i + n > self.input.len) return IonError.Incomplete;
    var v: u32 = 0;
    var j: usize = 0;
    while (j < n) : (j += 1) {
        const c = self.input[self.i + j];
        v <<= 4;
        v |= std.fmt.charToDigit(c, 16) catch return IonError.InvalidIon;
    }
    self.i += n;
    return v;
}
