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

const IonError = ion.IonError;

/// Parses an Ion text stream into a top-level sequence of `value.Element`s.
///
/// All returned slices are allocated in `arena` and valid until the arena is deinited.
pub fn parseTopLevel(arena: *value.Arena, bytes: []const u8) IonError![]value.Element {
    var parser = try Parser.init(arena, bytes);
    return parser.parseTopLevel();
}

/// Debug helper: on error, writes the parser byte offset into `err_index`.
/// Intended for ad-hoc repro tooling; normal callers should use `parseTopLevel`.
///
/// All returned slices are allocated in `arena` and valid until the arena is deinited.
pub fn parseTopLevelWithErrorIndex(arena: *value.Arena, bytes: []const u8, err_index: *usize) IonError![]value.Element {
    var parser = try Parser.init(arena, bytes);
    return parser.parseTopLevel() catch |e| {
        err_index.* = parser.i;
        return e;
    };
}

const Parser = struct {
    arena: *value.Arena,
    input: []const u8,
    i: usize = 0,
    st: symtab.SymbolTable,

    fn init(arena: *value.Arena, input: []const u8) IonError!Parser {
        return .{
            .arena = arena,
            .input = input,
            .i = 0,
            .st = try symtab.SymbolTable.init(arena),
        };
    }

    fn parseTopLevel(self: *Parser) IonError![]value.Element {
        defer self.st.deinit();

        var out = std.ArrayListUnmanaged(value.Element){};
        errdefer out.deinit(self.arena.allocator());

        while (true) {
            try self.skipWsComments();
            if (self.eof()) break;

            // Ion Version Marker in text: $ion_1_0 at top-level (not annotated) is a system value.
            // It can also appear as a normal symbol if annotated/inside containers; we only treat
            // it as IVM if it's the next token at top-level with no annotations.
            const before = self.i;
            const elem = try self.parseElement(.top);
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
                                if (major_all_digits and minor_all_digits and !std.mem.eql(u8, t, "$ion_1_0")) {
                                    return IonError.InvalidIon;
                                }
                            }
                        }
                    }
                }
            }
            if (isSystemValue(elem)) {
                // Apply symbol table if present, otherwise ignore.
                try self.maybeConsumeSymbolTable(elem);
            } else {
                out.append(self.arena.allocator(), elem) catch return IonError.OutOfMemory;
            }

            // Prevent infinite loops on malformed inputs.
            if (self.i == before) return IonError.InvalidIon;
        }

        return out.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory;
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
            // An annotation must have known text, except for $0 which represents unknown.
            if (sym.text == null and (sym.sid == null or sym.sid.? != 0)) return IonError.InvalidIon;
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
        if (self.startsWith("\"")) return value.Value{ .string = try self.parseStringConcat(false) };
        if (self.startsWith("'''")) return value.Value{ .string = try self.parseLongStringConcat(false) };
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

            const elem = try self.parseElement(.list);
            elems.append(self.arena.allocator(), elem) catch return IonError.OutOfMemory;
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
            const elem = try self.parseElement(.sexp);
            elems.append(self.arena.allocator(), elem) catch return IonError.OutOfMemory;
        }
        return value.Value{ .sexp = elems.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory };
    }

    fn parseStruct(self: *Parser) IonError!value.Value {
        if (!self.startsWith("{")) return IonError.InvalidIon;
        self.consume(1);
        try self.skipWsComments();
        var fields = std.ArrayListUnmanaged(value.StructField){};
        errdefer fields.deinit(self.arena.allocator());
        var expect_field = true;
        while (true) {
            try self.skipWsComments();
            if (self.eof()) return IonError.Incomplete;
            const c = self.peek().?;
            if (c == '}') {
                self.consume(1);
                break;
            }
            if (c == ',') {
                if (expect_field) return IonError.InvalidIon;
                self.consume(1);
                expect_field = true;
                continue;
            }
            if (!expect_field) expect_field = true;

            const name = try self.parseFieldName();
            try self.skipWsComments();
            if (self.eof() or self.peek().? != ':') return IonError.InvalidIon;
            self.consume(1);
            const v = try self.parseElement(.@"struct");
            fields.append(self.arena.allocator(), .{ .name = name, .value = v }) catch return IonError.OutOfMemory;
            expect_field = false;
        }
        return value.Value{ .@"struct" = .{ .fields = fields.toOwnedSlice(self.arena.allocator()) catch return IonError.OutOfMemory } };
    }

    fn parseFieldName(self: *Parser) IonError!value.Symbol {
        try self.skipWsComments();
        // Long strings start with three quotes, which also matches the quoted symbol prefix.
        // Check for long strings first.
        if (self.startsWith("'''")) {
            const text_bytes = try self.parseLongStringConcat(false);
            return value.makeSymbolId(null, text_bytes);
        }
        if (self.startsWith("'")) return self.parseQuotedSymbol();
        if (self.startsWith("\"")) {
            const text_bytes = try self.parseStringConcat(false);
            return value.makeSymbolId(null, text_bytes);
        }
        if (self.peek() == null) return IonError.Incomplete;
        if (self.peek().? == '$') {
            if (self.i + 1 < self.input.len and std.ascii.isDigit(self.input[self.i + 1])) {
                const s = try self.parseSymbolId();
                if (s.text == null and (s.sid == null or s.sid.? != 0)) return IonError.InvalidIon;
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
        const txt = self.st.textForSid(sid) orelse return IonError.InvalidIon;
        return value.makeSymbolId(sid, txt);
    }

    fn parseIdentifierToken(self: *Parser) IonError![]const u8 {
        const start = self.i;
        if (self.eof()) return IonError.Incomplete;
        if (!isIdentStart(self.peek().?)) return IonError.InvalidIon;
        self.i += 1;
        while (!self.eof() and isIdentCont(self.peek().?)) : (self.i += 1) {}
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
            const digits = try stripUnderscores(self.arena.allocator(), raw);
            defer self.arena.allocator().free(digits);
            const mag = std.fmt.parseInt(u128, digits, 16) catch return IonError.InvalidIon;
            if (mag > @as(u128, std.math.maxInt(i128))) return IonError.Unsupported;
            const signed: i128 = @intCast(mag);
            return value.Value{ .int = if (neg) -signed else signed };
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
            const digits = try stripUnderscores(self.arena.allocator(), raw);
            defer self.arena.allocator().free(digits);
            const mag = std.fmt.parseInt(u128, digits, 2) catch return IonError.InvalidIon;
            if (mag > @as(u128, std.math.maxInt(i128))) return IonError.Unsupported;
            const signed: i128 = @intCast(mag);
            return value.Value{ .int = if (neg) -signed else signed };
        }

        // Decimal / float / decimal with d exponent.
        // Scan token characters.
        self.i = start;
        while (!self.eof()) {
            const c = self.peek().?;
            if (std.ascii.isAlphanumeric(c) or c == '.' or c == '-' or c == '+' or c == '_' ) {
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
        const tok = try stripUnderscores(self.arena.allocator(), tok_raw);
        defer self.arena.allocator().free(tok);

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
            defer tmp_buf.deinit(self.arena.allocator());
            tmp_buf.appendSlice(self.arena.allocator(), left) catch return IonError.OutOfMemory;
            tmp_buf.appendSlice(self.arena.allocator(), right) catch return IonError.OutOfMemory;
            const digits = tmp_buf.items;
            const mag = if (digits.len == 0) 0 else std.fmt.parseInt(i128, digits, 10) catch return IonError.InvalidIon;
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
            defer tmp_buf.deinit(self.arena.allocator());
            tmp_buf.appendSlice(self.arena.allocator(), left) catch return IonError.OutOfMemory;
            tmp_buf.appendSlice(self.arena.allocator(), right) catch return IonError.OutOfMemory;
            const digits = tmp_buf.items;
            const mag = if (digits.len == 0) 0 else std.fmt.parseInt(i128, digits, 10) catch return IonError.InvalidIon;
            const exp: i32 = -@as(i32, @intCast(right.len));
            return value.Value{ .decimal = .{ .is_negative = coeff_neg, .coefficient = mag, .exponent = exp } };
        }

        // Int base-10
        if (tok.len == 0) return IonError.InvalidIon;
        if (tok[0] == '+') return IonError.InvalidIon;
        const v = std.fmt.parseInt(i128, tok, 10) catch return IonError.InvalidIon;
        return value.Value{ .int = v };
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
                const mag = std.fmt.parseInt(i128, frac_digits, 10) catch return IonError.InvalidIon;
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
        // Only handle local symbol tables with $ion_symbol_table annotation and 'symbols' field.
        if (elem.annotations.len == 0) return;
        const ann = elem.annotations[0].text orelse return;
        if (!std.mem.eql(u8, ann, "$ion_symbol_table")) return;
        if (elem.value != .@"struct") return;
        const st_val = elem.value.@"struct";

        var seen_symbols = false;
        var seen_imports = false;
        for (st_val.fields) |f| {
            const name = f.name.text orelse continue;
            if (std.mem.eql(u8, name, "symbols")) {
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
                continue;
            }
            if (std.mem.eql(u8, name, "imports")) {
                if (seen_imports) return IonError.InvalidIon;
                seen_imports = true;
                // Minimal handling: accept empty imports or `imports: $ion_symbol_table`, reject others.
                switch (f.value.value) {
                    .null => {},
                    .list => |imports| {
                        if (imports.len != 0) return IonError.InvalidIon;
                    },
                    .symbol => |s| {
                        const t = s.text orelse return IonError.InvalidIon;
                        if (!std.mem.eql(u8, t, "$ion_symbol_table")) return IonError.InvalidIon;
                    },
                    else => return IonError.InvalidIon,
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
        return std.mem.eql(u8, t, "$ion_1_0");
    }
    // Local symbol table struct is system.
    if (elem.annotations.len >= 1 and elem.value == .@"struct") {
        const t = elem.annotations[0].text orelse return false;
        return std.mem.eql(u8, t, "$ion_symbol_table") or std.mem.eql(u8, t, "$ion_shared_symbol_table");
    }
    return false;
}

fn parseNullType(text: []const u8) ?value.IonType {
    return if (std.mem.eql(u8, text, "null")) .null else if (std.mem.eql(u8, text, "bool")) .bool else if (std.mem.eql(u8, text, "int")) .int else if (std.mem.eql(u8, text, "float")) .float else if (std.mem.eql(u8, text, "decimal")) .decimal else if (std.mem.eql(u8, text, "timestamp")) .timestamp else if (std.mem.eql(u8, text, "symbol")) .symbol else if (std.mem.eql(u8, text, "string")) .string else if (std.mem.eql(u8, text, "clob")) .clob else if (std.mem.eql(u8, text, "blob")) .blob else if (std.mem.eql(u8, text, "list")) .list else if (std.mem.eql(u8, text, "sexp")) .sexp else if (std.mem.eql(u8, text, "struct")) .@"struct" else null;
}

fn isIdentStart(c: u8) bool {
    return std.ascii.isAlphabetic(c) or c == '_' or c == '$';
}

fn isIdentCont(c: u8) bool {
    return std.ascii.isAlphanumeric(c) or c == '_' or c == '$';
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
