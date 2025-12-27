//! Minimal Ion 1.0 reader/writer in Zig.
//!
//! Public entrypoints:
//! - `parseDocument(allocator, bytes)` parses either Ion text or Ion binary (IVM-detected).
//! - `parseDocumentWithOptions(allocator, bytes, options)` parses Ion with optional Ion 1.1 configuration.
//! - `parseDocumentBinary11WithOptions(allocator, bytes, options)` parses Ion 1.1 binary with explicit options.
//! - `serializeDocument(allocator, format, elements)` writes Ion text or Ion binary.
//! - `serializeDocumentBinary11WithOptions(allocator, elements, options)` writes Ion 1.1 binary with writer options.
//! - `serializeDocumentBinary11SelfContainedWithOptions(allocator, elements, options)` writes self-contained Ion 1.1 binary with writer options.

const std = @import("std");

pub const value = @import("ion/value.zig");
pub const symtab = @import("ion/symtab.zig");
pub const macro = @import("ion/macro.zig");
pub const text = @import("ion/text.zig");
pub const binary = @import("ion/binary.zig");
pub const binary11 = @import("ion/binary11.zig");
pub const writer = @import("ion/writer.zig");
pub const writer11 = @import("ion/writer11.zig");
pub const eq = @import("ion/eq.zig");

pub const IonError = error{
    InvalidIon,
    Incomplete,
    Unsupported,
    OutOfMemory,
};

pub const Allocator = std.mem.Allocator;

/// A parsed Ion document that owns all of its decoded values in an arena.
///
/// - `elements` is the top-level sequence.
/// - Call `deinit()` to free all arena allocations.
pub const Document = struct {
    arena: value.Arena,
    elements: []value.Element,

    /// Frees the arena backing `elements` and all nested values.
    pub fn deinit(self: *Document) void {
        self.arena.deinit();
    }
};

/// Parses a byte slice as Ion.
///
/// - If `bytes` begins with the Ion 1.0 binary IVM (`E0 01 00 EA`), parses as binary Ion.
/// - Otherwise parses as Ion text.
///
/// The returned `Document` owns an arena; call `Document.deinit()` when done.
pub fn parseDocument(allocator: Allocator, bytes: []const u8) IonError!Document {
    return parseDocumentWithMacroTable(allocator, bytes, null);
}

pub const ParseOptions = struct {
    /// Optional macro table for decoding Ion 1.1 binary e-expressions.
    mactab: ?*const macro.MacroTable = null,
    /// Optional override for the Ion 1.1 system symbol table variant when parsing Ion 1.1 binary.
    /// When null, the parser may use environment configuration and/or in-stream inference.
    sys_symtab11_variant: ?symtab.SystemSymtab11Variant = null,
    /// When true, rejects non-minimal FlexUInt/FlexInt encodings in Ion 1.1 binary.
    ///
    /// Note: `ion-tests` (especially conformance) intentionally uses non-canonical Flex encodings,
    /// so the default is `false` to keep the suite green.
    strict_flex: bool = false,
    /// When true, rejects conformance-driven opcode quirks that are not part of the Ion 1.1 binary
    /// opcode table (for example the `0x01` "tagged int 0" shortcut used by some conformance
    /// fixtures).
    strict_opcodes: bool = false,
};

/// Parses a byte slice as Ion (IVM-detected), with optional Ion 1.1 parsing configuration.
pub fn parseDocumentWithOptions(allocator: Allocator, bytes: []const u8, options: ParseOptions) IonError!Document {
    var arena = try value.Arena.init(allocator);
    errdefer arena.deinit();

    if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x00 and bytes[3] == 0xEA) {
        const elements = try binary.parseTopLevel(&arena, bytes);
        return .{ .arena = arena, .elements = elements };
    } else if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x01 and bytes[3] == 0xEA) {
        if (options.sys_symtab11_variant) |variant| {
            const res = try binary11.parseTopLevelWithMacroTableAndStateWithSystemSymtabVariantAndOptions(
                &arena,
                bytes,
                options.mactab,
                variant,
                .{ .strict_flex = options.strict_flex, .strict_opcodes = options.strict_opcodes },
            );
            return .{ .arena = arena, .elements = res.elements };
        }
        const res = try binary11.parseTopLevelWithMacroTableAndStateWithOptions(
            &arena,
            bytes,
            options.mactab,
            .{ .strict_flex = options.strict_flex, .strict_opcodes = options.strict_opcodes },
        );
        return .{ .arena = arena, .elements = res.elements };
    } else {
        const decoded = try decodeTextToUtf8(allocator, bytes);
        defer if (decoded) |b| allocator.free(b);
        const input = if (decoded) |b| b else bytes;
        const elements = try text.parseTopLevelWithMacroTable(&arena, input, options.mactab);
        return .{ .arena = arena, .elements = elements };
    }
}

/// Parses a byte slice as Ion, optionally using a conformance-provided Ion 1.1 macro table.
///
/// This is currently only used by the conformance runner to interpret Ion 1.1 binary e-expressions
/// whose macro table is supplied out-of-band via `(mactab ...)`.
pub fn parseDocumentWithMacroTable(allocator: Allocator, bytes: []const u8, mactab: ?*const macro.MacroTable) IonError!Document {
    var arena = try value.Arena.init(allocator);
    errdefer arena.deinit();

    if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x00 and bytes[3] == 0xEA) {
        const elements = try binary.parseTopLevel(&arena, bytes);
        return .{ .arena = arena, .elements = elements };
    } else if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x01 and bytes[3] == 0xEA) {
        const elements = try binary11.parseTopLevelWithMacroTable(&arena, bytes, mactab);
        return .{ .arena = arena, .elements = elements };
    } else {
        const decoded = try decodeTextToUtf8(allocator, bytes);
        defer if (decoded) |b| allocator.free(b);
        const input = if (decoded) |b| b else bytes;
        const elements = try text.parseTopLevelWithMacroTable(&arena, input, mactab);
        return .{ .arena = arena, .elements = elements };
    }
}

/// Parses a byte slice as Ion, but uses the Ion 1.1 conformance suite's "default module" symbol
/// model when parsing *text* Ion 1.1.
///
/// This is intended for the conformance runner only. The `iontestdata_1_1` corpus uses Ion 1.0-style
/// local symbol tables in text, so normal callers should continue to use `parseDocumentWithMacroTable`.
pub fn parseDocumentWithMacroTableIon11Modules(allocator: Allocator, bytes: []const u8, mactab: ?*const macro.MacroTable) IonError!Document {
    var arena = try value.Arena.init(allocator);
    errdefer arena.deinit();

    if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x00 and bytes[3] == 0xEA) {
        const elements = try binary.parseTopLevel(&arena, bytes);
        return .{ .arena = arena, .elements = elements };
    } else if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x01 and bytes[3] == 0xEA) {
        const elements = try binary11.parseTopLevelWithMacroTable(&arena, bytes, mactab);
        return .{ .arena = arena, .elements = elements };
    } else {
        const decoded = try decodeTextToUtf8(allocator, bytes);
        defer if (decoded) |b| allocator.free(b);
        const input = if (decoded) |b| b else bytes;
        const elements = try text.parseTopLevelWithMacroTableIon11Modules(&arena, input, mactab);
        return .{ .arena = arena, .elements = elements };
    }
}

pub const Binary11ParseOptions = struct {
    mactab: ?*const macro.MacroTable = null,
    sys_symtab11_variant: ?symtab.SystemSymtab11Variant = null,
    /// When true, rejects non-minimal FlexUInt/FlexInt encodings in Ion 1.1 binary.
    ///
    /// Note: `ion-tests` (especially conformance) intentionally uses non-canonical Flex encodings,
    /// so the default is `false` to keep the suite green.
    strict_flex: bool = false,
    /// When true, rejects conformance-driven opcode quirks that are not part of the Ion 1.1 binary
    /// opcode table (for example the `0x01` "tagged int 0" shortcut used by some conformance
    /// fixtures).
    strict_opcodes: bool = false,
};

/// Parses an Ion 1.1 binary stream that begins with the Ion 1.1 IVM (`E0 01 01 EA`).
///
/// This is useful when you want to:
/// - provide an out-of-band macro table, and/or
/// - force the Ion 1.1 system symbol table variant (`ion-tests` vs ion-rust) without relying on
///   `ION_ZIG_SYSTEM_SYMTAB11` or in-stream inference.
pub fn parseDocumentBinary11WithOptions(allocator: Allocator, bytes: []const u8, options: Binary11ParseOptions) IonError!Document {
    var arena = try value.Arena.init(allocator);
    errdefer arena.deinit();

    if (options.sys_symtab11_variant) |variant| {
        const res = try binary11.parseTopLevelWithMacroTableAndStateWithSystemSymtabVariantAndOptions(
            &arena,
            bytes,
            options.mactab,
            variant,
            .{ .strict_flex = options.strict_flex, .strict_opcodes = options.strict_opcodes },
        );
        return .{ .arena = arena, .elements = res.elements };
    }
    const res = try binary11.parseTopLevelWithMacroTableAndStateWithOptions(
        &arena,
        bytes,
        options.mactab,
        .{ .strict_flex = options.strict_flex, .strict_opcodes = options.strict_opcodes },
    );
    return .{ .arena = arena, .elements = res.elements };
}

fn decodeTextToUtf8(allocator: Allocator, bytes: []const u8) IonError!?[]u8 {
    if (bytes.len == 0) return null;

    const Encoding = enum { utf8, utf16le, utf16be, utf32le, utf32be };
    var enc: Encoding = .utf8;
    var start: usize = 0;

    // BOM detection.
    if (bytes.len >= 4 and std.mem.eql(u8, bytes[0..4], &.{ 0x00, 0x00, 0xFE, 0xFF })) {
        enc = .utf32be;
        start = 4;
    } else if (bytes.len >= 4 and std.mem.eql(u8, bytes[0..4], &.{ 0xFF, 0xFE, 0x00, 0x00 })) {
        enc = .utf32le;
        start = 4;
    } else if (bytes.len >= 3 and std.mem.eql(u8, bytes[0..3], &.{ 0xEF, 0xBB, 0xBF })) {
        enc = .utf8;
        start = 3;
    } else if (bytes.len >= 2 and std.mem.eql(u8, bytes[0..2], &.{ 0xFE, 0xFF })) {
        enc = .utf16be;
        start = 2;
    } else if (bytes.len >= 2 and std.mem.eql(u8, bytes[0..2], &.{ 0xFF, 0xFE })) {
        enc = .utf16le;
        start = 2;
    } else {
        // Heuristics for BOM-less UTF-16/32 (as in ion-tests fixtures).
        if (bytes.len >= 4 and bytes[0] == 0x00 and bytes[1] == 0x00 and bytes[2] == 0x00 and bytes[3] != 0x00) {
            enc = .utf32be;
        } else if (bytes.len >= 4 and bytes[0] != 0x00 and bytes[1] == 0x00 and bytes[2] == 0x00 and bytes[3] == 0x00) {
            enc = .utf32le;
        } else if (bytes.len >= 2 and bytes[0] == 0x00 and bytes[1] != 0x00) {
            enc = .utf16be;
        } else if (bytes.len >= 2 and bytes[0] != 0x00 and bytes[1] == 0x00) {
            enc = .utf16le;
        }
    }

    const body = bytes[start..];
    switch (enc) {
        .utf8 => return null,
        .utf16le, .utf16be => {
            if (body.len % 2 != 0) return IonError.InvalidIon;
            var out = std.ArrayListUnmanaged(u8){};
            errdefer out.deinit(allocator);

            var i: usize = 0;
            while (i < body.len) : (i += 2) {
                const u = if (enc == .utf16le)
                    std.mem.readInt(u16, @as(*const [2]u8, @ptrCast(body[i .. i + 2].ptr)), .little)
                else
                    std.mem.readInt(u16, @as(*const [2]u8, @ptrCast(body[i .. i + 2].ptr)), .big);

                var codepoint: u21 = 0;
                if (u >= 0xD800 and u <= 0xDBFF) {
                    // High surrogate: must be followed by low surrogate.
                    if (i + 4 > body.len) return IonError.InvalidIon;
                    const u_next = if (enc == .utf16le)
                        std.mem.readInt(u16, @as(*const [2]u8, @ptrCast(body[i + 2 .. i + 4].ptr)), .little)
                    else
                        std.mem.readInt(u16, @as(*const [2]u8, @ptrCast(body[i + 2 .. i + 4].ptr)), .big);
                    if (u_next < 0xDC00 or u_next > 0xDFFF) return IonError.InvalidIon;
                    const hi: u32 = u - 0xD800;
                    const lo: u32 = u_next - 0xDC00;
                    const cp: u32 = 0x10000 + ((hi << 10) | lo);
                    codepoint = @intCast(cp);
                    i += 2;
                } else if (u >= 0xDC00 and u <= 0xDFFF) {
                    return IonError.InvalidIon;
                } else {
                    codepoint = @intCast(u);
                }

                var buf: [4]u8 = undefined;
                const n = std.unicode.utf8Encode(codepoint, &buf) catch return IonError.InvalidIon;
                out.appendSlice(allocator, buf[0..n]) catch return IonError.OutOfMemory;
            }

            return out.toOwnedSlice(allocator) catch return IonError.OutOfMemory;
        },
        .utf32le, .utf32be => {
            if (body.len % 4 != 0) return IonError.InvalidIon;
            var out = std.ArrayListUnmanaged(u8){};
            errdefer out.deinit(allocator);

            var i: usize = 0;
            while (i < body.len) : (i += 4) {
                const u = if (enc == .utf32le)
                    std.mem.readInt(u32, @as(*const [4]u8, @ptrCast(body[i .. i + 4].ptr)), .little)
                else
                    std.mem.readInt(u32, @as(*const [4]u8, @ptrCast(body[i .. i + 4].ptr)), .big);

                // Validate Unicode scalar value (exclude surrogate range).
                if (u > 0x10FFFF or (u >= 0xD800 and u <= 0xDFFF)) return IonError.InvalidIon;

                var buf: [4]u8 = undefined;
                const n = std.unicode.utf8Encode(@intCast(u), &buf) catch return IonError.InvalidIon;
                out.appendSlice(allocator, buf[0..n]) catch return IonError.OutOfMemory;
            }

            return out.toOwnedSlice(allocator) catch return IonError.OutOfMemory;
        },
    }
}

/// Output format selector for `serializeDocument`.
pub const Format = enum(u32) {
    /// Ion binary (Ion 1.0).
    binary = 0,
    /// Ion binary (Ion 1.1).
    ///
    /// Note: this uses the experimental Ion 1.1 binary writer (`zig/src/ion/writer11.zig`).
    /// It emits values (not macros/e-expressions), and may emit a minimal module prelude
    /// (`$ion::(module ...)`) so non-system symbols can be encoded by address in a self-contained
    /// stream.
    binary_1_1 = 4,
    /// Ion 1.1 binary without forcing a self-contained module prelude.
    ///
    /// This is useful for writing bytes that rely on external module state (for example: SID-only
    /// user symbols). When in doubt, prefer `binary_1_1`.
    binary_1_1_raw = 5,
    /// Ion text (writer currently shares implementation; formatting is not distinguished).
    text_compact = 1,
    /// Ion text (writer currently shares implementation; formatting is not distinguished).
    text_lines = 2,
    /// Ion text (writer currently shares implementation; formatting is not distinguished).
    text_pretty = 3,
};

/// Serializes a sequence of top-level Ion elements to the requested format.
///
/// Ownership: returns an allocated `[]u8` owned by `allocator`; caller must free it.
pub fn serializeDocument(allocator: Allocator, format: Format, doc: []const value.Element) IonError![]u8 {
    return switch (format) {
        .binary => try writer.writeBinary(allocator, doc),
        .binary_1_1 => try writer11.writeBinary11SelfContained(allocator, doc),
        .binary_1_1_raw => try writer11.writeBinary11WithOptions(allocator, doc, .{ .symbol_encoding = .addresses }),
        .text_compact, .text_lines, .text_pretty => try writer.writeText(allocator, doc),
    };
}

/// Serializes a sequence of top-level Ion elements as Ion 1.1 binary using `writer11` options.
///
/// This writes values (not macros/e-expressions). If you want deterministic self-contained output,
/// use `serializeDocument(..., .binary_1_1, ...)` or call `writer11.writeBinary11SelfContained`.
pub fn serializeDocumentBinary11WithOptions(
    allocator: Allocator,
    doc: []const value.Element,
    options: writer11.Options,
) IonError![]u8 {
    return writer11.writeBinary11WithOptions(allocator, doc, options);
}

/// Serializes a sequence of top-level Ion elements as *self-contained* Ion 1.1 binary using
/// `writer11` options.
///
/// This writes values (not macros/e-expressions). It emits a minimal `$ion::(module ...)` prelude
/// when needed so user symbols can be encoded by address deterministically.
pub fn serializeDocumentBinary11SelfContainedWithOptions(
    allocator: Allocator,
    doc: []const value.Element,
    options: writer11.Options,
) IonError![]u8 {
    return writer11.writeBinary11SelfContainedWithOptions(allocator, doc, options);
}
