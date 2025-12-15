//! Minimal Ion 1.0 reader/writer in Zig.
//!
//! Public entrypoints:
//! - `parseDocument(allocator, bytes)` parses either Ion text or Ion binary (IVM-detected).
//! - `serializeDocument(allocator, format, elements)` writes Ion text or Ion binary.

pub const value = @import("ion/value.zig");
pub const symtab = @import("ion/symtab.zig");
pub const text = @import("ion/text.zig");
pub const binary = @import("ion/binary.zig");
pub const writer = @import("ion/writer.zig");
pub const eq = @import("ion/eq.zig");

pub const IonError = error{
    InvalidIon,
    Incomplete,
    Unsupported,
    OutOfMemory,
};

pub const Allocator = @import("std").mem.Allocator;

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
    var arena = try value.Arena.init(allocator);
    errdefer arena.deinit();

    if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x00 and bytes[3] == 0xEA) {
        const elements = try binary.parseTopLevel(&arena, bytes);
        return .{ .arena = arena, .elements = elements };
    } else {
        const elements = try text.parseTopLevel(&arena, bytes);
        return .{ .arena = arena, .elements = elements };
    }
}

/// Output format selector for `serializeDocument`.
pub const Format = enum(u32) {
    /// Ion binary (Ion 1.0).
    binary = 0,
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
        .text_compact, .text_lines, .text_pretty => try writer.writeText(allocator, doc),
    };
}
