//! Ion value model for the Zig port.
//!
//! This file defines:
//! - `Arena`: an arena allocator used to own all decoded values.
//! - `Value`/`Element`: the in-memory representation used by the parsers and writers.
//! - `Symbol`: symbols may have an optional `sid` and optional `text`.

const std = @import("std");
const IonError = @import("../ion.zig").IonError;
const big = std.math.big.int;

/// Arena allocator used by the parser to allocate all decoded values for a document.
pub const Arena = struct {
    gpa: std.mem.Allocator,
    arena: std.heap.ArenaAllocator,

    /// Initializes an arena backed by `gpa`.
    pub fn init(gpa: std.mem.Allocator) !Arena {
        const arena = std.heap.ArenaAllocator.init(gpa);
        return .{ .gpa = gpa, .arena = arena };
    }

    /// Returns an allocator that allocates from this arena.
    pub fn allocator(self: *Arena) std.mem.Allocator {
        return self.arena.allocator();
    }

    /// Duplicates a byte slice into the arena.
    pub fn dupe(self: *Arena, bytes: []const u8) IonError![]const u8 {
        return self.allocator().dupe(u8, bytes) catch return IonError.OutOfMemory;
    }

    /// Frees all allocations made in the arena.
    pub fn deinit(self: *Arena) void {
        self.arena.deinit();
    }
};

/// Ion type tags used by `Value`.
pub const IonType = enum {
    null,
    bool,
    int,
    float,
    decimal,
    timestamp,
    symbol,
    string,
    clob,
    blob,
    list,
    sexp,
    @"struct",
};

/// Ion symbol representation.
///
/// - `sid` is set for symbols created from `$<id>` (text) or from binary Ion.
/// - `text` is set for symbols with known text (identifiers, quoted symbols, or resolved SIDs).
pub const Symbol = struct {
    // `sid` is present for symbols created from $<id> (text) or from binary Ion.
    // `text` is present for symbols with known text (identifiers, quoted symbols, or resolved SIDs).
    sid: ?u32,
    text: ?[]const u8,
};

/// Annotation list (each annotation is a `Symbol`).
pub const Annotations = []Symbol;

/// Ion decimal representation (strict / representation-sensitive).
pub const Decimal = struct {
    // Strict representation; Ion equivalence is representation-sensitive.
    is_negative: bool,
    // Always stores the magnitude (non-negative). The sign is stored separately in `is_negative`
    // so we can represent negative zero.
    coefficient: Int,
    exponent: i32,
};

/// Ion integer representation.
pub const Int = union(enum) {
    small: i128,
    big: big.Managed,
};

/// Ion timestamp representation (strict / representation-sensitive where applicable).
pub const Timestamp = struct {
    // Minimal strict representation: keep parsed fields and original offset info.
    // `offset_minutes` null means unknown offset (-00:00 in Ion).
    year: i32,
    month: ?u8,
    day: ?u8,
    hour: ?u8,
    minute: ?u8,
    second: ?u8,
    fractional: ?Decimal, // fractional seconds as a Decimal (representation-sensitive)
    offset_minutes: ?i16,
    // Tracks the finest precision present in the source.
    precision: enum { year, month, day, minute, second, fractional },
};

/// Struct field: `{ name: value }`.
pub const StructField = struct {
    name: Symbol,
    value: Element,
};

/// Ion struct value.
pub const Struct = struct {
    fields: []StructField,
};

/// Ion value union.
pub const Value = union(IonType) {
    null: IonType, // typed null; value is IonType tag of the null (or .null)
    bool: bool,
    int: Int,
    float: f64,
    decimal: Decimal,
    timestamp: Timestamp,
    symbol: Symbol,
    string: []const u8,
    clob: []const u8,
    blob: []const u8,
    list: []Element,
    sexp: []Element,
    @"struct": Struct,
};

/// Ion element: a value plus optional annotations.
pub const Element = struct {
    annotations: Annotations,
    value: Value,
};

/// Creates a symbol with known text (duplicated into the arena).
pub fn makeSymbol(arena: *Arena, text: []const u8) IonError!Symbol {
    return .{ .sid = null, .text = try arena.dupe(text) };
}

/// Creates a symbol with an optional SID and optional text.
pub fn makeSymbolId(sid: ?u32, text: ?[]const u8) Symbol {
    return .{ .sid = sid, .text = text };
}

/// Returns the unknown symbol (`$0`), i.e. `sid = 0` and no text.
pub fn unknownSymbol() Symbol {
    return .{ .sid = 0, .text = null };
}
