//! Ion value model for the Zig port.
//!
//! This file defines:
//! - `Arena`: an arena allocator used to own all decoded values.
//! - `Value`/`Element`: the in-memory representation used by the parsers and writers.
//! - `Symbol`: symbols may have an optional `sid` and optional `text`.

const std = @import("std");
const IonError = @import("../ion.zig").IonError;
const big = std.math.big.int;
const Limb = std.math.big.Limb;
const symtab = @import("symtab.zig");

/// Arena allocator used by the parser to allocate all decoded values for a document.
pub const Arena = struct {
    gpa: std.mem.Allocator,
    arena: std.heap.ArenaAllocator,
    bigints: std.ArrayListUnmanaged(*big.Managed) = .{},

    /// Initializes an arena backed by `gpa`.
    pub fn init(gpa: std.mem.Allocator) !Arena {
        const arena = std.heap.ArenaAllocator.init(gpa);
        return .{ .gpa = gpa, .arena = arena };
    }

    /// Returns an allocator that allocates from this arena.
    pub fn allocator(self: *Arena) std.mem.Allocator {
        return self.arena.allocator();
    }

    pub fn makeBigInt(self: *Arena) IonError!*big.Managed {
        const p = self.allocator().create(big.Managed) catch return IonError.OutOfMemory;
        p.* = big.Managed.init(self.gpa) catch return IonError.OutOfMemory;
        self.bigints.append(self.gpa, p) catch return IonError.OutOfMemory;
        return p;
    }

    /// Duplicates a byte slice into the arena.
    pub fn dupe(self: *Arena, bytes: []const u8) IonError![]const u8 {
        return self.allocator().dupe(u8, bytes) catch return IonError.OutOfMemory;
    }

    /// Frees all allocations made in the arena.
    pub fn deinit(self: *Arena) void {
        for (self.bigints.items) |p| p.deinit();
        self.bigints.deinit(self.gpa);
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
    big: *big.Managed,
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

pub fn resolveSystemSymbols11(arena: *Arena, elems: []Element) IonError!void {
    for (elems) |*e| try resolveElement11(arena, e);
}

fn resolveElement11(arena: *Arena, e: *Element) IonError!void {
    for (e.annotations) |*a| try resolveSymbol11(arena, a);
    try resolveValue11(arena, &e.value);
}

fn resolveValue11(arena: *Arena, v: *Value) IonError!void {
    switch (v.*) {
        .symbol => |*s| try resolveSymbol11(arena, s),
        .list => |items| for (items) |*e| try resolveElement11(arena, e),
        .sexp => |items| for (items) |*e| try resolveElement11(arena, e),
        .@"struct" => |st| {
            for (st.fields) |*f| {
                try resolveSymbol11(arena, &f.name);
                try resolveElement11(arena, &f.value);
            }
        },
        else => {},
    }
}

fn resolveSymbol11(arena: *Arena, s: *Symbol) IonError!void {
    if (s.text != null) return;
    const sid = s.sid orelse return;
    if (symtab.SystemSymtab11.textForSid(sid)) |t| {
        s.text = try arena.dupe(t);
    }
}

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

pub fn setBigIntFromUnsignedDecimalDigitsFast(dst: *big.Managed, digits: []const u8) IonError!void {
    if (digits.len == 0) {
        dst.set(@as(u8, 0)) catch return IonError.OutOfMemory;
        return;
    }

    // `big.Managed.setString(10, digits)` is O(n) multiplications by 10, which is extremely slow for
    // the corpus' very large decimal literals (thousands of digits). Chunking reduces the number of
    // BigInt operations by ~18x.
    const chunk_digits: usize = 18;
    const chunk_base: u64 = 1_000_000_000_000_000_000; // 10^18 (fits in u64 and Limb on 64-bit targets)

    dst.ensureCapacity(big.calcSetStringLimbCount(10, digits.len)) catch return IonError.OutOfMemory;
    const limbs_buffer = dst.allocator.alloc(Limb, big.calcSetStringLimbsBufferLen(10, digits.len)) catch return IonError.OutOfMemory;
    defer dst.allocator.free(limbs_buffer);

    var m = dst.toMutable();

    var first_len: usize = digits.len % chunk_digits;
    if (first_len == 0) first_len = chunk_digits;
    const first_chunk = digits[0..first_len];
    const first_val = std.fmt.parseInt(u64, first_chunk, 10) catch return IonError.InvalidIon;
    m.set(first_val);

    const base_limb: Limb = @intCast(chunk_base);
    const base_const: big.Const = .{ .limbs = (&base_limb)[0..1], .positive = true };

    var pos: usize = first_len;
    while (pos < digits.len) : (pos += chunk_digits) {
        const part = digits[pos .. pos + chunk_digits];
        const part_val = std.fmt.parseInt(u64, part, 10) catch return IonError.InvalidIon;

        // Pass `null` allocator: for 1-limb multipliers (base 10^18) the fallback algorithm is
        // plenty fast and avoids allocator churn.
        m.mul(m.toConst(), base_const, limbs_buffer, null);

        var part_limb: Limb = @intCast(part_val);
        const part_const: big.Const = .{ .limbs = (&part_limb)[0..1], .positive = true };
        m.add(m.toConst(), part_const);
    }

    dst.setMetadata(m.positive, m.len);
}
