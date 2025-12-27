//! Symbol table support for the Zig Ion implementation.
//!
//! - `SystemSymtab` provides the Ion 1.0 system symbol IDs and their text.
//! - `SymbolTable` models the current (system + local) SID->text mapping while parsing.

const std = @import("std");
const IonError = @import("../ion.zig").IonError;
const value = @import("value.zig");

/// Ion 1.0 system symbol table (SIDs 1..max_id).
pub const SystemSymtab = struct {
    // SID 0 is reserved ($0 / unknown).
    pub const max_id: u32 = 9;

    pub const symbols = [_][]const u8{
        "$0",
        "$ion",
        "$ion_1_0",
        "$ion_symbol_table",
        "name",
        "version",
        "imports",
        "symbols",
        "max_id",
        "$ion_shared_symbol_table",
    };

    /// Returns the system SID for a symbol text, or null if not a system symbol.
    pub fn sidForText(text: []const u8) ?u32 {
        // linear is fine at this size
        var sid: u32 = 1;
        while (sid <= max_id) : (sid += 1) {
            if (std.mem.eql(u8, symbols[sid], text)) return sid;
        }
        return null;
    }

    /// Returns the system symbol text for a SID, or null if not a system SID.
    pub fn textForSid(sid: u32) ?[]const u8 {
        if (sid == 0 or sid > max_id) return null;
        return symbols[sid];
    }
};

/// Ion 1.1 system symbol table.
/// This is currently only used by the Ion 1.1 conformance suite runner.
pub const SystemSymtab11 = struct {
    // NOTE: This table matches the expectations in `ion-tests/conformance/system_symbols.ion`.
    // Ion-rust uses a different (newer) Ion 1.1 system symbol table that includes `symbol_table`
    // and has 63 symbols. When interoperating with ion-rust's Ion 1.1 binary writer, prefer its
    // address-to-text mapping as the source of truth.
    pub const max_id: u32 = 62;

    pub const symbols = [_][]const u8{
        "$0",
        "$ion",
        "$ion_1_0",
        "$ion_symbol_table",
        "name",
        "version",
        "imports",
        "symbols",
        "max_id",
        "$ion_shared_symbol_table",
        "encoding",
        "$ion_literal",
        "$ion_shared_module",
        "macro",
        "macro_table",
        "module",
        "export",
        "import",
        "flex_symbol",
        "flex_int",
        "flex_uint",
        "uint8",
        "uint16",
        "uint32",
        "uint64",
        "int8",
        "int16",
        "int32",
        "int64",
        "float16",
        "float32",
        "float64",
        "",
        "for",
        "literal",
        "if_none",
        "if_some",
        "if_single",
        "if_multi",
        "none",
        "values",
        "default",
        "meta",
        "repeat",
        "flatten",
        "delta",
        "sum",
        "annotate",
        "make_string",
        "make_symbol",
        "make_decimal",
        "make_timestamp",
        "make_blob",
        "make_list",
        "make_sexp",
        "make_field",
        "make_struct",
        "parse_ion",
        "set_symbols",
        "add_symbols",
        "set_macros",
        "add_macros",
        "use",
    };

    pub fn textForSid(sid: u32) ?[]const u8 {
        if (sid == 0 or sid > max_id) return null;
        return symbols[sid];
    }

    /// Returns the system SID for a symbol text, or null if not a system symbol.
    pub fn sidForText(text: []const u8) ?u32 {
        // Linear scan is fine at this size.
        var sid: u32 = 1;
        while (sid <= max_id) : (sid += 1) {
            if (std.mem.eql(u8, symbols[sid], text)) return sid;
        }
        return null;
    }
};

/// Mutable symbol table used by the parsers to resolve SIDs to text.
pub const SymbolTable = struct {
    arena: *value.Arena,
    // Highest SID that is defined in this table. Note that we may not materialize all slots up to
    // this value (imports can declare very large `max_id` values).
    declared_max_id: u32 = 0,
    // Dense mapping for small/contiguous SIDs. Index is SID; entry is optional text
    // (null => unknown slot).
    sid_to_text: std.ArrayListUnmanaged(?[]const u8) = .{},
    // Sparse mapping for known text at large SIDs.
    sid_to_text_sparse: std.AutoHashMapUnmanaged(u32, []const u8) = .{},

    /// Initializes the table with all system symbols populated.
    pub fn init(arena: *value.Arena) IonError!SymbolTable {
        var st = SymbolTable{ .arena = arena };
        // Pre-fill system IDs up to max_id.
        st.sid_to_text.ensureTotalCapacity(arena.allocator(), SystemSymtab.max_id + 1) catch return IonError.OutOfMemory;
        st.sid_to_text.items.len = 0;
        // SID 0
        st.sid_to_text.appendAssumeCapacity(null);
        var sid: u32 = 1;
        while (sid <= SystemSymtab.max_id) : (sid += 1) {
            st.sid_to_text.appendAssumeCapacity(SystemSymtab.textForSid(sid).?);
        }
        st.declared_max_id = SystemSymtab.max_id;
        return st;
    }

    /// Frees backing allocations (owned by the arena).
    pub fn deinit(self: *SymbolTable) void {
        self.sid_to_text.deinit(self.arena.allocator());
        self.sid_to_text_sparse.deinit(self.arena.allocator());
    }

    /// Returns the maximum SID currently defined in the table.
    pub fn maxId(self: *const SymbolTable) u32 {
        return self.declared_max_id;
    }

    /// Returns the text for a SID if known (null if unknown/out of range).
    pub fn textForSid(self: *const SymbolTable, sid: u32) ?[]const u8 {
        if (sid < self.sid_to_text.items.len) return self.sid_to_text.items[@intCast(sid)];
        if (self.sid_to_text_sparse.get(sid)) |t| return t;
        return null;
    }

    /// Returns the slot for a SID:
    /// - null => SID is out of range (undefined)
    /// - ?[]const u8 => defined, with optional text (null => unknown slot)
    pub fn slotForSid(self: *const SymbolTable, sid: u32) ?(?[]const u8) {
        if (sid < self.sid_to_text.items.len) return self.sid_to_text.items[@intCast(sid)];
        if (self.sid_to_text_sparse.get(sid)) |t| return t;
        if (sid <= self.declared_max_id) return @as(?[]const u8, null);
        return null;
    }

    /// Appends a new symbol text slot and returns its assigned SID.
    pub fn addSymbolText(self: *SymbolTable, text: []const u8) IonError!u32 {
        const owned = try self.arena.dupe(text);
        if (self.declared_max_id == std.math.maxInt(u32)) return IonError.InvalidIon;
        const new_sid: u32 = self.declared_max_id + 1;
        self.declared_max_id = new_sid;

        if (new_sid == self.sid_to_text.items.len) {
            self.sid_to_text.append(self.arena.allocator(), owned) catch return IonError.OutOfMemory;
        } else if (new_sid < self.sid_to_text.items.len) {
            self.sid_to_text.items[@intCast(new_sid)] = owned;
        } else {
            self.sid_to_text_sparse.put(self.arena.allocator(), new_sid, owned) catch return IonError.OutOfMemory;
        }
        return new_sid;
    }

    /// Appends an unknown (null) slot and returns its assigned SID.
    pub fn addNullSlot(self: *SymbolTable) IonError!u32 {
        if (self.declared_max_id == std.math.maxInt(u32)) return IonError.InvalidIon;
        const new_sid: u32 = self.declared_max_id + 1;
        self.declared_max_id = new_sid;

        if (new_sid == self.sid_to_text.items.len) {
            self.sid_to_text.append(self.arena.allocator(), null) catch return IonError.OutOfMemory;
        } else if (new_sid < self.sid_to_text.items.len) {
            self.sid_to_text.items[@intCast(new_sid)] = null;
        }
        // For sparse/very large SIDs, unknown slots are implicit.
        return new_sid;
    }

    pub fn addImport(self: *SymbolTable, symbols: []const ?[]const u8, import_max_id: u32) IonError!void {
        if (import_max_id == 0) return;
        if (import_max_id > std.math.maxInt(u32) - self.declared_max_id) return IonError.InvalidIon;

        const base: u32 = self.declared_max_id;
        self.declared_max_id = base + import_max_id;

        const take: u32 = @intCast(@min(@as(usize, import_max_id), symbols.len));
        var sid_in_table: u32 = 1;
        while (sid_in_table <= take) : (sid_in_table += 1) {
            const idx: usize = @intCast(sid_in_table - 1);
            if (symbols[idx]) |t| {
                const owned = try self.arena.dupe(t);
                const sid: u32 = base + sid_in_table;
                if (sid == self.sid_to_text.items.len) {
                    self.sid_to_text.append(self.arena.allocator(), owned) catch return IonError.OutOfMemory;
                } else if (sid < self.sid_to_text.items.len) {
                    self.sid_to_text.items[@intCast(sid)] = owned;
                } else {
                    self.sid_to_text_sparse.put(self.arena.allocator(), sid, owned) catch return IonError.OutOfMemory;
                }
            }
        }
    }
};
