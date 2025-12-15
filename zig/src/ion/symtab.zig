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

/// Mutable symbol table used by the parsers to resolve SIDs to text.
pub const SymbolTable = struct {
    arena: *value.Arena,
    // Index is SID; entry is optional text (null => unknown slot).
    sid_to_text: std.ArrayListUnmanaged(?[]const u8) = .{},

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
        return st;
    }

    /// Frees backing allocations (owned by the arena).
    pub fn deinit(self: *SymbolTable) void {
        self.sid_to_text.deinit(self.arena.allocator());
    }

    /// Returns the maximum SID currently defined in the table.
    pub fn maxId(self: *const SymbolTable) u32 {
        return @intCast(self.sid_to_text.items.len - 1);
    }

    /// Returns the text for a SID if known (null if unknown/out of range).
    pub fn textForSid(self: *const SymbolTable, sid: u32) ?[]const u8 {
        if (sid >= self.sid_to_text.items.len) return null;
        return self.sid_to_text.items[@intCast(sid)];
    }

    /// Returns the slot for a SID:
    /// - null => SID is out of range (undefined)
    /// - ?[]const u8 => defined, with optional text (null => unknown slot)
    pub fn slotForSid(self: *const SymbolTable, sid: u32) ?(?[]const u8) {
        if (sid >= self.sid_to_text.items.len) return null;
        return self.sid_to_text.items[@intCast(sid)];
    }

    /// Appends a new symbol text slot and returns its assigned SID.
    pub fn addSymbolText(self: *SymbolTable, text: []const u8) IonError!u32 {
        const owned = try self.arena.dupe(text);
        self.sid_to_text.append(self.arena.allocator(), owned) catch return IonError.OutOfMemory;
        return self.maxId();
    }

    /// Appends an unknown (null) slot and returns its assigned SID.
    pub fn addNullSlot(self: *SymbolTable) IonError!u32 {
        self.sid_to_text.append(self.arena.allocator(), null) catch return IonError.OutOfMemory;
        return self.maxId();
    }
};
