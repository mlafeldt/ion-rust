const std = @import("std");
const ion = @import("../ion.zig");

pub const CatalogError = error{
    InvalidIon,
    OutOfMemory,
    FileNotFound,
    Unsupported,
};

pub const SharedSymtabEntry = struct {
    name: []const u8,
    version: u32,
    /// Index 0 corresponds to shared SID 1.
    symbols: []const ?[]const u8,
};

pub const Catalog = struct {
    doc: ion.Document,
    entries: []SharedSymtabEntry,

    pub fn deinit(self: *Catalog) void {
        self.doc.deinit();
    }

    pub fn lookupSharedSymtab(self: *const Catalog, name: []const u8, version: u32) ?SharedSymtabEntry {
        for (self.entries) |e| {
            if (e.version == version and std.mem.eql(u8, e.name, name)) return e;
        }
        return null;
    }

    pub fn bestSharedSymtabForName(self: *const Catalog, name: []const u8) ?SharedSymtabEntry {
        var best: ?SharedSymtabEntry = null;
        for (self.entries) |e| {
            if (!std.mem.eql(u8, e.name, name)) continue;
            if (best == null or e.version > best.?.version) best = e;
        }
        return best;
    }
};

pub fn loadIonTestsCatalog(allocator: std.mem.Allocator, path: []const u8) CatalogError!Catalog {
    const raw = std.fs.cwd().readFileAlloc(allocator, path, 16 * 1024 * 1024) catch |e| switch (e) {
        error.FileNotFound => return CatalogError.FileNotFound,
        error.OutOfMemory => return CatalogError.OutOfMemory,
        else => return CatalogError.Unsupported,
    };
    defer allocator.free(raw);

    // `ion.parseDocument(...)` treats `$ion_shared_symbol_table::{...}` as a system value and
    // consumes it into internal parser state (meaning it won't be returned in `Document.elements`).
    // For catalog loading we want these values as data, so we inject `$ion_literal::` to force them
    // to be returned as user values and then stripped back out by the parser.
    const patched = try injectIonLiteralBeforeSystemAnnotation(allocator, raw, "$ion_shared_symbol_table::");
    defer allocator.free(patched);

    var doc = ion.parseDocument(allocator, patched) catch return CatalogError.InvalidIon;
    errdefer doc.deinit();

    const a = doc.arena.allocator();

    var out = std.ArrayListUnmanaged(SharedSymtabEntry){};
    errdefer out.deinit(a);

    for (doc.elements) |elem| {
        if (elem.value != .@"struct") continue;
        if (elem.annotations.len == 0) continue;
        const ann0 = elem.annotations[0].text orelse continue;
        if (!std.mem.eql(u8, ann0, "$ion_shared_symbol_table")) continue;

        var name: ?[]const u8 = null;
        var version: ?u32 = null;
        var symbols: ?[]const ?[]const u8 = null;

        const st = elem.value.@"struct";
        for (st.fields) |f| {
            const fname = f.name.text orelse continue;
            if (std.mem.eql(u8, fname, "name")) {
                if (f.value.value != .string) continue;
                name = f.value.value.string;
            } else if (std.mem.eql(u8, fname, "version")) {
                if (f.value.value != .int) continue;
                switch (f.value.value.int) {
                    .small => |v| {
                        if (v <= 0 or v > std.math.maxInt(u32)) continue;
                        version = @intCast(v);
                    },
                    else => continue,
                }
            } else if (std.mem.eql(u8, fname, "symbols")) {
                if (f.value.value != .list) continue;
                const items = f.value.value.list;
                const syms = a.alloc(?[]const u8, items.len) catch return CatalogError.OutOfMemory;
                for (items, 0..) |it, idx| {
                    syms[idx] = switch (it.value) {
                        .string => |s| s,
                        .null => null,
                        // `ion-tests/catalog/catalog.ion` uses the token `absent` to denote a gap.
                        .symbol => |s| blk: {
                            const t = s.text orelse break :blk null;
                            if (std.mem.eql(u8, t, "absent")) break :blk null;
                            break :blk null;
                        },
                        else => null,
                    };
                }
                symbols = syms;
            }
        }

        const n = name orelse continue;
        const v = version orelse continue;
        const s = symbols orelse continue;
        out.append(a, .{ .name = n, .version = v, .symbols = s }) catch return CatalogError.OutOfMemory;
    }

    return .{
        .doc = doc,
        .entries = out.toOwnedSlice(a) catch return CatalogError.OutOfMemory,
    };
}

fn injectIonLiteralBeforeSystemAnnotation(
    allocator: std.mem.Allocator,
    input: []const u8,
    needle: []const u8,
) CatalogError![]u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    var i: usize = 0;
    while (i < input.len) {
        if (std.mem.indexOfPos(u8, input, i, needle)) |pos| {
            out.appendSlice(allocator, input[i..pos]) catch return CatalogError.OutOfMemory;
            out.appendSlice(allocator, "$ion_literal::") catch return CatalogError.OutOfMemory;
            out.appendSlice(allocator, needle) catch return CatalogError.OutOfMemory;
            i = pos + needle.len;
            continue;
        }
        out.appendSlice(allocator, input[i..]) catch return CatalogError.OutOfMemory;
        break;
    }

    return out.toOwnedSlice(allocator) catch return CatalogError.OutOfMemory;
}
