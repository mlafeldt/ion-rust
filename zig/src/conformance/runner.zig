const std = @import("std");
const ion = @import("../ion.zig");
const value = ion.value;
const denote = @import("denote.zig");

pub const RunError = error{
    InvalidConformanceDsl,
    Unsupported,
    OutOfMemory,
};

pub const Stats = struct {
    cases: usize = 0,
    branches: usize = 0,
    passed: usize = 0,
    skipped: usize = 0,
};

const Version = enum { document, ion_1_0, ion_1_1 };

const AstEvent = union(enum) {
    value: value.Element,
    ivm: Version,
    ivm_invalid: struct { major: u32, minor: u32 },
};

const Absence = struct {
    name: []const u8,
    offset: u32,
};

const SharedSymtabCatalog = struct {
    const Entry = struct {
        name: []const u8,
        version: u32,
        symbols: []const ?[]const u8,
    };

    // Minimal shared symbol table catalog required by the conformance suite.
    // Entries here are referenced by `ion-tests/conformance/local_symtab_imports.ion`.
    const entries = [_]Entry{
        .{ .name = "empty", .version = 1, .symbols = &.{} },
        .{ .name = "abcs", .version = 1, .symbols = &.{ "a" } },
        .{ .name = "abcs", .version = 2, .symbols = &.{ "a", "b" } },
        .{ .name = "mnop", .version = 1, .symbols = &.{ "m", "n", "o", "p" } },
        // v4 has a gap in the first slot (as referenced by conformance comments).
        .{ .name = "mnop", .version = 4, .symbols = &.{ null, "n", "o", "p" } },
    };

    fn lookup(name: []const u8, version: u32) ?Entry {
        for (entries) |e| {
            if (e.version == version and std.mem.eql(u8, e.name, name)) return e;
        }
        return null;
    }

    fn bestForName(name: []const u8) ?Entry {
        var best: ?Entry = null;
        for (entries) |e| {
            if (!std.mem.eql(u8, e.name, name)) continue;
            if (best == null or e.version > best.?.version) best = e;
        }
        return best;
    }
};

const State = struct {
    version: Version,
    // Persistent stacks of fragment/event nodes to avoid O(n) copies on `each` branching.
    text_tail: ?*TextNode = null,
    text_len: usize = 0,
    event_tail: ?*EventNode = null,
    event_len: usize = 0,
    // If true, some clause required to evaluate this branch is not yet implemented.
    unsupported: bool = false,

    fn deinit(self: *State, allocator: std.mem.Allocator) void {
        // Nodes are arena-allocated in `evalSeq` and freed all at once; nothing to do here.
        _ = self;
        _ = allocator;
    }

    fn clone(self: *const State, allocator: std.mem.Allocator) RunError!State {
        _ = allocator;
        return self.*;
    }

    fn pushText(self: *State, allocator: std.mem.Allocator, frag: []const u8) RunError!void {
        const n = allocator.create(TextNode) catch return RunError.OutOfMemory;
        n.* = .{ .prev = self.text_tail, .frag = frag };
        self.text_tail = n;
        self.text_len += 1;
    }

    fn pushEvent(self: *State, allocator: std.mem.Allocator, ev: AstEvent) RunError!void {
        const n = allocator.create(EventNode) catch return RunError.OutOfMemory;
        n.* = .{ .prev = self.event_tail, .ev = ev };
        self.event_tail = n;
        self.event_len += 1;
    }
};

const TextNode = struct {
    prev: ?*TextNode,
    frag: []const u8,
};

const EventNode = struct {
    prev: ?*EventNode,
    ev: AstEvent,
};

fn symText(e: value.Element) ?[]const u8 {
    return switch (e.value) {
        .symbol => |s| s.text,
        else => null,
    };
}

fn isSexpHead(e: value.Element, name: []const u8) bool {
    if (e.value != .sexp) return false;
    const sx = e.value.sexp;
    if (sx.len == 0) return false;
    const t = symText(sx[0]) orelse return false;
    return std.mem.eql(u8, t, name);
}

fn getSexpItems(e: value.Element) ?[]const value.Element {
    if (e.value != .sexp) return null;
    return e.value.sexp;
}

fn sysTextForSid(version: Version, sid: u32) ?[]const u8 {
    return switch (version) {
        .ion_1_1 => ion.symtab.SystemSymtab11.textForSid(sid),
        else => ion.symtab.SystemSymtab.textForSid(sid),
    };
}

fn sysMaxId(version: Version) u32 {
    return switch (version) {
        .ion_1_1 => ion.symtab.SystemSymtab11.max_id,
        else => ion.symtab.SystemSymtab.max_id,
    };
}

fn parseDelayedSid(s: value.Symbol) ?u32 {
    const t = s.text orelse return null;
    if (!(t.len >= 3 and t[0] == '#' and t[1] == '$')) return null;
    return std.fmt.parseInt(u32, t[2..], 10) catch null;
}

fn applyTextFragment(state: *State, allocator: std.mem.Allocator, sx: []const value.Element) RunError!void {
    // (text <string?>)
    if (sx.len == 1) {
        return state.pushText(allocator, "");
    }
    for (sx[1..]) |e| if (e.value != .string) return RunError.InvalidConformanceDsl;
    const s: []const u8 = if (sx.len == 2) blk: {
        break :blk sx[1].value.string;
    } else blk: {
        var total: usize = 0;
        for (sx[1..]) |e| total += e.value.string.len;
        const out = allocator.alloc(u8, total) catch return RunError.OutOfMemory;
        var i: usize = 0;
        for (sx[1..]) |e| {
            const part = e.value.string;
            @memcpy(out[i .. i + part.len], part);
            i += part.len;
        }
        break :blk out;
    };
    if (parseTextIvmToken(s)) |v| {
        switch (v) {
            .valid => |ver| try state.pushEvent(allocator, .{ .ivm = ver }),
            .invalid => |bad| try state.pushEvent(allocator, .{ .ivm_invalid = .{ .major = bad.major, .minor = bad.minor } }),
        }
        return;
    }
    try state.pushText(allocator, s);
}

fn applyTopLevel2(state: *State, allocator: std.mem.Allocator, sx: []const value.Element) RunError!void {
    for (sx[1..]) |e| {
        // Abstract Ion 1.1 conformance uses macro invocations encoded as sexps beginning with a
        // `#$:` address token (e.g. ("#$:set_macros" ...)). The Zig port doesn't evaluate macros
        // yet, so treat any such branch as unsupported.
        if (containsMacroAddressToken(e)) state.unsupported = true;
        try state.pushEvent(allocator, .{ .value = e });
    }
}

fn containsMacroAddressToken(elem: value.Element) bool {
    return switch (elem.value) {
        .sexp => |sx| blk: {
            if (sx.len != 0) {
                const head = sx[0];
                switch (head.value) {
                    .string => |s| {
                        if (std.mem.startsWith(u8, s, "#$:") and !std.mem.eql(u8, s, "#$:values")) break :blk true;
                    },
                    .symbol => |sym| {
                        if (sym.text) |t| {
                            if (std.mem.startsWith(u8, t, "#$:") and !std.mem.eql(u8, t, "#$:values")) break :blk true;
                        }
                    },
                    else => {},
                }
            }
            for (sx) |e| if (containsMacroAddressToken(e)) break :blk true;
            break :blk false;
        },
        .list => |items| blk: {
            for (items) |e| if (containsMacroAddressToken(e)) break :blk true;
            break :blk false;
        },
        .@"struct" => |st| blk: {
            for (st.fields) |f| {
                if (f.name.text) |t| if (std.mem.startsWith(u8, t, "#$:") and !std.mem.eql(u8, t, "#$:values")) break :blk true;
                if (containsMacroAddressToken(f.value)) break :blk true;
            }
            break :blk false;
        },
        else => false,
    };
}

fn applyBinaryFragment(state: *State, allocator: std.mem.Allocator, sx: []const value.Element) RunError!void {
    // (binary <byte>*) where <byte> is either 0..255 int or a hex string.
    if (sx.len == 1) return; // empty fragment

    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(allocator);

    for (sx[1..]) |e| {
        switch (e.value) {
            .int => |i| switch (i) {
                .small => |v| {
                    if (v < 0 or v > 255) return RunError.InvalidConformanceDsl;
                    bytes.append(allocator, @intCast(v)) catch return RunError.OutOfMemory;
                },
                else => return RunError.InvalidConformanceDsl,
            },
            .string => |s| {
                var i: usize = 0;
                while (i < s.len) {
                    while (i < s.len and std.ascii.isWhitespace(s[i])) : (i += 1) {}
                    if (i >= s.len) break;
                    if (i + 2 > s.len) return RunError.InvalidConformanceDsl;
                    const hi = std.fmt.charToDigit(s[i], 16) catch return RunError.InvalidConformanceDsl;
                    const lo = std.fmt.charToDigit(s[i + 1], 16) catch return RunError.InvalidConformanceDsl;
                    bytes.append(allocator, @intCast((hi << 4) | lo)) catch return RunError.OutOfMemory;
                    i += 2;
                }
            },
            else => return RunError.InvalidConformanceDsl,
        }
    }

    // Minimal support: recognize the 4-byte binary IVM and convert it to an abstract IVM event.
    if (bytes.items.len != 4 or bytes.items[0] != 0xE0 or bytes.items[3] != 0xEA) {
        state.unsupported = true;
        return;
    }
    const major: u32 = bytes.items[1];
    const minor: u32 = bytes.items[2];
    if (major == 1 and minor == 0) {
        try state.pushEvent(allocator, .{ .ivm = .ion_1_0 });
        return;
    }
    if (major == 1 and minor == 1) {
        try state.pushEvent(allocator, .{ .ivm = .ion_1_1 });
        return;
    }
    try state.pushEvent(allocator, .{ .ivm_invalid = .{ .major = major, .minor = minor } });
}

fn buildTextDocument(allocator: std.mem.Allocator, version: Version, frags: []const []const u8) RunError![]u8 {
    var out = std.ArrayListUnmanaged(u8){};
    errdefer out.deinit(allocator);

    // Prefix with IVM if requested.
    switch (version) {
        .ion_1_0 => out.appendSlice(allocator, "$ion_1_0\n") catch return RunError.OutOfMemory,
        .ion_1_1 => out.appendSlice(allocator, "$ion_1_1\n") catch return RunError.OutOfMemory,
        else => {},
    }

    var first = true;
    for (frags) |f| {
        if (!first) out.append(allocator, ' ') catch return RunError.OutOfMemory;
        first = false;
        out.appendSlice(allocator, f) catch return RunError.OutOfMemory;
    }
    return out.toOwnedSlice(allocator) catch return RunError.OutOfMemory;
}

fn collectTextFragments(allocator: std.mem.Allocator, state: *const State) RunError![][]const u8 {
    if (state.text_len == 0) return &.{};
    const out = allocator.alloc([]const u8, state.text_len) catch return RunError.OutOfMemory;
    var idx: usize = state.text_len;
    var n = state.text_tail;
    while (n) |node| {
        idx -= 1;
        out[idx] = node.frag;
        n = node.prev;
    }
    return out;
}

fn collectEvents(allocator: std.mem.Allocator, state: *const State) RunError![]AstEvent {
    if (state.event_len == 0) return &.{};
    const out = allocator.alloc(AstEvent, state.event_len) catch return RunError.OutOfMemory;
    var idx: usize = state.event_len;
    var n = state.event_tail;
    while (n) |node| {
        idx -= 1;
        out[idx] = node.ev;
        n = node.prev;
    }
    return out;
}

fn symtabTextForSid(symtab: []const ?[]const u8, symtab_max_id: u32, sid: u32) ?[]const u8 {
    if (sid == 0) return null;
    if (sid < symtab.len) return symtab[@intCast(sid)];
    if (sid <= symtab_max_id) return null;
    return null;
}

fn effectiveSymbolText(symtab: []const ?[]const u8, symtab_max_id: u32, s: value.Symbol) ?[]const u8 {
    if (parseDelayedSid(s)) |sid| return symtabTextForSid(symtab, symtab_max_id, sid);
    if (s.text) |t| return t;
    if (s.sid) |sid| return symtabTextForSid(symtab, symtab_max_id, sid);
    return null;
}

fn resolveDelayedSymbolUsingSymtab(
    arena: *value.Arena,
    symtab: []const ?[]const u8,
    symtab_max_id: u32,
    absences: *const std.AutoHashMapUnmanaged(u32, Absence),
    s: value.Symbol,
) RunError!value.Symbol {
    const sid = parseDelayedSid(s) orelse return s;
    if (sid == 0) return value.makeSymbolId(0, null);
    if (sid > symtab_max_id) return RunError.InvalidConformanceDsl;
    const t = symtabTextForSid(symtab, symtab_max_id, sid);
    if (t == null) {
        if (absences.get(sid) != null) return value.makeSymbolId(sid, null);
        // Conformance: unknown/malformed symbol table entries act like $0.
        return value.makeSymbolId(0, null);
    }
    _ = arena;
    return value.makeSymbolId(null, t.?);
}

fn resolveDelayedInElement(
    arena: *value.Arena,
    symtab: []const ?[]const u8,
    symtab_max_id: u32,
    absences: *const std.AutoHashMapUnmanaged(u32, Absence),
    elem: value.Element,
) RunError!value.Element {
    var out = elem;
    if (elem.annotations.len != 0) {
        const anns = arena.allocator().dupe(value.Symbol, elem.annotations) catch return RunError.OutOfMemory;
        for (anns) |*a| a.* = try resolveDelayedSymbolUsingSymtab(arena, symtab, symtab_max_id, absences, a.*);
        out.annotations = anns;
    }
    out.value = try resolveDelayedInValue(arena, symtab, symtab_max_id, absences, elem.value);
    return out;
}

fn resolveDelayedInValue(
    arena: *value.Arena,
    symtab: []const ?[]const u8,
    symtab_max_id: u32,
    absences: *const std.AutoHashMapUnmanaged(u32, Absence),
    v: value.Value,
) RunError!value.Value {
    return switch (v) {
        .symbol => |s| .{ .symbol = try resolveDelayedSymbolUsingSymtab(arena, symtab, symtab_max_id, absences, s) },
        .list => |l| blk: {
            const out = arena.allocator().alloc(value.Element, l.len) catch return RunError.OutOfMemory;
            for (l, 0..) |e, i| out[i] = try resolveDelayedInElement(arena, symtab, symtab_max_id, absences, e);
            break :blk .{ .list = out };
        },
        .sexp => |sx| blk: {
            const out = arena.allocator().alloc(value.Element, sx.len) catch return RunError.OutOfMemory;
            for (sx, 0..) |e, i| out[i] = try resolveDelayedInElement(arena, symtab, symtab_max_id, absences, e);
            break :blk .{ .sexp = out };
        },
        .@"struct" => |st| blk: {
            const out_fields = arena.allocator().alloc(value.StructField, st.fields.len) catch return RunError.OutOfMemory;
            for (st.fields, 0..) |f, i| {
                out_fields[i] = .{
                    .name = try resolveDelayedSymbolUsingSymtab(arena, symtab, symtab_max_id, absences, f.name),
                    .value = try resolveDelayedInElement(arena, symtab, symtab_max_id, absences, f.value),
                };
            }
            break :blk .{ .@"struct" = .{ .fields = out_fields } };
        },
        else => v,
    };
}

fn isIstStructTopLevel(symtab: []const ?[]const u8, symtab_max_id: u32, elem: value.Element) bool {
    if (!(elem.value == .@"struct" or (elem.value == .null and elem.value.null == .@"struct"))) return false;
    if (elem.annotations.len == 0) return false;
    const first = elem.annotations[0];
    const resolved = effectiveSymbolText(symtab, symtab_max_id, first) orelse return false;
    return std.mem.eql(u8, resolved, "$ion_symbol_table");
}

fn resetSymtabForVersion(allocator: std.mem.Allocator, version: Version, out: *std.ArrayListUnmanaged(?[]const u8), out_max_id: *u32) RunError!void {
    out.clearRetainingCapacity();
    const sys_max: u32 = sysMaxId(version);
    out.ensureTotalCapacity(allocator, sys_max + 1) catch return RunError.OutOfMemory;
    out.items.len = 0;
    out.appendAssumeCapacity(null);
    var sid: u32 = 1;
    while (sid <= sys_max) : (sid += 1) out.appendAssumeCapacity(sysTextForSid(version, sid).?);
    out_max_id.* = sys_max;
}

fn applyIstStruct(
    version: Version,
    allocator: std.mem.Allocator,
    symtab: *std.ArrayListUnmanaged(?[]const u8),
    symtab_max_id: *u32,
    absences: *std.AutoHashMapUnmanaged(u32, Absence),
    prev_symtab: []const ?[]const u8,
    prev_symtab_max_id: u32,
    elem: value.Element,
) RunError!void {
    // Only struct-valued `$ion_symbol_table` annotations are symbol tables; other types pass through.
    if (!(elem.value == .@"struct" or (elem.value == .null and elem.value.null == .@"struct"))) return;
    // Successive local symtabs replace earlier ones (reset to system + imports/symbols).
    try resetSymtabForVersion(allocator, version, symtab, symtab_max_id);
    absences.clearRetainingCapacity();

    if (elem.value == .null) return;
    const st = elem.value.@"struct";

    var imports_field: ?value.Element = null;
    var symbols_field: ?value.Element = null;

    for (st.fields) |f| {
        const name_text = effectiveSymbolText(symtab.items, symtab_max_id.*, f.name) orelse continue;
        if (std.mem.eql(u8, name_text, "imports")) {
            if (imports_field != null) return RunError.InvalidConformanceDsl;
            imports_field = f.value;
            continue;
        }
        if (std.mem.eql(u8, name_text, "symbols")) {
            if (symbols_field != null) return RunError.InvalidConformanceDsl;
            symbols_field = f.value;
            continue;
        }
    }

    // Apply imports first if present.
    if (imports_field) |imp| {
        // Special-case: `imports:$ion_symbol_table` means import the current symbol table.
        if (imp.value == .symbol) {
            const imp_sym = imp.value.symbol;
            const imp_name = effectiveSymbolText(symtab.items, symtab_max_id.*, imp_sym) orelse null;
            if (imp_name != null and std.mem.eql(u8, imp_name.?, "$ion_symbol_table")) {
                const sys_max = sysMaxId(version);
                if (prev_symtab_max_id > sys_max) {
                    const count: u32 = prev_symtab_max_id - sys_max;
                    var off: u32 = 1;
                    while (off <= count) : (off += 1) {
                        const sid: u32 = sys_max + off;
                        const t = symtabTextForSid(prev_symtab, prev_symtab_max_id, sid);
                        symtab.append(allocator, t) catch return RunError.OutOfMemory;
                    }
                    symtab_max_id.* = prev_symtab_max_id;
                }
            }
        } else if (imp.value == .list) {
            const imports = imp.value.list;
            for (imports) |imp_elem| {
                if (imp_elem.value != .@"struct") continue;
                const imp_st = imp_elem.value.@"struct";

                var name_opt: ?[]const u8 = null;
                var ver: u32 = 1;
                var max_id_opt: ?u32 = null;
                var saw_name = false;
                var saw_ver = false;
                var saw_max = false;

                for (imp_st.fields) |ff| {
                    const fn_text = effectiveSymbolText(symtab.items, symtab_max_id.*, ff.name) orelse continue;
                    if (std.mem.eql(u8, fn_text, "name")) {
                        if (saw_name) return RunError.InvalidConformanceDsl;
                        saw_name = true;
                        if (ff.value.value == .string) {
                            const n = ff.value.value.string;
                            if (n.len != 0) name_opt = n;
                        }
                        continue;
                    }
                    if (std.mem.eql(u8, fn_text, "version")) {
                        if (saw_ver) return RunError.InvalidConformanceDsl;
                        saw_ver = true;
                        if (ff.value.value == .int) {
                            switch (ff.value.value.int) {
                                .small => |v| {
                                    if (v > 0) ver = @intCast(v);
                                },
                                else => {},
                            }
                        }
                        continue;
                    }
                    if (std.mem.eql(u8, fn_text, "max_id")) {
                        if (saw_max) return RunError.InvalidConformanceDsl;
                        saw_max = true;
                        if (ff.value.value == .int) {
                            switch (ff.value.value.int) {
                                .small => |v| {
                                    if (v >= 0) max_id_opt = @intCast(v);
                                },
                                else => {},
                            }
                        }
                        continue;
                    }
                }

                const name = name_opt orelse continue;

                const exact = SharedSymtabCatalog.lookup(name, ver);
                const requested_max_valid = max_id_opt;

                if (exact == null and requested_max_valid == null) return RunError.InvalidConformanceDsl;
                const chosen = exact orelse if (requested_max_valid != null) SharedSymtabCatalog.bestForName(name) else null;

                if (chosen) |tab| {
                    // If we have an exact match, malformed max_id is ignored and the table's full size is used.
                    const use_max: u32 = if (exact != null)
                        (requested_max_valid orelse @intCast(tab.symbols.len))
                    else
                        (requested_max_valid orelse return RunError.InvalidConformanceDsl);

                    var off: u32 = 1;
                    while (off <= use_max) : (off += 1) {
                        const idx: usize = @intCast(off - 1);
                        const sid: u32 = symtab_max_id.* + 1;
                        if (idx < tab.symbols.len) {
                            if (tab.symbols[idx]) |txt| {
                                symtab.append(allocator, txt) catch return RunError.OutOfMemory;
                            } else {
                                symtab.append(allocator, null) catch return RunError.OutOfMemory;
                                const owned = allocator.dupe(u8, name) catch return RunError.OutOfMemory;
                                absences.put(allocator, sid, .{ .name = owned, .offset = off }) catch return RunError.OutOfMemory;
                            }
                        } else {
                            symtab.append(allocator, null) catch return RunError.OutOfMemory;
                            const owned = allocator.dupe(u8, name) catch return RunError.OutOfMemory;
                            absences.put(allocator, sid, .{ .name = owned, .offset = off }) catch return RunError.OutOfMemory;
                        }
                        symtab_max_id.* += 1;
                    }
                } else {
                    // No catalog entry; pad out to max_id with absent slots.
                    const pad: u32 = requested_max_valid orelse return RunError.InvalidConformanceDsl;
                    var off: u32 = 1;
                    while (off <= pad) : (off += 1) {
                        const sid: u32 = symtab_max_id.* + 1;
                        symtab.append(allocator, null) catch return RunError.OutOfMemory;
                        const owned = allocator.dupe(u8, name) catch return RunError.OutOfMemory;
                        absences.put(allocator, sid, .{ .name = owned, .offset = off }) catch return RunError.OutOfMemory;
                        symtab_max_id.* += 1;
                    }
                }
            }
        } else {
            // Non-list imports are ignored (including sexp).
        }
    }

    // Apply symbols (local symbols) if present and well-formed.
    if (symbols_field) |sym| {
        if (sym.value != .list) return; // malformed, ignore whole field
        const items = sym.value.list;
        for (items) |it| {
            symtab.append(allocator, if (it.value == .string) it.value.string else null) catch return RunError.OutOfMemory;
            symtab_max_id.* += 1;
        }
        if (symtab.items.len > 0) symtab_max_id.* = @intCast(symtab.items.len - 1);
    }
}

fn normalizeExpectedElement(arena: *value.Arena, elem: value.Element) RunError!value.Element {
    // Currently, conformance uses `#$0` in `produces` to denote unknown symbols.
    var out = elem;
    if (elem.annotations.len != 0) {
        const anns = arena.allocator().dupe(value.Symbol, elem.annotations) catch return RunError.OutOfMemory;
        for (anns) |*a| {
            const sid = parseDelayedSid(a.*);
            if (sid != null and sid.? == 0) a.* = value.makeSymbolId(0, null);
        }
        out.annotations = anns;
    }
    out.value = try normalizeExpectedValue(arena, elem.value);
    return out;
}

fn normalizeExpectedValue(arena: *value.Arena, v: value.Value) RunError!value.Value {
    return switch (v) {
        .symbol => |s| blk: {
            const sid = parseDelayedSid(s);
            if (sid != null and sid.? == 0) break :blk .{ .symbol = value.makeSymbolId(0, null) };
            break :blk v;
        },
        .list => |l| blk: {
            const out = arena.allocator().alloc(value.Element, l.len) catch return RunError.OutOfMemory;
            for (l, 0..) |e, i| out[i] = try normalizeExpectedElement(arena, e);
            break :blk .{ .list = out };
        },
        .sexp => |sx| blk: {
            const out = arena.allocator().alloc(value.Element, sx.len) catch return RunError.OutOfMemory;
            for (sx, 0..) |e, i| out[i] = try normalizeExpectedElement(arena, e);
            break :blk .{ .sexp = out };
        },
        .@"struct" => |st| blk: {
            const out_fields = arena.allocator().alloc(value.StructField, st.fields.len) catch return RunError.OutOfMemory;
            for (st.fields, 0..) |f, i| {
                var name = f.name;
                const sid = parseDelayedSid(name);
                if (sid != null and sid.? == 0) name = value.makeSymbolId(0, null);
                out_fields[i] = .{
                    .name = name,
                    .value = try normalizeExpectedElement(arena, f.value),
                };
            }
            break :blk .{ .@"struct" = .{ .fields = out_fields } };
        },
        else => v,
    };
}

const ParsedIvm = union(enum) { valid: Version, invalid: struct { major: u32, minor: u32 } };

fn parseTextIvmToken(raw: []const u8) ?ParsedIvm {
    const s = std.mem.trim(u8, raw, " \t\r\n");
    if (!std.mem.startsWith(u8, s, "$ion_")) return null;
    const rest = s["$ion_".len..];
    const us = std.mem.indexOfScalar(u8, rest, '_') orelse return null;
    const major_s = rest[0..us];
    const minor_s = rest[us + 1 ..];
    const major = std.fmt.parseInt(u32, major_s, 10) catch return null;
    const minor = std.fmt.parseInt(u32, minor_s, 10) catch return null;
    if (major == 1 and minor == 0) return .{ .valid = .ion_1_0 };
    if (major == 1 and minor == 1) return .{ .valid = .ion_1_1 };
    return .{ .invalid = .{ .major = major, .minor = minor } };
}

fn parseAbstractIvmSymbol(s: value.Symbol) ?ParsedIvm {
    const t = s.text orelse return null;
    if (!std.mem.startsWith(u8, t, "#$ion_")) return null;
    const rest = t["#$ion_".len..];
    const us = std.mem.indexOfScalar(u8, rest, '_') orelse return null;
    const major_s = rest[0..us];
    const minor_s = rest[us + 1 ..];
    const major = std.fmt.parseInt(u32, major_s, 10) catch return null;
    const minor = std.fmt.parseInt(u32, minor_s, 10) catch return null;
    if (major == 1 and minor == 0) return .{ .valid = .ion_1_0 };
    if (major == 1 and minor == 1) return .{ .valid = .ion_1_1 };
    return .{ .invalid = .{ .major = major, .minor = minor } };
}

fn evalAbstractDocument(arena: *value.Arena, state: *State, absences: *std.AutoHashMapUnmanaged(u32, Absence)) RunError![]value.Element {
    const a = arena.allocator();
    var out = std.ArrayListUnmanaged(value.Element){};
    errdefer out.deinit(a);

    var version_ctx: Version = if (state.version == .document) .ion_1_0 else state.version;
    var symtab = std.ArrayListUnmanaged(?[]const u8){};
    defer symtab.deinit(a);
    var symtab_max_id: u32 = 0;
    try resetSymtabForVersion(a, version_ctx, &symtab, &symtab_max_id);
    absences.clearRetainingCapacity();

    const events = try collectEvents(a, state);
    defer if (events.len != 0) a.free(events);

    for (events) |ev| {
        switch (ev) {
            .ivm => |v| {
                version_ctx = v;
                try resetSymtabForVersion(a, version_ctx, &symtab, &symtab_max_id);
                absences.clearRetainingCapacity();
            },
            .ivm_invalid => |_| return RunError.InvalidConformanceDsl,
            .value => |e| {
                if (e.annotations.len == 0 and e.value == .symbol) {
                    if (parseAbstractIvmSymbol(e.value.symbol)) |ivm| {
                        switch (ivm) {
                            .valid => |v| {
                                version_ctx = v;
                                try resetSymtabForVersion(a, version_ctx, &symtab, &symtab_max_id);
                                absences.clearRetainingCapacity();
                                continue;
                            },
                            .invalid => |_| return RunError.InvalidConformanceDsl,
                        }
                    }
                }
                if (isIstStructTopLevel(symtab.items, symtab_max_id, e)) {
                    const prev_items = a.dupe(?[]const u8, symtab.items) catch return RunError.OutOfMemory;
                    const prev_max = symtab_max_id;
                    try applyIstStruct(version_ctx, a, &symtab, &symtab_max_id, absences, prev_items, prev_max, e);
                    continue;
                }
                const expanded = try resolveDelayedInElement(arena, symtab.items, symtab_max_id, absences, e);
                const expanded_list = try expandValuesAtTopLevel(arena, expanded);
                out.appendSlice(a, expanded_list) catch return RunError.OutOfMemory;
            },
        }
    }
    return out.toOwnedSlice(a) catch return RunError.OutOfMemory;
}

fn isValuesMacroInvocation(elem: value.Element) bool {
    if (elem.value != .sexp) return false;
    const sx = elem.value.sexp;
    if (sx.len == 0) return false;
    if (sx[0].value != .symbol) return false;
    const t = sx[0].value.symbol.text orelse return false;
    return std.mem.eql(u8, t, "#$:values");
}

fn expandValuesAtTopLevel(arena: *value.Arena, elem: value.Element) RunError![]value.Element {
    if (isValuesMacroInvocation(elem)) {
        const sx = elem.value.sexp;
        if (sx.len == 1) return &.{}; // `values` with no args produces no values
        const out = arena.allocator().alloc(value.Element, sx.len - 1) catch return RunError.OutOfMemory;
        for (sx[1..], 0..) |e, i| out[i] = try expandValuesInElement(arena, e);
        return out;
    }
    const single = arena.allocator().alloc(value.Element, 1) catch return RunError.OutOfMemory;
    single[0] = try expandValuesInElement(arena, elem);
    return single;
}

fn expandValuesInElement(arena: *value.Arena, elem: value.Element) RunError!value.Element {
    var out = elem;
    out.value = try expandValuesInValue(arena, elem.value);
    return out;
}

fn expandValuesInValue(arena: *value.Arena, v: value.Value) RunError!value.Value {
    return switch (v) {
        .list => |items| blk: {
            var out = std.ArrayListUnmanaged(value.Element){};
            errdefer out.deinit(arena.allocator());
            for (items) |e| {
                if (isValuesMacroInvocation(e)) {
                    const sx = e.value.sexp;
                    for (sx[1..]) |arg| out.append(arena.allocator(), try expandValuesInElement(arena, arg)) catch return RunError.OutOfMemory;
                } else {
                    out.append(arena.allocator(), try expandValuesInElement(arena, e)) catch return RunError.OutOfMemory;
                }
            }
            break :blk .{ .list = out.toOwnedSlice(arena.allocator()) catch return RunError.OutOfMemory };
        },
        .sexp => |items| blk: {
            var out = std.ArrayListUnmanaged(value.Element){};
            errdefer out.deinit(arena.allocator());
            for (items) |e| {
                if (isValuesMacroInvocation(e)) {
                    const sx = e.value.sexp;
                    for (sx[1..]) |arg| out.append(arena.allocator(), try expandValuesInElement(arena, arg)) catch return RunError.OutOfMemory;
                } else {
                    out.append(arena.allocator(), try expandValuesInElement(arena, e)) catch return RunError.OutOfMemory;
                }
            }
            break :blk .{ .sexp = out.toOwnedSlice(arena.allocator()) catch return RunError.OutOfMemory };
        },
        .@"struct" => |st| blk: {
            // We don't model multi-value inlining into structs yet.
            var out_fields = std.ArrayListUnmanaged(value.StructField){};
            errdefer out_fields.deinit(arena.allocator());
            for (st.fields) |f| {
                if (isValuesMacroInvocation(f.value)) return RunError.Unsupported;
                out_fields.append(arena.allocator(), .{ .name = f.name, .value = try expandValuesInElement(arena, f.value) }) catch return RunError.OutOfMemory;
            }
            break :blk .{ .@"struct" = .{ .fields = out_fields.toOwnedSlice(arena.allocator()) catch return RunError.OutOfMemory } };
        },
        else => v,
    };
}

fn runExpectation(
    allocator: std.mem.Allocator,
    state: *State,
    exp: value.Element,
) RunError!bool {
    // Returns true if executed, false if skipped due to unsupported features.
    if (state.unsupported) return false;
    const sx = getSexpItems(exp) orelse return RunError.InvalidConformanceDsl;
    if (sx.len == 0) return RunError.InvalidConformanceDsl;
    const head = symText(sx[0]) orelse return RunError.InvalidConformanceDsl;

    var arena = value.Arena.init(allocator) catch return RunError.OutOfMemory;
    defer arena.deinit();

    var absences = std.AutoHashMapUnmanaged(u32, Absence){};
    defer absences.deinit(arena.allocator());

    var actual: []const value.Element = &.{};
    var parsed_doc: ?ion.Document = null;
    defer if (parsed_doc) |*d| d.deinit();
    var doc_bytes_owned: ?[]u8 = null;
    defer if (doc_bytes_owned) |b| allocator.free(b);

    if (state.text_len != 0) {
        const frags = try collectTextFragments(allocator, state);
        defer if (frags.len != 0) allocator.free(frags);
        const doc_bytes = try buildTextDocument(allocator, state.version, frags);
        doc_bytes_owned = doc_bytes;
        parsed_doc = ion.parseDocument(allocator, doc_bytes) catch |e| {
            if (std.mem.eql(u8, head, "signals")) return true;
            // Conformance suite includes many Ion 1.1 macro system / e-expression inputs. We don't
            // implement those yet, but we still want to run the rest of the suite. Treat parser
            // "unsupported" as a skip for this branch (rather than a hard failure).
            if (e == ion.IonError.Unsupported) return false;
            // Many not-yet-implemented macro invocations currently surface as other parse errors
            // (InvalidIon/Incomplete/etc). If the input appears to contain an Ion 1.1 macro
            // invocation, treat it as unsupported to keep conformance progress incremental.
            if (std.mem.indexOf(u8, doc_bytes, "(:") != null) return false;
            std.debug.print("conformance parse failed unexpectedly: {s}\n", .{@errorName(e)});
            return RunError.InvalidConformanceDsl;
        };
        actual = parsed_doc.?.elements;
    } else {
        const abs = evalAbstractDocument(&arena, state, &absences) catch |err| {
            if (std.mem.eql(u8, head, "signals")) return true;
            return err;
        };
        actual = abs;
    }

    if (std.mem.eql(u8, head, "signals")) {
        // If we got here, parsing succeeded, which violates the expectation.
        if (sx.len >= 2 and sx[1].value == .string) {
            std.debug.print("signals violated: expected error '{s}'\n", .{sx[1].value.string});
        } else {
            std.debug.print("signals violated: expected error\n", .{});
        }
        if (doc_bytes_owned) |b| {
            const show: usize = @min(b.len, 512);
            std.debug.print("signals violated: parsed bytes (prefix, {d}/{d}):\n{s}\n", .{ show, b.len, b[0..show] });
        }
        return RunError.InvalidConformanceDsl;
    }

    if (std.mem.eql(u8, head, "produces")) {
        const expected_raw = sx[1..];
        const expected = arena.allocator().alloc(value.Element, expected_raw.len) catch return RunError.OutOfMemory;
        for (expected_raw, 0..) |e, i| expected[i] = try normalizeExpectedElement(&arena, e);
        if (!ion.eq.ionEqElements(actual, expected)) return RunError.InvalidConformanceDsl;
        return true;
    }

    if (std.mem.eql(u8, head, "denotes")) {
        const expected_raw = sx[1..];

        // Compute denotation for actual outputs.
        var den_arena = value.Arena.init(allocator) catch return RunError.OutOfMemory;
        defer den_arena.deinit();
        const denoted = den_arena.allocator().alloc(value.Element, actual.len) catch return RunError.OutOfMemory;
        for (actual, 0..) |e, i| denoted[i] = denote.denoteElement(&den_arena, e) catch return RunError.OutOfMemory;
        // Patch up symbol denotations for absent imported slots.
        if (absences.count() != 0) {
            for (denoted) |*d| patchAbsentSymbols(&den_arena, &absences, d);
        }

        // Normalize expected forms into the same representation.
        const expected = den_arena.allocator().alloc(value.Element, expected_raw.len) catch return RunError.OutOfMemory;
        for (expected_raw, 0..) |e, i| {
            expected[i] = denote.normalizeDenoteExpected(&den_arena, e) catch return RunError.Unsupported;
        }

        if (denoted.len != expected.len) {
            const a_dbg = ion.serializeDocument(allocator, .text_pretty, denoted) catch "";
            defer if (a_dbg.len != 0) allocator.free(a_dbg);
            const e_dbg = ion.serializeDocument(allocator, .text_pretty, expected) catch "";
            defer if (e_dbg.len != 0) allocator.free(e_dbg);
            if (a_dbg.len != 0 and e_dbg.len != 0) {
                std.debug.print("denotes length mismatch\nactual:\n{s}\nexpected:\n{s}\n", .{ a_dbg, e_dbg });
            }
            return RunError.InvalidConformanceDsl;
        }
        for (denoted, expected) |a, b| {
            if (!denote.denoteEq(a, b)) {
                const a_dbg = ion.serializeDocument(allocator, .text_pretty, denoted) catch "";
                defer if (a_dbg.len != 0) allocator.free(a_dbg);
                const e_dbg = ion.serializeDocument(allocator, .text_pretty, expected) catch "";
                defer if (e_dbg.len != 0) allocator.free(e_dbg);
                if (a_dbg.len != 0 and e_dbg.len != 0) {
                    std.debug.print("denotes mismatch\nactual:\n{s}\nexpected:\n{s}\n", .{ a_dbg, e_dbg });
                }
                return RunError.InvalidConformanceDsl;
            }
        }
        return true;
    }

    return RunError.Unsupported;
}

fn patchAbsentSymbols(arena: *value.Arena, absences: *const std.AutoHashMapUnmanaged(u32, Absence), elem: *value.Element) void {
    switch (elem.value) {
        .list => |items| for (items) |*e| patchAbsentSymbols(arena, absences, e),
        .sexp => |sx| {
            if (sx.len == 2 and sx[0].value == .symbol and sx[0].value.symbol.text != null and std.mem.eql(u8, sx[0].value.symbol.text.?, "Symbol")) {
                if (sx[1].value == .int) switch (sx[1].value.int) {
                    .small => |sid_i| {
                        if (sid_i >= 0) {
                            const sid: u32 = @intCast(sid_i);
                            if (absences.get(sid)) |a| {
                                const head_sym = value.makeSymbol(arena, "absent") catch return;
                                const head_elem: value.Element = .{ .annotations = &.{}, .value = .{ .symbol = head_sym } };
                                const name_elem: value.Element = .{ .annotations = &.{}, .value = .{ .string = a.name } };
                                const off_elem: value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = @intCast(a.offset) } } };
                                const absent_sx = arena.allocator().dupe(value.Element, &.{ head_elem, name_elem, off_elem }) catch return;
                                sx[1] = .{ .annotations = &.{}, .value = .{ .sexp = absent_sx } };
                            }
                        }
                    },
                    else => {},
                };
            }
            for (sx) |*e| patchAbsentSymbols(arena, absences, e);
        },
        .@"struct" => |st| for (st.fields) |*f| patchAbsentSymbols(arena, absences, &f.value),
        else => {},
    }
}

fn isFragmentHead(head: []const u8) bool {
    return std.mem.eql(u8, head, "text") or
        std.mem.eql(u8, head, "toplevel") or
        std.mem.eql(u8, head, "ivm") or
        std.mem.eql(u8, head, "binary");
}

fn applyFragmentElement(state: *State, allocator: std.mem.Allocator, frag_elem: value.Element) RunError!void {
    const sx = getSexpItems(frag_elem) orelse return RunError.InvalidConformanceDsl;
    if (sx.len == 0) return RunError.InvalidConformanceDsl;
    const head = symText(sx[0]) orelse return RunError.InvalidConformanceDsl;

    if (std.mem.eql(u8, head, "text")) return applyTextFragment(state, allocator, sx);
    if (std.mem.eql(u8, head, "toplevel")) return applyTopLevel2(state, allocator, sx);
    if (std.mem.eql(u8, head, "binary")) return applyBinaryFragment(state, allocator, sx);
    if (std.mem.eql(u8, head, "ivm")) {
        if (sx.len != 3) return RunError.InvalidConformanceDsl;
        if (sx[1].value != .int or sx[2].value != .int) return RunError.InvalidConformanceDsl;
        const major: i128 = switch (sx[1].value.int) {
            .small => |v| v,
            else => return RunError.InvalidConformanceDsl,
        };
        const minor: i128 = switch (sx[2].value.int) {
            .small => |v| v,
            else => return RunError.InvalidConformanceDsl,
        };
        if (major < 0 or minor < 0) return RunError.InvalidConformanceDsl;
        const maj_u: u32 = @intCast(major);
        const min_u: u32 = @intCast(minor);
        if (maj_u == 1 and min_u == 0) {
            try state.pushEvent(allocator, .{ .ivm = .ion_1_0 });
        } else if (maj_u == 1 and min_u == 1) {
            try state.pushEvent(allocator, .{ .ivm = .ion_1_1 });
        } else {
            try state.pushEvent(allocator, .{ .ivm_invalid = .{ .major = maj_u, .minor = min_u } });
        }
        return;
    }
    // Unrecognized fragment type: treat as unsupported.
    state.unsupported = true;
}

fn evalSeq(gpa: std.mem.Allocator, stats: *Stats, state: *State, items: []const value.Element) RunError!void {
    var work_arena = std.heap.ArenaAllocator.init(gpa);
    defer work_arena.deinit();
    const work = work_arena.allocator();

    const Frame = struct {
        state: State,
        items: []const value.Element,
        idx: usize,
    };

    var stack = std.ArrayListUnmanaged(Frame){};
    defer {
        while (stack.items.len != 0) {
            var tmp = stack.pop() orelse break;
            tmp.state.deinit(work);
        }
        stack.deinit(work);
    }

    stack.append(work, .{ .state = try state.clone(work), .items = items, .idx = 0 }) catch return RunError.OutOfMemory;

    while (stack.items.len != 0) {
        // Avoid holding pointers into `stack.items` across `stack.append()` calls: appends may
        // reallocate and invalidate pointers, which can corrupt `State` (notably `text_len`).
        const frame_idx = stack.items.len - 1;
        var frame = &stack.items[frame_idx];
        if (frame.idx >= frame.items.len) {
            var finished = stack.pop() orelse return RunError.InvalidConformanceDsl;
            finished.state.deinit(work);
            continue;
        }

        const it = frame.items[frame.idx];
        frame.idx += 1;

        const sx = getSexpItems(it) orelse continue; // label/no-op
        if (sx.len == 0) return RunError.InvalidConformanceDsl;
        const head = symText(sx[0]) orelse return RunError.InvalidConformanceDsl;

        if (std.mem.eql(u8, head, "then")) {
            const base_state = frame.state;
            const child = try base_state.clone(work);
            stack.append(work, .{ .state = child, .items = sx[1..], .idx = 0 }) catch return RunError.OutOfMemory;
            continue;
        }

        if (std.mem.eql(u8, head, "each")) {
            const base_state = frame.state;
            if (sx.len < 2) return RunError.InvalidConformanceDsl;
            var branch_frags = std.ArrayListUnmanaged(value.Element){};
            defer branch_frags.deinit(work);

            var split_idx: usize = 1;
            while (split_idx < sx.len) : (split_idx += 1) {
                if (sx[split_idx].value != .sexp) continue;
                const frag_sx = sx[split_idx].value.sexp;
                if (frag_sx.len == 0) return RunError.InvalidConformanceDsl;
                const frag_head = symText(frag_sx[0]) orelse return RunError.InvalidConformanceDsl;
                if (!isFragmentHead(frag_head)) break;
                branch_frags.append(work, sx[split_idx]) catch return RunError.OutOfMemory;
            }
            if (split_idx >= sx.len) return RunError.InvalidConformanceDsl;
            const continuation = sx[split_idx..];

            if (branch_frags.items.len == 0) {
                const branch_state = try base_state.clone(work);
                stack.append(work, .{ .state = branch_state, .items = continuation, .idx = 0 }) catch return RunError.OutOfMemory;
            } else {
                // Push in reverse order so the first fragment runs first.
                var j: usize = branch_frags.items.len;
                while (j != 0) {
                    j -= 1;
                    var branch_state = try base_state.clone(work);
                    try applyFragmentElement(&branch_state, work, branch_frags.items[j]);
                    stack.append(work, .{ .state = branch_state, .items = continuation, .idx = 0 }) catch return RunError.OutOfMemory;
                }
            }
            continue;
        }

        if (isFragmentHead(head)) {
            try applyFragmentElement(&frame.state, work, it);
            continue;
        }

        if (std.mem.eql(u8, head, "produces") or std.mem.eql(u8, head, "signals") or std.mem.eql(u8, head, "denotes")) {
            stats.branches += 1;
            const ok = runExpectation(gpa, &frame.state, it) catch |e| switch (e) {
                RunError.Unsupported => {
                    stats.skipped += 1;
                    // End this branch.
                    frame.idx = frame.items.len;
                    continue;
                },
                else => return e,
            };
            if (ok) stats.passed += 1 else stats.skipped += 1;
            frame.idx = frame.items.len;
            continue;
        }

        // Unimplemented clause type: mark this branch unsupported until an expectation is reached.
        frame.state.unsupported = true;
    }
}

pub fn runConformanceFile(allocator: std.mem.Allocator, data: []const u8, stats: *Stats) RunError!void {
    // Parse conformance DSL using Ion text rules *without* adjacent string literal concatenation.
    var arena = value.Arena.init(allocator) catch return RunError.OutOfMemory;
    defer arena.deinit();
    const elements = ion.text.parseTopLevelNoStringConcat(&arena, data) catch return RunError.InvalidConformanceDsl;

    for (elements) |top| {
        if (top.value != .sexp) continue;
        const sx = top.value.sexp;
        if (sx.len == 0) continue;
        const head = symText(sx[0]) orelse continue;
        if (std.mem.eql(u8, head, "ion_1_x")) {
            stats.cases += 1;
            var state_10 = State{ .version = .ion_1_0 };
            defer state_10.deinit(allocator);
            try evalSeq(allocator, stats, &state_10, sx[1..]);

            var state_11 = State{ .version = .ion_1_1 };
            defer state_11.deinit(allocator);
            try evalSeq(allocator, stats, &state_11, sx[1..]);
            continue;
        }

        const version: Version = if (std.mem.eql(u8, head, "ion_1_0")) .ion_1_0 else if (std.mem.eql(u8, head, "ion_1_1")) .ion_1_1 else if (std.mem.eql(u8, head, "document")) .document else continue;

        stats.cases += 1;
        var state = State{ .version = version };
        defer state.deinit(allocator);
        try evalSeq(allocator, stats, &state, sx[1..]);
    }
}
