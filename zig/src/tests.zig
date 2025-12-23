//! Zig test harness for the Ion Zig port.
//!
//! Walks `ion-tests/iontestdata` and `ion-tests/iontestdata_1_1` and enforces:
//! - `bad/` files must be rejected
//! - `good/equivs/` groups must be equivalent
//! - `good/non-equivs/` groups must not be equivalent across members
//! - `good/` roundtrips across a format matrix
//!
//! Some fixtures are intentionally skipped; each skip has an inline comment explaining why.

const std = @import("std");
const ion = @import("ion.zig");
const conformance = @import("conformance/runner.zig");

fn isSkipped(path: []const u8, skip_list: []const []const u8) bool {
    for (skip_list) |skip| {
        if (std.mem.eql(u8, path, skip)) return true;
    }
    return false;
}

fn hasAnySuffix(path: []const u8, suffixes: []const []const u8) bool {
    for (suffixes) |suffix| {
        if (std.mem.endsWith(u8, path, suffix)) return true;
    }
    return false;
}

fn walkAndTest(
    allocator: std.mem.Allocator,
    base_path: []const u8,
    file_suffixes: []const []const u8,
    skip_list: []const []const u8,
    test_fn: fn ([]const u8, []const u8) anyerror!void,
) !void {
    // Some commands (e.g. `zig test src/tests.zig`) run with CWD set to `zig/`, while the normal
    // `zig build test` runs from the repo root. Try both so the tests are runnable either way.
    var alt_base_path: ?[]const u8 = null;
    defer if (alt_base_path) |p| allocator.free(p);

    var dir = std.fs.cwd().openDir(base_path, .{ .iterate = true }) catch |e| switch (e) {
        error.FileNotFound => blk: {
            const alt = try std.fs.path.join(allocator, &.{ "..", base_path });
            alt_base_path = alt;
            break :blk try std.fs.cwd().openDir(alt, .{ .iterate = true });
        },
        else => return e,
    };
    defer dir.close();

    var walker = try dir.walk(allocator);
    defer walker.deinit();

    while (try walker.next()) |entry| {
        if (entry.kind != .file) continue;
        if (!hasAnySuffix(entry.path, file_suffixes)) continue;

        const full_path = try std.fs.path.join(allocator, &.{ base_path, entry.path });
        defer allocator.free(full_path);

        // `walk()` yields paths relative to `base_path`; turn them into repo-relative paths for
        // skip list matching.
        const repo_rel = full_path;
        if (isSkipped(repo_rel, skip_list)) continue;

        const data = try dir.readFileAlloc(allocator, entry.path, 64 * 1024 * 1024);
        defer allocator.free(data);

        try test_fn(repo_rel, data);
    }
}

const global_skip_list = [_][]const u8{
};

const round_trip_skip_list = [_][]const u8{
};

const equivs_skip_list = [_][]const u8{
};

fn concatSkipLists(allocator: std.mem.Allocator, lists: []const []const []const u8) ![][]const u8 {
    var total: usize = 0;
    for (lists) |list| total += list.len;

    var out = try allocator.alloc([]const u8, total);
    var i: usize = 0;
    for (lists) |list| {
        for (list) |item| {
            out[i] = item;
            i += 1;
        }
    }
    return out;
}

test "ion-tests bad files reject" {
    const allocator = std.testing.allocator;

    try walkAndTest(
        allocator,
        "ion-tests/iontestdata/bad",
        &.{ ".ion", ".10n" },
        &global_skip_list,
        struct {
            fn run(path: []const u8, data: []const u8) !void {
                const parsed = ion.parseDocument(std.testing.allocator, data);
                if (parsed) |doc| {
                    var d = doc;
                    d.deinit();
                    std.debug.print("unexpectedly parsed bad file: {s}\n", .{path});
                    return error.UnexpectedSuccess;
                } else |_| {}
            }
        }.run,
    );
}

test "ion-tests 1_1 bad files reject" {
    const allocator = std.testing.allocator;

    try walkAndTest(
        allocator,
        "ion-tests/iontestdata_1_1/bad",
        &.{ ".ion" },
        &global_skip_list,
        struct {
            fn run(path: []const u8, data: []const u8) !void {
                const parsed = ion.parseDocument(std.testing.allocator, data);
                if (parsed) |doc| {
                    var d = doc;
                    d.deinit();
                    std.debug.print("unexpectedly parsed bad file: {s}\n", .{path});
                    return error.UnexpectedSuccess;
                } else |_| {}
            }
        }.run,
    );
}

test "zig ion parses simple text" {
    var doc = try ion.parseDocument(std.testing.allocator, "1");
    defer doc.deinit();
    try std.testing.expect(doc.elements.len == 1);
}

test "ion-tests equiv groups" {
    const allocator = std.testing.allocator;
    const skip = try concatSkipLists(allocator, &.{ &global_skip_list, &equivs_skip_list });
    defer allocator.free(skip);

    try walkAndTest(
        allocator,
        "ion-tests/iontestdata/good/equivs",
        &.{ ".ion", ".10n" },
        skip,
        struct {
            fn run(path: []const u8, data: []const u8) !void {
                checkGroup(data, true) catch |e| {
                    std.debug.print("equivs failed: {s}: {s}\n", .{ path, @errorName(e) });
                    return e;
                };
            }
        }.run,
    );
}

test "ion-tests 1_1 equiv groups" {
    const allocator = std.testing.allocator;
    const skip = try concatSkipLists(allocator, &.{ &global_skip_list, &equivs_skip_list });
    defer allocator.free(skip);

    try walkAndTest(
        allocator,
        "ion-tests/iontestdata_1_1/good/equivs",
        &.{ ".ion" },
        skip,
        struct {
            fn run(path: []const u8, data: []const u8) !void {
                checkGroup(data, true) catch |e| {
                    std.debug.print("equivs failed: {s}: {s}\n", .{ path, @errorName(e) });
                    return e;
                };
            }
        }.run,
    );
}

test "ion-tests non-equiv groups" {
    const allocator = std.testing.allocator;

    try walkAndTest(
        allocator,
        "ion-tests/iontestdata/good/non-equivs",
        &.{ ".ion" },
        &global_skip_list,
        struct {
            fn run(path: []const u8, data: []const u8) !void {
                checkGroup(data, false) catch |e| {
                    std.debug.print("non-equivs failed: {s}: {s}\n", .{ path, @errorName(e) });
                    return e;
                };
            }
        }.run,
    );
}

test "ion-tests 1_1 non-equiv groups" {
    const allocator = std.testing.allocator;

    try walkAndTest(
        allocator,
        "ion-tests/iontestdata_1_1/good/non-equivs",
        &.{ ".ion" },
        &global_skip_list,
        struct {
            fn run(path: []const u8, data: []const u8) !void {
                checkGroup(data, false) catch |e| {
                    std.debug.print("non-equivs failed: {s}: {s}\n", .{ path, @errorName(e) });
                    return e;
                };
            }
        }.run,
    );
}

const FormatPair = struct { from: u32, to: u32 };

const format_pairs = [_]FormatPair{
    .{ .from = 0, .to = 1 }, // binary -> compact
    .{ .from = 0, .to = 2 }, // binary -> lines
    .{ .from = 0, .to = 3 }, // binary -> pretty
    .{ .from = 1, .to = 0 }, // compact -> binary
    .{ .from = 1, .to = 2 }, // compact -> lines
    .{ .from = 1, .to = 3 }, // compact -> pretty
    .{ .from = 2, .to = 0 }, // lines -> binary
    .{ .from = 2, .to = 1 }, // lines -> compact
    .{ .from = 2, .to = 3 }, // lines -> pretty
    .{ .from = 3, .to = 0 }, // pretty -> binary
    .{ .from = 3, .to = 1 }, // pretty -> compact
    .{ .from = 3, .to = 2 }, // pretty -> lines
};

test "ion-tests good roundtrip (format matrix)" {
    const allocator = std.testing.allocator;
    const skip = try concatSkipLists(allocator, &.{ &global_skip_list, &round_trip_skip_list });
    defer allocator.free(skip);

    try walkAndTest(
        allocator,
        "ion-tests/iontestdata/good",
        &.{ ".ion", ".10n" },
        skip,
        struct {
            fn run(path: []const u8, data: []const u8) !void {
                for (format_pairs) |pair| {
                    roundtripEq(std.testing.allocator, data, @enumFromInt(pair.from), @enumFromInt(pair.to)) catch |e| {
                        std.debug.print("roundtrip failed: {s} (formats {d}->{d}): {s}\n", .{ path, pair.from, pair.to, @errorName(e) });
                        return e;
                    };
                }
            }
        }.run,
    );
}

test "ion-tests 1_1 good roundtrip (text lines)" {
    const allocator = std.testing.allocator;
    const skip = try concatSkipLists(allocator, &.{ &global_skip_list, &round_trip_skip_list });
    defer allocator.free(skip);

    try walkAndTest(
        allocator,
        "ion-tests/iontestdata_1_1/good",
        &.{ ".ion" },
        skip,
        struct {
            fn run(path: []const u8, data: []const u8) !void {
                roundtripEq(std.testing.allocator, data, .text_lines, .text_lines) catch |e| {
                    std.debug.print("roundtrip failed: {s} (formats lines->lines): {s}\n", .{ path, @errorName(e) });
                    return e;
                };
            }
        }.run,
    );
}

test "ion-tests conformance suite (partial)" {
    const allocator = std.testing.allocator;
    var stats: conformance.Stats = .{};

    const Runner = struct {
        var stats_ptr: *conformance.Stats = undefined;
        fn run(path: []const u8, data: []const u8) !void {
            conformance.runConformanceFile(std.testing.allocator, data, stats_ptr) catch |e| {
                std.debug.print("conformance failed: {s}: {s}\n", .{ path, @errorName(e) });
                return e;
            };
        }
    };
    Runner.stats_ptr = &stats;

    try walkAndTest(
        allocator,
        "ion-tests/conformance",
        &.{ ".ion" },
        &.{},
        Runner.run,
    );

    try std.testing.expect(stats.passed + stats.skipped == stats.branches);
}

fn roundtripEq(allocator: std.mem.Allocator, data: []const u8, format1: ion.Format, format2: ion.Format) !void {
    var src = try ion.parseDocument(allocator, data);
    defer src.deinit();

    const b1 = try ion.serializeDocument(allocator, format1, src.elements);
    defer allocator.free(b1);
    var d1 = try ion.parseDocument(allocator, b1);
    defer d1.deinit();

    const b2 = try ion.serializeDocument(allocator, format2, d1.elements);
    defer allocator.free(b2);
    var d2 = ion.parseDocument(allocator, b2) catch |e| {
        if (format2 != .binary) {
            std.debug.print("roundtrip produced unparsable text:\n{s}\n", .{b2});
        }
        return e;
    };
    defer d2.deinit();

    if (!ion.eq.ionEqElements(src.elements, d2.elements)) {
        const src_dbg = ion.serializeDocument(allocator, .text_pretty, src.elements) catch "";
        defer if (src_dbg.len != 0) allocator.free(src_dbg);
        const dst_dbg = ion.serializeDocument(allocator, .text_pretty, d2.elements) catch "";
        defer if (dst_dbg.len != 0) allocator.free(dst_dbg);
        if (src_dbg.len != 0 and dst_dbg.len != 0) {
            std.debug.print("roundtrip mismatch src(pretty):\n{s}\n", .{src_dbg});
            std.debug.print("roundtrip mismatch dst(pretty):\n{s}\n", .{dst_dbg});
        }
        return error.RoundTripFailed;
    }
}

fn hasAnnotation(elem: ion.value.Element, text: []const u8) bool {
    for (elem.annotations) |a| {
        if (a.text) |t| {
            if (std.mem.eql(u8, t, text)) return true;
        }
    }
    return false;
}

fn parseEmbeddedDoc(elem: ion.value.Element) !ion.Document {
    return switch (elem.value) {
        .string => |s| try ion.parseDocument(std.testing.allocator, s),
        .blob => |b| try ion.parseDocument(std.testing.allocator, b),
        else => error.InvalidEmbeddedDocument,
    };
}

fn checkGroup(data: []const u8, expect_equivs: bool) !void {
    var doc = try ion.parseDocument(std.testing.allocator, data);
    defer doc.deinit();

    for (doc.elements) |group_container| {
        const embedded = hasAnnotation(group_container, "embedded_documents");
        switch (group_container.value) {
            .list => |group| try compareGroupSequence(group, embedded, expect_equivs),
            .sexp => |group| try compareGroupSequence(group, embedded, expect_equivs),
            .@"struct" => |st| try compareGroupStruct(st, embedded, expect_equivs),
            else => return error.InvalidGroupContainer,
        }
    }
}

fn compareGroupSequence(group: []const ion.value.Element, embedded: bool, expect_equivs: bool) !void {
    var docs = std.ArrayListUnmanaged(ion.Document){};
    defer {
        for (docs.items) |*d| d.deinit();
        docs.deinit(std.testing.allocator);
    }

    var elems = std.ArrayListUnmanaged(ion.value.Element){};
    defer elems.deinit(std.testing.allocator);

    if (embedded) {
        for (group) |e| {
            const d = try parseEmbeddedDoc(e);
            docs.append(std.testing.allocator, d) catch return error.OutOfMemory;
            const wrapper: ion.value.Element = .{ .annotations = &.{}, .value = ion.value.Value{ .sexp = d.elements } };
            elems.append(std.testing.allocator, wrapper) catch return error.OutOfMemory;
        }
    } else {
        elems.appendSlice(std.testing.allocator, group) catch return error.OutOfMemory;
    }

    const g = elems.items;
    for (g, 0..) |a, i| {
        for (g, 0..) |b, j| {
            const eq = ion.eq.ionEqElement(a, b);
            if (i == j) {
                if (!eq) return error.IdentityNotEq;
            } else if (expect_equivs) {
                if (!eq) return error.ExpectedEquivsFailed;
            } else {
                if (eq) return error.ExpectedNonEquivsFailed;
            }
        }
    }
}

fn compareGroupStruct(st: ion.value.Struct, embedded: bool, expect_equivs: bool) !void {
    var docs = std.ArrayListUnmanaged(ion.Document){};
    defer {
        for (docs.items) |*d| d.deinit();
        docs.deinit(std.testing.allocator);
    }

    var values = std.ArrayListUnmanaged(ion.value.Element){};
    defer values.deinit(std.testing.allocator);

    if (embedded) {
        for (st.fields) |f| {
            const d = try parseEmbeddedDoc(f.value);
            docs.append(std.testing.allocator, d) catch return error.OutOfMemory;
            const wrapper: ion.value.Element = .{ .annotations = &.{}, .value = ion.value.Value{ .sexp = d.elements } };
            values.append(std.testing.allocator, wrapper) catch return error.OutOfMemory;
        }
    } else {
        for (st.fields) |f| values.append(std.testing.allocator, f.value) catch return error.OutOfMemory;
    }

    const g = values.items;
    for (g, 0..) |a, i| {
        for (g, 0..) |b, j| {
            const eq = ion.eq.ionEqElement(a, b);
            if (i == j) {
                if (!eq) return error.IdentityNotEq;
            } else if (expect_equivs) {
                if (!eq) return error.ExpectedEquivsFailed;
            } else {
                if (eq) return error.ExpectedNonEquivsFailed;
            }
        }
    }
}

test "ion 1.1 binary containers (basic)" {
    // These are small Ion 1.1 binary encodings taken from ion-rust's Ion 1.1 binary reader tests.
    // The corpus/conformance suites mostly exercise Ion 1.1 text, so keep at least a small amount
    // of coverage here to prevent Ion 1.1 binary decoding from regressing.

    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // { $10: '', $11: 0e0 }
    {
        const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xD4, 0x15, 0xA0, 0x17, 0x6A };
        const elems = try ion.binary11.parseTopLevel(&arena, bytes);
        try std.testing.expectEqual(@as(usize, 1), elems.len);
        try std.testing.expect(elems[0].value == .@"struct");
        const st = elems[0].value.@"struct";
        try std.testing.expectEqual(@as(usize, 2), st.fields.len);
        try std.testing.expectEqual(@as(?u32, 10), st.fields[0].name.sid);
        try std.testing.expect(st.fields[0].name.text == null);
        try std.testing.expect(st.fields[0].value.value == .symbol);
        try std.testing.expectEqualStrings("", st.fields[0].value.value.symbol.text.?);
        try std.testing.expectEqual(@as(?u32, 11), st.fields[1].name.sid);
        try std.testing.expect(st.fields[1].value.value == .float);
        try std.testing.expectEqual(@as(f64, 0.0), st.fields[1].value.value.float);
    }

    // {"foo": 1, $11: 2} (FlexSym mode inside a short struct)
    {
        const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xDA, 0x01, 0xFB, 0x66, 0x6F, 0x6F, 0x61, 0x01, 0x17, 0x61, 0x02 };
        const elems = try ion.binary11.parseTopLevel(&arena, bytes);
        try std.testing.expectEqual(@as(usize, 1), elems.len);
        const st = elems[0].value.@"struct";
        try std.testing.expectEqual(@as(usize, 2), st.fields.len);
        try std.testing.expect(st.fields[0].name.text != null);
        try std.testing.expectEqualStrings("foo", st.fields[0].name.text.?);
        try std.testing.expect(st.fields[0].value.value == .int);
        try std.testing.expectEqual(@as(i128, 1), st.fields[0].value.value.int.small);
        try std.testing.expectEqual(@as(?u32, 11), st.fields[1].name.sid);
        try std.testing.expect(st.fields[1].value.value == .int);
        try std.testing.expectEqual(@as(i128, 2), st.fields[1].value.value.int.small);
    }

    // [null.null, '', "hello"]
    {
        const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xB8, 0xEA, 0xA0, 0x95, 0x68, 0x65, 0x6C, 0x6C, 0x6F };
        const elems = try ion.binary11.parseTopLevel(&arena, bytes);
        try std.testing.expectEqual(@as(usize, 1), elems.len);
        try std.testing.expect(elems[0].value == .list);
        const items = elems[0].value.list;
        try std.testing.expectEqual(@as(usize, 3), items.len);
        try std.testing.expect(items[0].value == .null);
        try std.testing.expect(items[1].value == .symbol);
        try std.testing.expectEqualStrings("", items[1].value.symbol.text.?);
        try std.testing.expect(items[2].value == .string);
        try std.testing.expectEqualStrings("hello", items[2].value.string);
    }
}

test "ion 1.1 binary e-expression 12-bit address (minimal)" {
    // Minimal coverage for the EExpressionWith12BitAddress encoding (0x40..0x4F).
    // This uses a synthetic user macro at address 64 that expands to its single argument.

    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Build a macro table with a single-parameter macro at address 64.
    const params = try arena.allocator().alloc(ion.macro.Param, 1);
    params[0] = .{ .ty = .tagged, .card = .one, .name = "vals", .shape = null };

    const body = try arena.allocator().alloc(ion.value.Element, 1);
    body[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%vals") } };

    const macros = try arena.allocator().alloc(ion.macro.Macro, 65);
    @memset(macros, ion.macro.Macro{ .name = null, .params = &.{}, .body = &.{} });
    macros[64] = .{ .name = null, .params = params, .body = body };

    const tab = ion.macro.MacroTable{ .macros = macros };

    // Invoke macro address 64 using the 12-bit address encoding:
    // opcode 0x40 + next byte 0x00 => bias 64, address 64.
    //
    // Argument is a single tagged int(1): 0x61 0x01.
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0x40, 0x00, 0x61, 0x01 };
    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes, &tab);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
}
