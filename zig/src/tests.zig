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

test "ion 1.1 binary delimited list" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // F1 => delimited list, terminated by F0.
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xF1, 0x61, 0x01, 0x61, 0x02, 0xF0 };
    const elems = try ion.binary11.parseTopLevel(&arena, bytes);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .list);
    const items = elems[0].value.list;
    try std.testing.expectEqual(@as(usize, 2), items.len);
    try std.testing.expectEqual(@as(i128, 1), items[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), items[1].value.int.small);
}

test "ion 1.1 binary annotations sequence (E4)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // E4 <FlexUInt(sid=1)> <int(1)>
    // FlexUInt(1)=0x03.
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xE4, 0x03, 0x61, 0x01 };
    const elems = try ion.binary11.parseTopLevel(&arena, bytes);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expectEqual(@as(usize, 1), elems[0].annotations.len);
    try std.testing.expectEqual(@as(?u32, 1), elems[0].annotations[0].sid);
    try std.testing.expect(elems[0].annotations[0].text == null);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
}

test "ion 1.1 binary long string and long symbol" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // F9 <FlexUInt(5)> "hello", FA <FlexUInt(3)> "foo"
    // FlexUInt(5)=0x0B, FlexUInt(3)=0x07.
    const bytes = &[_]u8{
        0xE0, 0x01, 0x01, 0xEA,
        0xF9, 0x0B, 'h', 'e', 'l', 'l', 'o',
        0xFA, 0x07, 'f', 'o', 'o',
    };
    const elems = try ion.binary11.parseTopLevel(&arena, bytes);
    try std.testing.expectEqual(@as(usize, 2), elems.len);
    try std.testing.expect(elems[0].value == .string);
    try std.testing.expectEqualStrings("hello", elems[0].value.string);
    try std.testing.expect(elems[1].value == .symbol);
    try std.testing.expect(elems[1].value.symbol.text != null);
    try std.testing.expectEqualStrings("foo", elems[1].value.symbol.text.?);
}

test "ion 1.1 binary NOP padding (EC/ED)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // EC => 1-byte NOP, ED <FlexUInt(n)> <n bytes>.
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xEC, 0xED, 0x05, 0xAA, 0xBB, 0x61, 0x01 };
    const elems = try ion.binary11.parseTopLevel(&arena, bytes);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
}

test "ion 1.1 binary decimals accept large FlexInt encodings" {
    // Conformance uses non-minimal FlexInt encodings (e.g. exponent=0 encoded in multiple bytes).
    // Keep a regression test that exercises `shift > 16` so we don't accidentally reintroduce
    // small fixed caps in FlexInt/FlexUInt decoding.

    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Long decimal:
    //   F7 <flexuint payload_len=17> <FlexInt(0) encoded with shift=17 bytes>
    //
    // FlexUInt(17) with minimal 1-byte encoding: (17<<1)|1 = 0x23.
    // FlexInt(0) with shift=17: only the tag bit set at bit 16 => byte[2]=0x01, others 0.
    const bytes = &[_]u8{
        0xE0, 0x01, 0x01, 0xEA,
        0xF7, 0x23,
        0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    };
    const elems = try ion.binary11.parseTopLevel(&arena, bytes);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .decimal);
    try std.testing.expect(!elems[0].value.decimal.is_negative);
    try std.testing.expectEqual(@as(i32, 0), elems[0].value.decimal.exponent);
    try std.testing.expectEqual(@as(i128, 0), elems[0].value.decimal.coefficient.small);
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

test "ion 1.1 binary e-expression FlexSym inline symbol (single)" {
    // Exercise `.flex_sym` decoding for non-tagged macro parameters, including the inline-text
    // (negative) FlexSym form.

    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 64: (flex_sym::sym) => (%sym)
    const params = try arena.allocator().alloc(ion.macro.Param, 1);
    params[0] = .{ .ty = .flex_sym, .card = .one, .name = "sym", .shape = null };

    const body = try arena.allocator().alloc(ion.value.Element, 1);
    body[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%sym") } };

    const macros = try arena.allocator().alloc(ion.macro.Macro, 65);
    @memset(macros, ion.macro.Macro{ .name = null, .params = &.{}, .body = &.{} });
    macros[64] = .{ .name = null, .params = params, .body = body };

    const tab = ion.macro.MacroTable{ .macros = macros };

    // Invoke macro address 64 using the 12-bit address encoding (0x40..0x4F) with one FlexSym arg:
    //   FlexInt(-2) => 0xFD, followed by 2 bytes of UTF-8 symbol text.
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0x40, 0x00, 0xFD, 'h', 'i' };
    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes, &tab);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .symbol);
    try std.testing.expectEqualStrings("hi", elems[0].value.symbol.text.?);
}

test "ion 1.1 binary e-expression FlexSym inline symbols (tagless group)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 64: (flex_sym::vals*) => (%vals)
    const params = try arena.allocator().alloc(ion.macro.Param, 1);
    params[0] = .{ .ty = .flex_sym, .card = .zero_or_many, .name = "vals", .shape = null };

    const body = try arena.allocator().alloc(ion.value.Element, 1);
    body[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%vals") } };

    const macros = try arena.allocator().alloc(ion.macro.Macro, 65);
    @memset(macros, ion.macro.Macro{ .name = null, .params = &.{}, .body = &.{} });
    macros[64] = .{ .name = null, .params = params, .body = body };

    const tab = ion.macro.MacroTable{ .macros = macros };

    // Bitmap low 2 bits = 0b10 (ArgGroup) for the single variadic parameter.
    // Expression group payload is 6 bytes: "hi" then "yo" as inline FlexSyms.
    const bytes = &[_]u8{
        0xE0, 0x01, 0x01, 0xEA,
        0x40, 0x00,
        0x02, // bitmap
        0x0D, // FlexUInt(6)
        0xFD, 'h', 'i',
        0xFD, 'y', 'o',
    };
    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes, &tab);
    try std.testing.expectEqual(@as(usize, 2), elems.len);
    try std.testing.expect(elems[0].value == .symbol);
    try std.testing.expect(elems[1].value == .symbol);
    try std.testing.expectEqualStrings("hi", elems[0].value.symbol.text.?);
    try std.testing.expectEqualStrings("yo", elems[1].value.symbol.text.?);
}

test "ion 1.1 binary e-expression FlexUInt big value" {
    // Exercises FlexUInt values that exceed `usize` and `i128`, which can appear in macro arg
    // positions for `.flex_uint` parameters.

    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 64: (flex_uint::n) => (%n)
    const params = try arena.allocator().alloc(ion.macro.Param, 1);
    params[0] = .{ .ty = .flex_uint, .card = .one, .name = "n", .shape = null };

    const body = try arena.allocator().alloc(ion.value.Element, 1);
    body[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%n") } };

    const macros = try arena.allocator().alloc(ion.macro.Macro, 65);
    @memset(macros, ion.macro.Macro{ .name = null, .params = &.{}, .body = &.{} });
    macros[64] = .{ .name = null, .params = params, .body = body };

    const tab = ion.macro.MacroTable{ .macros = macros };

    // Encode a FlexUInt with shift=19 such that (raw >> 19) == 2^128.
    // raw has bits at 18 (tag bit) and 147 (value bit).
    const flex = &[_]u8{
        0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08,
    };
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0x40, 0x00 } ++ flex;
    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes, &tab);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[0].value.int == .big);
    const bi = elems[0].value.int.big;
    try std.testing.expect(bi.toConst().positive);
    try std.testing.expectEqual(@as(usize, 129), bi.toConst().bitCountAbs());
}

test "ion 1.1 binary e-expression bitmap with 2 variadic params" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 64: (tagged::a* tagged::b*) => (%a %b)
    const params = try arena.allocator().alloc(ion.macro.Param, 2);
    params[0] = .{ .ty = .tagged, .card = .zero_or_many, .name = "a", .shape = null };
    params[1] = .{ .ty = .tagged, .card = .zero_or_many, .name = "b", .shape = null };

    const body = try arena.allocator().alloc(ion.value.Element, 2);
    body[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%a") } };
    body[1] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%b") } };

    const macros = try arena.allocator().alloc(ion.macro.Macro, 65);
    @memset(macros, ion.macro.Macro{ .name = null, .params = &.{}, .body = &.{} });
    macros[64] = .{ .name = null, .params = params, .body = body };

    const tab = ion.macro.MacroTable{ .macros = macros };

    // F5 <addr=64> <args_len=8> <bitmap=0x09> <int(1)> <group len=4> <int(2)> <int(3)>
    // FlexUInt(64)=0x81, FlexUInt(8)=0x11, group len FlexUInt(4)=0x09.
    // bitmap groups: a=0b01 (single), b=0b10 (arg group) => 0b1001.
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xF5, 0x81, 0x11, 0x09, 0x61, 0x01, 0x09, 0x61, 0x02, 0x61, 0x03 };
    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes, &tab);
    try std.testing.expectEqual(@as(usize, 3), elems.len);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), elems[1].value.int.small);
    try std.testing.expectEqual(@as(i128, 3), elems[2].value.int.small);
}

test "ion 1.1 binary e-expression bitmap spans multiple bytes" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 64: (tagged::p0* tagged::p1* tagged::p2* tagged::p3* tagged::p4*) => (%p0 %p1 %p2 %p3 %p4)
    const params = try arena.allocator().alloc(ion.macro.Param, 5);
    params[0] = .{ .ty = .tagged, .card = .zero_or_many, .name = "p0", .shape = null };
    params[1] = .{ .ty = .tagged, .card = .zero_or_many, .name = "p1", .shape = null };
    params[2] = .{ .ty = .tagged, .card = .zero_or_many, .name = "p2", .shape = null };
    params[3] = .{ .ty = .tagged, .card = .zero_or_many, .name = "p3", .shape = null };
    params[4] = .{ .ty = .tagged, .card = .zero_or_many, .name = "p4", .shape = null };

    const body = try arena.allocator().alloc(ion.value.Element, 5);
    body[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%p0") } };
    body[1] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%p1") } };
    body[2] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%p2") } };
    body[3] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%p3") } };
    body[4] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%p4") } };

    const macros = try arena.allocator().alloc(ion.macro.Macro, 65);
    @memset(macros, ion.macro.Macro{ .name = null, .params = &.{}, .body = &.{} });
    macros[64] = .{ .name = null, .params = params, .body = body };

    const tab = ion.macro.MacroTable{ .macros = macros };

    // 5 variadic params => bitmap length 2 bytes. Grouping choices:
    // p0=single (01), p1=empty (00), p2=arg group (10), p3=empty (00), p4=single (01)
    // => bitmap bits: 01 00 10 00 01 => bytes { 0x21, 0x01 }.
    //
    // args payload bytes:
    // - bitmap (2 bytes)
    // - p0: int(1)
    // - p2 group: len=4, int(2) int(3)
    // - p4: int(4)
    // Total args_len = 11 => FlexUInt(11)=0x17.
    const bytes = &[_]u8{
        0xE0, 0x01, 0x01, 0xEA,
        0xF5, 0x81, 0x17,
        0x21, 0x01,
        0x61, 0x01,
        0x09, 0x61, 0x02, 0x61, 0x03,
        0x61, 0x04,
    };
    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes, &tab);
    try std.testing.expectEqual(@as(usize, 4), elems.len);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), elems[1].value.int.small);
    try std.testing.expectEqual(@as(i128, 3), elems[2].value.int.small);
    try std.testing.expectEqual(@as(i128, 4), elems[3].value.int.small);
}

test "ion 1.1 binary e-expression length-prefixed (0xF5, minimal)" {
    // Minimal coverage for the length-prefixed e-expression opcode (0xF5).
    // This uses a synthetic user macro at address 64 that expands to its argument group.

    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Build a macro table with a single variadic parameter macro at address 64.
    const params = try arena.allocator().alloc(ion.macro.Param, 1);
    params[0] = .{ .ty = .tagged, .card = .zero_or_many, .name = "vals", .shape = null };

    const body = try arena.allocator().alloc(ion.value.Element, 1);
    body[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%vals") } };

    const macros = try arena.allocator().alloc(ion.macro.Macro, 65);
    @memset(macros, ion.macro.Macro{ .name = null, .params = &.{}, .body = &.{} });
    macros[64] = .{ .name = null, .params = params, .body = body };

    const tab = ion.macro.MacroTable{ .macros = macros };

    // Invoke macro address 64 using a length-prefixed e-expression:
    //   F5 <flexuint addr=64> <flexuint args_len=3> <bitmap=01> <tagged int(1)>
    //
    // FlexUInt encoding: 1-byte values are written as `(value << 1) | 1`.
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xF5, 0x81, 0x07, 0x01, 0x61, 0x01 };
    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes, &tab);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
}

test "ion 1.1 binary e-expression length-prefixed (0xF5, multi-param)" {
    // Exercises length-prefixed decoding for a signature with required + optional params.

    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 64: expands to `%a` then `%b`.
    const params = try arena.allocator().alloc(ion.macro.Param, 2);
    params[0] = .{ .ty = .tagged, .card = .one, .name = "a", .shape = null };
    params[1] = .{ .ty = .tagged, .card = .zero_or_one, .name = "b", .shape = null };

    const body = try arena.allocator().alloc(ion.value.Element, 2);
    body[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%a") } };
    body[1] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%b") } };

    const macros = try arena.allocator().alloc(ion.macro.Macro, 65);
    @memset(macros, ion.macro.Macro{ .name = null, .params = &.{}, .body = &.{} });
    macros[64] = .{ .name = null, .params = params, .body = body };

    const tab = ion.macro.MacroTable{ .macros = macros };

    // Case 1: b present as ValueExprLiteral.
    // args payload: <bitmap=01> <a:int(1)> <b:int(2)>
    {
        const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xF5, 0x81, 0x0B, 0x01, 0x61, 0x01, 0x61, 0x02 };
        const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes, &tab);
        try std.testing.expectEqual(@as(usize, 2), elems.len);
        try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
        try std.testing.expectEqual(@as(i128, 2), elems[1].value.int.small);
    }

    // Case 2: b empty.
    // args payload: <bitmap=00> <a:int(1)>
    {
        const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xF5, 0x81, 0x07, 0x00, 0x61, 0x01 };
        const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes, &tab);
        try std.testing.expectEqual(@as(usize, 1), elems.len);
        try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
    }
}

test "ion 1.1 binary macro-shape tagless group (minimal)" {
    // Mirrors the conformance demo idea for `tiny_decimal_values`, but in a minimal synthetic form:
    // - define `tiny_decimal` as a shape macro producing a decimal via `.make_decimal`
    // - define `tiny_decimal_values` taking `tiny_decimal::vals*` and expanding `%vals`
    // - invoke `tiny_decimal_values` in Ion 1.1 binary using a delimited arg group containing
    //   two shape-encoded values: (1 2) and (3 4) as tagless int8 pairs.

    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1: tiny_decimal (int8::a int8::b) => (.make_decimal a b)
    const params_td = try arena.allocator().alloc(ion.macro.Param, 2);
    params_td[0] = .{ .ty = .int8, .card = .one, .name = "a", .shape = null };
    params_td[1] = .{ .ty = .int8, .card = .one, .name = "b", .shape = null };

    const body_td = try arena.allocator().alloc(ion.value.Element, 1);
    const call = try arena.allocator().alloc(ion.value.Element, 3);
    call[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, ".make_decimal") } };
    call[1] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "a") } };
    call[2] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "b") } };
    body_td[0] = .{ .annotations = &.{}, .value = .{ .sexp = call } };

    // Macro at address 0: tiny_decimal_values (tiny_decimal::vals*) => (%vals)
    const params_vals = try arena.allocator().alloc(ion.macro.Param, 1);
    params_vals[0] = .{
        .ty = .macro_shape,
        .card = .zero_or_many,
        .name = "vals",
        .shape = .{ .module = null, .name = "tiny_decimal" },
    };
    const body_vals = try arena.allocator().alloc(ion.value.Element, 1);
    body_vals[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%vals") } };

    const macros = try arena.allocator().alloc(ion.macro.Macro, 2);
    @memset(macros, ion.macro.Macro{ .name = null, .params = &.{}, .body = &.{} });
    macros[0] = .{ .name = "tiny_decimal_values", .params = params_vals, .body = body_vals };
    macros[1] = .{ .name = "tiny_decimal", .params = params_td, .body = body_td };

    const tab = ion.macro.MacroTable{ .macros = macros };

    // Invoke macro address 0 (6-bit address form) with one variadic parameter (bitmap/presence=2 => arg group).
    // Arg group: delimited tagless chunk encoding with one chunk containing:
    //   (1,2) (3,4) as two int8 pairs: 01 02 03 04
    //
    // Encoding details:
    // - bitmap/presence: 0x02 (ArgGroup)
    // - group header FlexUInt(0) sentinel: 0x01
    // - chunk_len FlexUInt(4): (4<<1)|1 = 0x09
    // - terminator FlexUInt(0): 0x01
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0x00, 0x02, 0x01, 0x09, 0x01, 0x02, 0x03, 0x04, 0x01 };
    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes, &tab);
    try std.testing.expectEqual(@as(usize, 2), elems.len);
    try std.testing.expect(elems[0].value == .decimal);
    try std.testing.expect(elems[1].value == .decimal);
    try std.testing.expectEqual(@as(i32, 2), elems[0].value.decimal.exponent);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.decimal.coefficient.small);
    try std.testing.expectEqual(@as(i32, 4), elems[1].value.decimal.exponent);
    try std.testing.expectEqual(@as(i128, 3), elems[1].value.decimal.coefficient.small);
}

test "ion 1.1 binary e-expression length-prefixed system make_decimal (0xF5)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Length-prefixed system macro invocation:
    //   F5 <flexuint addr=11> <flexuint args_len=4> <coeff:int(1)> <exp:int(2)>
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xF5, 0x17, 0x09, 0x61, 0x01, 0x61, 0x02 };
    const elems = try ion.binary11.parseTopLevel(&arena, bytes);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .decimal);
    try std.testing.expectEqual(@as(i32, 2), elems[0].value.decimal.exponent);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.decimal.coefficient.small);
}

test "ion 1.1 binary e-expression length-prefixed system make_decimal (big coefficient)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Coefficient is a long int (F6) with a 17-byte payload representing 2^128 (LE two's complement).
    // Exponent is int(0) using the short form opcode 0x60.
    //
    // args_len = 20 bytes:
    //   <F6> <flexuint 17> <17 bytes payload> <0x60>
    const bytes = &[_]u8{
        0xE0, 0x01, 0x01, 0xEA,
        0xF5, 0x17, 0x29,
        0xF6, 0x23,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
        0x60,
    };
    const elems = try ion.binary11.parseTopLevel(&arena, bytes);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .decimal);
    try std.testing.expectEqual(@as(i32, 0), elems[0].value.decimal.exponent);
    try std.testing.expect(!elems[0].value.decimal.is_negative);

    const coeff = elems[0].value.decimal.coefficient;
    try std.testing.expect(coeff == .big);
    const bi = coeff.big;
    try std.testing.expect(bi.toConst().positive);
    try std.testing.expectEqual(@as(usize, 129), bi.toConst().bitCountAbs());

    var buf: [17]u8 = undefined;
    @memset(&buf, 0);
    bi.toConst().writeTwosComplement(&buf, .big);
    const expected = &[_]u8{ 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 };
    try std.testing.expectEqualSlices(u8, expected, &buf);
}

test "ion 1.1 binary e-expression length-prefixed system make_string (0xF5)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // F5 <addr=9> <args_len=8> <bitmap=10 (arg group)> <FlexUInt(6)> <"hello"> (short string)
    // FlexUInt(9)=0x13, FlexUInt(8)=0x11, group length FlexUInt(6)=0x0D
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xF5, 0x13, 0x11, 0x02, 0x0D, 0x95, 0x68, 0x65, 0x6C, 0x6C, 0x6F };
    const elems = try ion.binary11.parseTopLevel(&arena, bytes);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .string);
    try std.testing.expectEqualStrings("hello", elems[0].value.string);
}

test "ion 1.1 binary writer roundtrip (basic)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const list_items = try arena.allocator().alloc(ion.value.Element, 2);
    list_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    list_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };

    const struct_fields = try arena.allocator().alloc(ion.value.StructField, 2);
    struct_fields[0] = .{
        .name = .{ .sid = null, .text = "foo" },
        .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
    };
    struct_fields[1] = .{
        .name = .{ .sid = null, .text = "bar" },
        .value = .{ .annotations = &.{}, .value = .{ .string = "x" } },
    };

    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .string = "hello" } },
        .{ .annotations = &.{}, .value = .{ .symbol = .{ .sid = null, .text = "sym" } } },
        .{ .annotations = &.{}, .value = .{ .decimal = .{ .is_negative = false, .coefficient = .{ .small = 12345 }, .exponent = -2 } } },
        .{ .annotations = &.{}, .value = .{ .blob = &.{ 0x00, 0xFF, 0x01 } } },
        .{ .annotations = &.{}, .value = .{ .list = list_items } },
        .{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = struct_fields } } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();

    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}
