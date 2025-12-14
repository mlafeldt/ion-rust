const std = @import("std");

extern fn ionrs_clear_error() void;
extern fn ionrs_last_error_ptr() [*]const u8;
extern fn ionrs_last_error_len() usize;

extern fn ionrs_parse_ok(data: ?[*]const u8, len: usize) bool;
extern fn ionrs_roundtrip_eq(data: ?[*]const u8, len: usize, format1: u32, format2: u32) bool;
extern fn ionrs_check_equivs(data: ?[*]const u8, len: usize) bool;
extern fn ionrs_check_non_equivs(data: ?[*]const u8, len: usize) bool;

fn lastError(allocator: std.mem.Allocator) ![]u8 {
    const ptr = ionrs_last_error_ptr();
    const len = ionrs_last_error_len();
    return try allocator.dupe(u8, ptr[0..len]);
}

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
    var dir = try std.fs.cwd().openDir(base_path, .{ .iterate = true });
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

        const data = try std.fs.cwd().readFileAlloc(allocator, repo_rel, 64 * 1024 * 1024);
        defer allocator.free(data);

        try test_fn(repo_rel, data);
    }
}

const global_skip_list = [_][]const u8{
    "ion-tests/iontestdata/bad/listWithValueLargerThanSize.10n",
    "ion-tests/iontestdata/good/subfieldVarInt.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt15bit.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt16bit.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt32bit.ion",
    "ion-tests/iontestdata/good/typecodes/T7-large.10n",
    "ion-tests/iontestdata/good/item1.10n",
    "ion-tests/iontestdata/good/localSymbolTableImportZeroMaxId.ion",
    "ion-tests/iontestdata/good/testfile35.ion",
    "ion-tests/iontestdata/good/utf16.ion",
    "ion-tests/iontestdata/good/utf32.ion",
    "ion-tests/iontestdata/good/non-equivs/localSymbolTableWithAnnotations.ion",
    "ion-tests/iontestdata/good/non-equivs/symbolTablesUnknownText.ion",
    "ion-tests/iontestdata/good/intBigSize16.10n",
    "ion-tests/iontestdata/good/intBigSize256.ion",
    "ion-tests/iontestdata/good/intBigSize256.10n",
    "ion-tests/iontestdata/good/intBigSize512.ion",
    "ion-tests/iontestdata/good/intBigSize1201.10n",
    "ion-tests/iontestdata/good/equivs/bigInts.ion",
    "ion-tests/iontestdata/good/equivs/intsLargePositive3.10n",
    "ion-tests/iontestdata/good/equivs/intsLargeNegative3.10n",
};

const round_trip_skip_list = [_][]const u8{
    "ion-tests/iontestdata/good/item1.10n",
    "ion-tests/iontestdata/good/localSymbolTableImportZeroMaxId.ion",
    "ion-tests/iontestdata/good/notVersionMarkers.ion",
    "ion-tests/iontestdata/good/subfieldInt.ion",
    "ion-tests/iontestdata/good/subfieldUInt.ion",
    "ion-tests/iontestdata/good/subfieldVarInt.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt15bit.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt16bit.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt32bit.ion",
    "ion-tests/iontestdata/good/utf16.ion",
    "ion-tests/iontestdata/good/utf32.ion",
};

const equivs_skip_list = [_][]const u8{
    "ion-tests/iontestdata/good/equivs/localSymbolTableAppend.ion",
    "ion-tests/iontestdata/good/equivs/localSymbolTableNullSlots.ion",
    "ion-tests/iontestdata/good/equivs/nonIVMNoOps.ion",
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
                ionrs_clear_error();
                const ok = ionrs_parse_ok(if (data.len == 0) null else data.ptr, data.len);
                if (ok) {
                    std.debug.print("unexpectedly parsed bad file: {s}\n", .{path});
                    return error.UnexpectedSuccess;
                }
            }
        }.run,
    );
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
                ionrs_clear_error();
                const ok = ionrs_check_equivs(if (data.len == 0) null else data.ptr, data.len);
                if (!ok) {
                    const msg = try lastError(std.testing.allocator);
                    defer std.testing.allocator.free(msg);
                    std.debug.print("equivs failed: {s}\n{s}\n", .{ path, msg });
                    return error.EquivsFailed;
                }
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
                ionrs_clear_error();
                const ok = ionrs_check_non_equivs(if (data.len == 0) null else data.ptr, data.len);
                if (!ok) {
                    const msg = try lastError(std.testing.allocator);
                    defer std.testing.allocator.free(msg);
                    std.debug.print("non-equivs failed: {s}\n{s}\n", .{ path, msg });
                    return error.NonEquivsFailed;
                }
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
                    ionrs_clear_error();
                    const ok = ionrs_roundtrip_eq(
                        if (data.len == 0) null else data.ptr,
                        data.len,
                        pair.from,
                        pair.to,
                    );
                    if (!ok) {
                        const msg = try lastError(std.testing.allocator);
                        defer std.testing.allocator.free(msg);
                        std.debug.print(
                            "roundtrip failed: {s} (formats {d}->{d})\n{s}\n",
                            .{ path, pair.from, pair.to, msg },
                        );
                        return error.RoundTripFailed;
                    }
                }
            }
        }.run,
    );
}
