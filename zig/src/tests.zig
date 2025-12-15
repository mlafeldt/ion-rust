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
