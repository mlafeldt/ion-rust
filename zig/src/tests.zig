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
const conformance_catalog = @import("conformance/catalog.zig");

fn appendFlexUIntShift1(allocator: std.mem.Allocator, list: *std.ArrayListUnmanaged(u8), v: usize) !void {
    const value: u128 = @intCast(v);
    const bits: usize = if (v == 0) 0 else (usize_bits: {
        const lz: usize = @intCast(@clz(value));
        break :usize_bits 128 - lz;
    });
    const n: usize = @max(@as(usize, 1), (bits + 6) / 7);

    const tag: u128 = @as(u128, 1) << @intCast(n - 1);
    const raw: u128 = (value << @intCast(n)) | tag;
    var i: usize = 0;
    while (i < n) : (i += 1) {
        try list.append(allocator, @intCast((raw >> @intCast(i * 8)) & 0xFF));
    }
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

const global_skip_list = [_][]const u8{};

const round_trip_skip_list = [_][]const u8{};

const equivs_skip_list = [_][]const u8{};

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
        &.{".ion"},
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

test "zig ion serializeDocument binary_1_1 emits Ion 1.1 IVM" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const elems = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } }};
    const bytes = try ion.serializeDocument(std.testing.allocator, .binary_1_1, elems);
    defer std.testing.allocator.free(bytes);

    try std.testing.expect(bytes.len >= 4);
    try std.testing.expectEqualSlices(u8, &.{ 0xE0, 0x01, 0x01, 0xEA }, bytes[0..4]);
}

test "zig ion serializeDocument binary_1_1 rejects SID-only symbols" {
    const elems = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = .{ .sid = 200, .text = null } } },
    };
    try std.testing.expectError(ion.IonError.InvalidIon, ion.serializeDocument(std.testing.allocator, .binary_1_1, elems));
}

test "zig ion serializeDocument binary_1_1 rejects SID-only user symbols in annotations" {
    var anns = [_]ion.value.Symbol{.{ .sid = 200, .text = null }};
    const doc = &[_]ion.value.Element{
        .{ .annotations = anns[0..], .value = .{ .int = .{ .small = 1 } } },
    };
    try std.testing.expectError(ion.IonError.InvalidIon, ion.serializeDocument(std.testing.allocator, .binary_1_1, doc));
}

test "zig ion serializeDocument binary_1_1 rejects SID-only user symbols as struct field names" {
    var fields = [_]ion.value.StructField{
        .{ .name = .{ .sid = 200, .text = null }, .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } } },
    };
    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = fields[0..] } } },
    };
    try std.testing.expectError(ion.IonError.InvalidIon, ion.serializeDocument(std.testing.allocator, .binary_1_1, doc));
}

test "zig ion serializeDocument binary_1_1 uses system symbol addresses in module prelude" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const sym_a = try ion.value.makeSymbol(&arena, "a");
    const elems = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .symbol = sym_a } }};
    const bytes = try ion.serializeDocument(std.testing.allocator, .binary_1_1, elems);
    defer std.testing.allocator.free(bytes);

    // Default test configuration uses the ion-tests Ion 1.1 system symtab, where:
    // - module == 15
    // - symbols == 7
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0xEE, 0x0F }) != null);
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0xEE, 0x07 }) != null);
}

test "zig ion serializeDocument binary_1_1 does not emit module prelude when unnecessary" {
    const elems = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = .{ .sid = null, .text = "$ion" } } },
    };
    const bytes = try ion.serializeDocument(std.testing.allocator, .binary_1_1, elems);
    defer std.testing.allocator.free(bytes);

    // No user symbols appear in the stream, so `writeBinary11SelfContained` should not emit the
    // `$ion::(module ...)` prelude (which contains the system symbol address for "module": EE 0F).
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0xEE, 0x0F }) == null);
}

test "zig ion serializeDocument binary_1_1_raw does not emit module prelude" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const sym_a = try ion.value.makeSymbol(&arena, "a");
    const elems = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .symbol = sym_a } }};
    const bytes = try ion.serializeDocument(std.testing.allocator, .binary_1_1_raw, elems);
    defer std.testing.allocator.free(bytes);

    // `binary_1_1_raw` does not attempt to make output self-contained, so it should not emit
    // `$ion::(module ...)` up front.
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0xEE, 0x0F }) == null);
}

test "ion.serializeDocumentBinary11WithOptions controls container encoding" {
    const allocator = std.testing.allocator;

    var items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
    };
    const elems = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .list = items[0..] },
    }};

    const delimited = try ion.serializeDocumentBinary11WithOptions(allocator, elems, .{ .container_encoding = .delimited });
    defer allocator.free(delimited);
    try std.testing.expectEqualSlices(u8, &.{ 0xE0, 0x01, 0x01, 0xEA }, delimited[0..4]);
    try std.testing.expect(delimited.len >= 5);
    try std.testing.expectEqual(@as(u8, 0xF1), delimited[4]);

    const prefixed = try ion.serializeDocumentBinary11WithOptions(allocator, elems, .{ .container_encoding = .length_prefixed });
    defer allocator.free(prefixed);
    try std.testing.expectEqualSlices(u8, &.{ 0xE0, 0x01, 0x01, 0xEA }, prefixed[0..4]);
    try std.testing.expect(prefixed.len >= 5);
    try std.testing.expect(prefixed[4] != 0xF1);
}

test "ion 1.1 writer11 symbol address opcodes at E2/E3 boundary roundtrip" {
    const allocator = std.testing.allocator;

    const doc_e2 = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .symbol = .{ .sid = 65_791, .text = null } },
    }};
    const bytes_e2 = try ion.serializeDocument(allocator, .binary_1_1_raw, doc_e2);
    defer allocator.free(bytes_e2);

    // E2 uses a 2-byte little-endian payload, biased by 256.
    try std.testing.expect(std.mem.indexOf(u8, bytes_e2, &.{0xE2}) != null);

    var parsed_e2 = try ion.parseDocument(allocator, bytes_e2);
    defer parsed_e2.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_e2, parsed_e2.elements));

    const doc_e3 = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .symbol = .{ .sid = 65_792, .text = null } },
    }};
    const bytes_e3 = try ion.serializeDocument(allocator, .binary_1_1_raw, doc_e3);
    defer allocator.free(bytes_e3);

    // E3 uses a 3-byte little-endian payload, biased by 65,792.
    try std.testing.expect(std.mem.indexOf(u8, bytes_e3, &.{0xE3}) != null);

    var parsed_e3 = try ion.parseDocument(allocator, bytes_e3);
    defer parsed_e3.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_e3, parsed_e3.elements));
}

test "ion 1.1 writer11 symbol address opcodes at E1/E2 boundary roundtrip" {
    const allocator = std.testing.allocator;

    const doc_e1 = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .symbol = .{ .sid = 255, .text = null } },
    }};
    const bytes_e1 = try ion.serializeDocument(allocator, .binary_1_1_raw, doc_e1);
    defer allocator.free(bytes_e1);

    try std.testing.expect(std.mem.indexOf(u8, bytes_e1, &.{0xE1}) != null);

    var parsed_e1 = try ion.parseDocument(allocator, bytes_e1);
    defer parsed_e1.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_e1, parsed_e1.elements));

    const doc_e2 = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .symbol = .{ .sid = 256, .text = null } },
    }};
    const bytes_e2 = try ion.serializeDocument(allocator, .binary_1_1_raw, doc_e2);
    defer allocator.free(bytes_e2);

    try std.testing.expect(std.mem.indexOf(u8, bytes_e2, &.{0xE2}) != null);

    var parsed_e2 = try ion.parseDocument(allocator, bytes_e2);
    defer parsed_e2.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_e2, parsed_e2.elements));
}

test "ion 1.1 writer11 rejects unencodable symbol IDs" {
    const allocator = std.testing.allocator;

    const max_encodable_sid: u32 = 0x00FF_FFFF + 65_792;
    const doc_max = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .symbol = .{ .sid = max_encodable_sid, .text = null } },
    }};
    const bytes = try ion.serializeDocument(allocator, .binary_1_1_raw, doc_max);
    defer allocator.free(bytes);
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{0xE3}) != null);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_max, parsed.elements));

    const doc_too_big = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .symbol = .{ .sid = max_encodable_sid + 1, .text = null } },
    }};
    try std.testing.expectError(ion.IonError.InvalidIon, ion.serializeDocument(allocator, .binary_1_1_raw, doc_too_big));
}

test "ion 1.1 writer11 encodes system symbol text via 0xEE in addresses mode" {
    const allocator = std.testing.allocator;

    const doc = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .symbol = .{ .sid = null, .text = "$ion" } },
    }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{ .symbol_encoding = .addresses });
    defer allocator.free(bytes);

    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0xEE, 0x01 }) != null);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed.elements));
}

test "ion 1.1 writer11 inline_text_only does not emit 0xEE for system symbols" {
    const allocator = std.testing.allocator;

    const doc = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .symbol = .{ .sid = null, .text = "$ion" } },
    }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{ .symbol_encoding = .inline_text_only });
    defer allocator.free(bytes);

    // "$ion" should be emitted as a short inline symbol (A0 + len).
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{0xA4}) != null);
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0xEE, 0x01 }) == null);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed.elements));
}

test "ion 1.1 writer11 encodes SID-only user symbols by address" {
    const allocator = std.testing.allocator;

    const doc = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .symbol = .{ .sid = 300, .text = null } },
    }};

    const bytes = try ion.serializeDocument(allocator, .binary_1_1_raw, doc);
    defer allocator.free(bytes);

    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{0xE2}) != null);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed.elements));
}

test "ion 1.1 writer11 long string uses 0xF9" {
    const allocator = std.testing.allocator;

    const s = "aaaaaaaaaaaaaaaa"; // 16 bytes
    const doc = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .string = s },
    }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{});
    defer allocator.free(bytes);

    try std.testing.expect(bytes.len >= 5);
    try std.testing.expect(bytes[4] == 0xF9);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed.elements));
}

test "ion 1.1 writer11 long symbol uses 0xFA" {
    const allocator = std.testing.allocator;

    const t = "abcdefghijklmnop"; // 16 bytes, not a system symbol
    const doc = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .symbol = .{ .sid = null, .text = t } },
    }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{});
    defer allocator.free(bytes);

    try std.testing.expect(bytes.len >= 5);
    try std.testing.expect(bytes[4] == 0xFA);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed.elements));
}

test "ion 1.1 writer11 long int uses 0xF6" {
    const allocator = std.testing.allocator;

    const v: i128 = @as(i128, 1) << 72;
    const doc = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .int = .{ .small = v } },
    }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{});
    defer allocator.free(bytes);

    try std.testing.expect(bytes.len >= 5);
    try std.testing.expect(bytes[4] == 0xF6);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed.elements));
}

test "ion 1.1 writer11 long decimal uses 0xF7" {
    const allocator = std.testing.allocator;

    const coeff: i128 = @as(i128, 1) << 120;
    const doc = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .decimal = .{ .is_negative = false, .coefficient = .{ .small = coeff }, .exponent = 0 } },
    }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{});
    defer allocator.free(bytes);

    try std.testing.expect(bytes.len >= 5);
    try std.testing.expect(bytes[4] == 0xF7);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed.elements));
}

test "ion 1.1 writer11 encodes decimal negative zero marker" {
    const allocator = std.testing.allocator;

    const doc = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .decimal = .{ .is_negative = true, .coefficient = .{ .small = 0 }, .exponent = 0 } },
    }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{});
    defer allocator.free(bytes);

    // Decimal with exponent 0 emits FlexInt(0) = 0x01. Negative zero adds an extra 0x00 marker.
    // This should produce a short decimal opcode with payload length 2 => 0x72.
    try std.testing.expect(bytes.len >= 7);
    try std.testing.expect(bytes[4] == 0x72);
    try std.testing.expect(bytes[5] == 0x01);
    try std.testing.expect(bytes[6] == 0x00);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed.elements));
}

test "ion 1.1 writer11 blob/clob use 0xFE/0xFF" {
    const allocator = std.testing.allocator;

    const bytes_in = &[_]u8{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 };

    const doc_blob = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .blob = bytes_in },
    }};
    const blob_bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc_blob, .{});
    defer allocator.free(blob_bytes);
    try std.testing.expect(blob_bytes.len >= 5);
    try std.testing.expect(blob_bytes[4] == 0xFE);
    var parsed_blob = try ion.parseDocument(allocator, blob_bytes);
    defer parsed_blob.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_blob, parsed_blob.elements));

    const doc_clob = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .clob = bytes_in },
    }};
    const clob_bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc_clob, .{});
    defer allocator.free(clob_bytes);
    try std.testing.expect(clob_bytes.len >= 5);
    try std.testing.expect(clob_bytes[4] == 0xFF);
    var parsed_clob = try ion.parseDocument(allocator, clob_bytes);
    defer parsed_clob.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_clob, parsed_clob.elements));
}

test "ion 1.1 writer11 timestamp short vs long opcode selection" {
    const allocator = std.testing.allocator;

    const ts_short: ion.value.Timestamp = .{
        .year = 2020,
        .month = null,
        .day = null,
        .hour = null,
        .minute = null,
        .second = null,
        .fractional = null,
        .offset_minutes = null,
        .precision = .year,
    };
    const doc_short = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .timestamp = ts_short } }};
    const short_bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc_short, .{});
    defer allocator.free(short_bytes);
    try std.testing.expect(short_bytes.len >= 5);
    try std.testing.expect(short_bytes[4] == 0x80);
    var parsed_short = try ion.parseDocument(allocator, short_bytes);
    defer parsed_short.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_short, parsed_short.elements));

    const ts_long: ion.value.Timestamp = .{
        .year = 2100, // outside the short timestamp range
        .month = null,
        .day = null,
        .hour = null,
        .minute = null,
        .second = null,
        .fractional = null,
        .offset_minutes = null,
        .precision = .year,
    };
    const doc_long = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .timestamp = ts_long } }};
    const long_bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc_long, .{});
    defer allocator.free(long_bytes);
    try std.testing.expect(long_bytes.len >= 5);
    try std.testing.expect(long_bytes[4] == 0xF8);
    var parsed_long = try ion.parseDocument(allocator, long_bytes);
    defer parsed_long.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_long, parsed_long.elements));
}

test "ion 1.1 writer11 delimited struct uses FlexSym escape terminator" {
    const allocator = std.testing.allocator;

    var fields = [_]ion.value.StructField{
        .{ .name = .{ .sid = null, .text = "a" }, .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } } },
    };
    const doc = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .@"struct" = .{ .fields = fields[0..] } },
    }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{ .container_encoding = .delimited });
    defer allocator.free(bytes);

    // Delimited struct ends with a FlexSym escape for 0xF0:
    //   FlexInt(0) then 0xF0
    // and FlexInt(0) in shift-1 form is 0x01.
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0x01, 0xF0 }) != null);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed.elements));
}

test "ion 1.1 writer11 encodes system symbol field name as FlexSym escape" {
    const allocator = std.testing.allocator;

    // "$ion" is a system symbol. In addresses mode, the writer should encode it in FlexSym form
    // as an escape (FlexInt(0) + 0x60+addr).
    var fields = [_]ion.value.StructField{
        .{ .name = .{ .sid = null, .text = "$ion" }, .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } } },
    };
    const doc = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .@"struct" = .{ .fields = fields[0..] } },
    }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{ .container_encoding = .delimited, .symbol_encoding = .addresses });
    defer allocator.free(bytes);

    // FlexSym escape: FlexInt(0) then 0x60 + sys_sid (1).
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0x01, 0x61 }) != null);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed.elements));
}

test "ion 1.1 writer11 timestamp short microseconds/nanoseconds opcodes" {
    const allocator = std.testing.allocator;

    const base: ion.value.Timestamp = .{
        .year = 2020,
        .month = 1,
        .day = 2,
        .hour = 3,
        .minute = 4,
        .second = 5,
        .fractional = null,
        .offset_minutes = null, // unknown offset
        .precision = .fractional,
    };

    const ts_us: ion.value.Timestamp = blk: {
        var ts = base;
        ts.fractional = .{ .is_negative = false, .coefficient = .{ .small = 123_456 }, .exponent = -6 };
        break :blk ts;
    };
    const doc_us = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .timestamp = ts_us } }};
    const us_bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc_us, .{});
    defer allocator.free(us_bytes);
    try std.testing.expect(us_bytes.len >= 5);
    try std.testing.expect(us_bytes[4] == 0x86);
    var parsed_us = try ion.parseDocument(allocator, us_bytes);
    defer parsed_us.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_us, parsed_us.elements));

    const ts_ns: ion.value.Timestamp = blk: {
        var ts = base;
        ts.fractional = .{ .is_negative = false, .coefficient = .{ .small = 987_654_321 }, .exponent = -9 };
        break :blk ts;
    };
    const doc_ns = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .timestamp = ts_ns } }};
    const ns_bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc_ns, .{});
    defer allocator.free(ns_bytes);
    try std.testing.expect(ns_bytes.len >= 5);
    try std.testing.expect(ns_bytes[4] == 0x87);
    var parsed_ns = try ion.parseDocument(allocator, ns_bytes);
    defer parsed_ns.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_ns, parsed_ns.elements));
}

test "ion 1.1 writer11 timestamp known offset short opcodes" {
    const allocator = std.testing.allocator;

    const ts_min: ion.value.Timestamp = .{
        .year = 2020,
        .month = 1,
        .day = 2,
        .hour = 3,
        .minute = 4,
        .second = null,
        .fractional = null,
        .offset_minutes = 0, // UTC
        .precision = .minute,
    };
    const doc_min = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .timestamp = ts_min } }};
    const min_bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc_min, .{});
    defer allocator.free(min_bytes);
    try std.testing.expect(min_bytes.len >= 5);
    try std.testing.expect(min_bytes[4] == 0x88);
    var parsed_min = try ion.parseDocument(allocator, min_bytes);
    defer parsed_min.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_min, parsed_min.elements));

    const ts_sec: ion.value.Timestamp = .{
        .year = 2020,
        .month = 1,
        .day = 2,
        .hour = 3,
        .minute = 4,
        .second = 5,
        .fractional = null,
        .offset_minutes = 0, // UTC
        .precision = .second,
    };
    const doc_sec = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .timestamp = ts_sec } }};
    const sec_bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc_sec, .{});
    defer allocator.free(sec_bytes);
    try std.testing.expect(sec_bytes.len >= 5);
    try std.testing.expect(sec_bytes[4] == 0x89);
    var parsed_sec = try ion.parseDocument(allocator, sec_bytes);
    defer parsed_sec.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_sec, parsed_sec.elements));

    const ts_ms: ion.value.Timestamp = .{
        .year = 2020,
        .month = 1,
        .day = 2,
        .hour = 3,
        .minute = 4,
        .second = 5,
        .fractional = .{ .is_negative = false, .coefficient = .{ .small = 999 }, .exponent = -3 },
        .offset_minutes = 0, // UTC
        .precision = .fractional,
    };
    const doc_ms = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .timestamp = ts_ms } }};
    const ms_bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc_ms, .{});
    defer allocator.free(ms_bytes);
    try std.testing.expect(ms_bytes.len >= 5);
    try std.testing.expect(ms_bytes[4] == 0x8A);
    var parsed_ms = try ion.parseDocument(allocator, ms_bytes);
    defer parsed_ms.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_ms, parsed_ms.elements));
}

test "ion 1.1 writer11 float opcode selection" {
    const allocator = std.testing.allocator;

    const doc_f16 = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .float = 1.5 },
    }};
    const bytes_f16 = try ion.writer11.writeBinary11WithOptions(allocator, doc_f16, .{});
    defer allocator.free(bytes_f16);
    try std.testing.expect(bytes_f16.len >= 5);
    try std.testing.expect(bytes_f16[4] == 0x6B);
    var parsed_f16 = try ion.parseDocument(allocator, bytes_f16);
    defer parsed_f16.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_f16, parsed_f16.elements));

    const f32_exact: f32 = @bitCast(@as(u32, 0x3F800001)); // 1.0000001192092896
    const doc_f32 = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .float = @floatCast(f32_exact) },
    }};
    const bytes_f32 = try ion.writer11.writeBinary11WithOptions(allocator, doc_f32, .{});
    defer allocator.free(bytes_f32);
    try std.testing.expect(bytes_f32.len >= 5);
    try std.testing.expect(bytes_f32[4] == 0x6C);
    var parsed_f32 = try ion.parseDocument(allocator, bytes_f32);
    defer parsed_f32.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_f32, parsed_f32.elements));

    const doc_inf = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .float = std.math.inf(f64) },
    }};
    const bytes_inf = try ion.writer11.writeBinary11WithOptions(allocator, doc_inf, .{});
    defer allocator.free(bytes_inf);
    try std.testing.expect(bytes_inf.len >= 5);
    try std.testing.expect(bytes_inf[4] == 0x6D);
    var parsed_inf = try ion.parseDocument(allocator, bytes_inf);
    defer parsed_inf.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_inf, parsed_inf.elements));
}

test "ion 1.1 writer11 encodes signed zero floats distinctly" {
    const allocator = std.testing.allocator;

    const doc_pos = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .float = 0.0 },
    }};
    const bytes_pos = try ion.writer11.writeBinary11WithOptions(allocator, doc_pos, .{});
    defer allocator.free(bytes_pos);
    try std.testing.expect(bytes_pos.len >= 5);
    try std.testing.expect(bytes_pos[4] == 0x6A);
    var parsed_pos = try ion.parseDocument(allocator, bytes_pos);
    defer parsed_pos.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_pos, parsed_pos.elements));

    const neg_zero: f64 = @bitCast(@as(u64, 0x8000_0000_0000_0000));
    const doc_neg = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .float = neg_zero },
    }};
    const bytes_neg = try ion.writer11.writeBinary11WithOptions(allocator, doc_neg, .{});
    defer allocator.free(bytes_neg);
    try std.testing.expect(bytes_neg.len >= 5);
    try std.testing.expect(bytes_neg[4] != 0x6A);
    var parsed_neg = try ion.parseDocument(allocator, bytes_neg);
    defer parsed_neg.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc_neg, parsed_neg.elements));
}

test "ion 1.1 writer11 encodes integer zero with 0x60" {
    const allocator = std.testing.allocator;

    const doc = &[_]ion.value.Element{.{
        .annotations = &.{},
        .value = .{ .int = .{ .small = 0 } },
    }};
    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{});
    defer allocator.free(bytes);

    try std.testing.expect(bytes.len >= 5);
    try std.testing.expect(bytes[4] == 0x60);

    var parsed = try ion.parseDocument(allocator, bytes);
    defer parsed.deinit();
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed.elements));
}

test "zig ion serializeDocument binary_1_1 inlines system symbols by SID" {
    const elems = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = .{ .sid = 1, .text = null } } }, // $ion
    };
    const bytes = try ion.serializeDocument(std.testing.allocator, .binary_1_1, elems);
    defer std.testing.allocator.free(bytes);

    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0xEE, 0x01 }) != null);
}

test "ion 1.1 writer11 can roundtrip length-prefixed containers" {
    const allocator = std.testing.allocator;

    var arena = try ion.value.Arena.init(allocator);
    defer arena.deinit();

    const sym_a = try ion.value.makeSymbol(&arena, "a");
    const sym_b = try ion.value.makeSymbol(&arena, "b");

    const list_items = try arena.allocator().alloc(ion.value.Element, 2);
    list_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    list_items[1] = .{ .annotations = &.{}, .value = .{ .string = "hello" } };

    const sexp_items = try arena.allocator().alloc(ion.value.Element, 2);
    sexp_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    sexp_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };

    const struct_fields = try arena.allocator().alloc(ion.value.StructField, 2);
    struct_fields[0] = .{ .name = sym_a, .value = .{ .annotations = &.{}, .value = .{ .list = list_items } } };
    struct_fields[1] = .{ .name = sym_b, .value = .{ .annotations = &.{}, .value = .{ .sexp = sexp_items } } };

    const doc = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = struct_fields } } }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{
        .symbol_encoding = .inline_text_only,
        .container_encoding = .length_prefixed,
    });
    defer allocator.free(bytes);

    var arena2 = try ion.value.Arena.init(allocator);
    defer arena2.deinit();
    const parsed = try ion.binary11.parseTopLevel(&arena2, bytes);

    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}

test "ion 1.1 writer11 uses SID-only annotation sequence encoding when possible" {
    const allocator = std.testing.allocator;

    // Two SID-only system symbols => E5 + FlexUInt(sid0) + FlexUInt(sid1)
    var anns = [_]ion.value.Symbol{
        .{ .sid = 1, .text = null }, // $ion
        .{ .sid = 2, .text = null }, // $ion_1_0
    };
    const doc = &[_]ion.value.Element{.{ .annotations = anns[0..], .value = .{ .int = .{ .small = 1 } } }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{ .symbol_encoding = .addresses });
    defer allocator.free(bytes);

    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{0xE5}) != null);
}

test "ion 1.1 writer11 uses E4 for single SID-only annotation" {
    const allocator = std.testing.allocator;

    var anns = [_]ion.value.Symbol{
        .{ .sid = 1, .text = null }, // $ion
    };
    const doc = &[_]ion.value.Element{.{ .annotations = anns[0..], .value = .{ .int = .{ .small = 1 } } }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{ .symbol_encoding = .addresses });
    defer allocator.free(bytes);

    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{0xE4}) != null);
}

test "ion 1.1 writer11 uses E6 for 3+ SID-only annotations" {
    const allocator = std.testing.allocator;

    var anns = [_]ion.value.Symbol{
        .{ .sid = 1, .text = null }, // $ion
        .{ .sid = 2, .text = null }, // $ion_1_0
        .{ .sid = 3, .text = null }, // $ion_1_1
    };
    const doc = &[_]ion.value.Element{.{ .annotations = anns[0..], .value = .{ .int = .{ .small = 1 } } }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{ .symbol_encoding = .addresses });
    defer allocator.free(bytes);

    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{0xE6}) != null);
}

test "ion 1.1 writer11 can write SID-only system annotations in inline-text mode" {
    const allocator = std.testing.allocator;

    // In inline-text mode, SID-only system symbols are rewritten to text and then encoded using
    // FlexSym inline text annotation wrappers.
    var anns = [_]ion.value.Symbol{
        .{ .sid = 1, .text = null }, // $ion
        .{ .sid = 2, .text = null }, // $ion_1_0
    };
    const doc = &[_]ion.value.Element{.{ .annotations = anns[0..], .value = .{ .int = .{ .small = 1 } } }};

    const bytes = try ion.writer11.writeBinary11WithOptions(allocator, doc, .{ .symbol_encoding = .inline_text_only });
    defer allocator.free(bytes);

    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{0xE8}) != null);
}

test "ion.serializeDocument(.binary_1_1_raw) allows SID-only user symbols" {
    const allocator = std.testing.allocator;

    const doc = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .symbol = .{ .sid = 200, .text = null } } }};

    const bytes = try ion.serializeDocument(allocator, .binary_1_1_raw, doc);
    defer allocator.free(bytes);

    var parsed_doc = try ion.parseDocument(allocator, bytes);
    defer parsed_doc.deinit();

    try std.testing.expect(ion.eq.ionEqElements(doc, parsed_doc.elements));
}

test "ion 1.1 binary FlexSym escape returns system symbol as text" {
    const bytes = &[_]u8{
        0xE0, 0x01, 0x01, 0xEA, // IVM
        0xF3, // delimited struct
        0x01, 0x61, // FlexSym escape: system symbol address 1 ($ion)
        0x61, 0x01, // int 1 (1-byte LE twos complement)
        0x01, 0xF0, // FlexSym escape: end delimited
    };

    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const elems = try ion.binary11.parseTopLevel(&arena, bytes);

    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .@"struct");
    const st = elems[0].value.@"struct";
    try std.testing.expectEqual(@as(usize, 1), st.fields.len);
    try std.testing.expectEqualStrings("$ion", st.fields[0].name.text orelse return error.TestExpectedEqual);
    try std.testing.expect(st.fields[0].name.sid == 1);
}

test "ion 1.1 binary can apply $ion::(module ...) encoded via symbol addresses" {
    // This is a minimal Ion 1.1 binary stream:
    //   $ion::(module _ (symbols _ "a" "b"))
    //   $1
    //
    // The module directive is encoded using symbol addresses (so `module` and `symbols` have SIDs
    // but no text). The decoder should still recognize and apply it at top-level.
    const bytes = &[_]u8{
        0xE0, 0x01, 0x01, 0xEA, // IVM
        0xE7, 0x01, 0x61, // annotations: FlexSym escape system symbol address 1 ($ion)
        0xF2, // delimited sexp
        0xEE, 0x0F, // system symbol address 15 ("module" in ion-tests SystemSymtab11)
        0xA1, '_', // inline symbol "_"
        0xF2, // clause: delimited sexp
        0xEE, 0x07, // system symbol address 7 ("symbols")
        0xA1, '_', // inline symbol "_"
        0x91, 'a', // string "a"
        0x91, 'b', // string "b"
        0xF0, // end clause sexp
        0xF0, // end module sexp
        0xE1, 0x01, // symbol address 1 ($1)
    };

    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const res = try ion.binary11.parseTopLevelWithState(&arena, bytes);
    try ion.value.resolveDefaultModuleSymbols11(&arena, res.elements, res.state.user_symbols, res.state.system_loaded);

    try std.testing.expectEqual(@as(usize, 1), res.elements.len);
    try std.testing.expect(res.elements[0].value == .symbol);
    try std.testing.expectEqualStrings("a", res.elements[0].value.symbol.text orelse return error.TestExpectedEqual);
}

test "ion 1.1 binary can infer ion-rust system symbols from module head" {
    // Like the previous test, but the module head uses address 16 (ion-rust's `module`).
    // After the directive is applied, subsequent system symbol addresses should resolve using the
    // ion-rust table, even though tests default to the ion-tests table.
    const bytes = &[_]u8{
        0xE0, 0x01, 0x01, 0xEA, // IVM
        0xE7, 0x01, 0x61, // annotations: FlexSym escape system symbol address 1 ($ion)
        0xF2, // delimited sexp
        0xEE, 0x10, // system symbol address 16 (ion-rust `module`, ion-tests `export`)
        0xA1, '_', // inline symbol "_"
        0xF2, // clause: delimited sexp
        0xEE, 0x07, // system symbol address 7 ("symbols")
        0xA1, '_', // inline symbol "_"
        0x91, 'a', // string "a"
        0xF0, // end clause sexp
        0xF0, // end module sexp
        0xEE, 0x10, // system symbol address 16 again
    };

    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const res = try ion.binary11.parseTopLevelWithState(&arena, bytes);

    try std.testing.expectEqual(@as(usize, 1), res.elements.len);
    try std.testing.expect(res.elements[0].value == .symbol);
    try std.testing.expectEqualStrings("module", res.elements[0].value.symbol.text orelse return error.TestExpectedEqual);
}

test "ion 1.1 writer11 self-contained module prelude can use ion-rust system symbols" {
    const allocator = std.testing.allocator;

    // Force emission of the module prelude by including a user symbol.
    const doc = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "a") } }};

    const bytes = try ion.writer11.writeBinary11SelfContainedWithOptions(allocator, doc, .{ .sys_symtab11_variant = .ion_rust });
    defer allocator.free(bytes);

    // Under the ion-rust system symbol table, the module prelude uses the `symbol_table` clause,
    // which is system symbol address 15.
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0xEE, 0x0F }) != null);
}

test "ion 1.1 writer11 can emit delimited tagged argument groups" {
    const allocator = std.testing.allocator;

    // macro pass(vals*) => %vals
    var params = [_]ion.macro.Param{.{ .ty = .tagged, .card = .zero_or_many, .name = "vals", .shape = null }};
    const body = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%vals") } },
    };
    var macros = [_]ion.macro.Macro{.{
        .name = "pass",
        .params = params[0..],
        .body = body[0..],
    }};
    const tab = ion.macro.MacroTable{ .base_addr = ion.macro.system_macro_count, .macros = macros[0..] };

    const args = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
    };
    const args_by_param = [_][]const ion.value.Element{args[0..]};

    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeUserMacroInvocationLengthPrefixedByNameWithParams(
        allocator,
        &bytes,
        &tab,
        "pass",
        args_by_param[0..],
        .{ .arg_group_encoding = .delimited },
    );

    var arena = try ion.value.Arena.init(allocator);
    defer arena.deinit();
    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes.items, &tab);

    try std.testing.expectEqual(@as(usize, 2), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[1].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), elems[1].value.int.small);
}

test "ion 1.1 writer11 can emit delimited tagless argument groups" {
    const allocator = std.testing.allocator;

    // macro pass_i8(vals*) => ((.$ion::values %) vals)
    var params = [_]ion.macro.Param{.{ .ty = .int8, .card = .zero_or_many, .name = "vals", .shape = null }};
    var inner_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, ".values") } },
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%") } },
    };
    const inner = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = inner_items[0..] } };
    var outer_items = [_]ion.value.Element{
        inner,
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "vals") } },
    };
    const outer = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = outer_items[0..] } };
    const body = [_]ion.value.Element{outer};

    var macros = [_]ion.macro.Macro{.{
        .name = "pass_i8",
        .params = params[0..],
        .body = body[0..],
    }};
    const tab = ion.macro.MacroTable{ .base_addr = ion.macro.system_macro_count, .macros = macros[0..] };

    const args = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };
    const args_by_param = [_][]const ion.value.Element{args[0..]};

    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeUserMacroInvocationLengthPrefixedByNameWithParams(
        allocator,
        &bytes,
        &tab,
        "pass_i8",
        args_by_param[0..],
        .{ .arg_group_encoding = .delimited },
    );

    var arena = try ion.value.Arena.init(allocator);
    defer arena.deinit();
    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes.items, &tab);

    try std.testing.expectEqual(@as(usize, 3), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[1].value == .int);
    try std.testing.expect(elems[2].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), elems[1].value.int.small);
    try std.testing.expectEqual(@as(i128, 3), elems[2].value.int.small);
}

test "ion 1.1 writer11 can emit delimited tagged expression groups for values" {
    const allocator = std.testing.allocator;

    const args = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
    };

    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationLengthPrefixedTaggedVariadicWithOptions(
        allocator,
        &bytes,
        1, // values
        args[0..],
        .{ .arg_group_encoding = .delimited },
    );

    var arena = try ion.value.Arena.init(allocator);
    defer arena.deinit();
    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);

    try std.testing.expectEqual(@as(usize, 2), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[1].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), elems[1].value.int.small);
}

test "ion 1.1 writer11 can emit delimited expression groups for qualified values" {
    const allocator = std.testing.allocator;

    const args = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
    };

    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedValues(allocator, &bytes, args[0..], .{ .arg_group_encoding = .delimited });

    var arena = try ion.value.Arena.init(allocator);
    defer arena.deinit();
    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);

    try std.testing.expectEqual(@as(usize, 2), elems.len);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), elems[1].value.int.small);
}

test "ion 1.1 writer11 can chunk tagless delimited groups" {
    const allocator = std.testing.allocator;

    // macro pass_i8(vals*) => ((.$ion::values %) vals)
    var params = [_]ion.macro.Param{.{ .ty = .int8, .card = .zero_or_many, .name = "vals", .shape = null }};
    var inner_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, ".values") } },
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%") } },
    };
    const inner = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = inner_items[0..] } };
    var outer_items = [_]ion.value.Element{
        inner,
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "vals") } },
    };
    const outer = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = outer_items[0..] } };
    const body = [_]ion.value.Element{outer};

    var macros = [_]ion.macro.Macro{.{
        .name = "pass_i8",
        .params = params[0..],
        .body = body[0..],
    }};
    const tab = ion.macro.MacroTable{ .base_addr = ion.macro.system_macro_count, .macros = macros[0..] };

    const args = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };
    const args_by_param = [_][]const ion.value.Element{args[0..]};

    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(allocator);
    try bytes.appendSlice(allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeUserMacroInvocationLengthPrefixedByNameWithParams(
        allocator,
        &bytes,
        &tab,
        "pass_i8",
        args_by_param[0..],
        .{ .arg_group_encoding = .delimited, .arg_group_chunk_max_bytes = 1 },
    );

    var arena = try ion.value.Arena.init(allocator);
    defer arena.deinit();
    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, bytes.items, &tab);

    try std.testing.expectEqual(@as(usize, 3), elems.len);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), elems[1].value.int.small);
    try std.testing.expectEqual(@as(i128, 3), elems[2].value.int.small);
}

test "zig ion serializeDocument binary_1_1 roundtrips values" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const sym_a = try ion.value.makeSymbol(&arena, "a");
    const sym_field = try ion.value.makeSymbol(&arena, "field");

    const anns = try arena.allocator().alloc(ion.value.Symbol, 1);
    anns[0] = sym_a;

    const struct_fields = try arena.allocator().alloc(ion.value.StructField, 2);
    struct_fields[0] = .{
        .name = sym_field,
        .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
    };
    struct_fields[1] = .{
        .name = sym_a,
        .value = .{ .annotations = &.{}, .value = .{ .string = "hello" } },
    };

    const st = ion.value.Struct{ .fields = struct_fields };

    const elems = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .null = .null } },
        .{ .annotations = &.{}, .value = .{ .bool = true } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = -7 } } },
        .{ .annotations = &.{}, .value = .{ .float = 3.25 } },
        .{ .annotations = &.{}, .value = .{ .decimal = .{ .is_negative = false, .coefficient = .{ .small = 314 }, .exponent = -2 } } },
        .{ .annotations = anns, .value = .{ .symbol = sym_a } },
        .{ .annotations = &.{}, .value = .{ .string = "world" } },
        .{ .annotations = &.{}, .value = .{ .blob = "xyz" } },
        .{ .annotations = &.{}, .value = .{ .clob = "abc" } },
        .{ .annotations = &.{}, .value = .{ .@"struct" = st } },
    };

    const bytes = try ion.serializeDocument(std.testing.allocator, .binary_1_1, elems);
    defer std.testing.allocator.free(bytes);

    const res = try ion.binary11.parseTopLevelWithState(&arena, bytes);
    const parsed = res.elements;
    try ion.value.resolveDefaultModuleSymbols11(&arena, parsed, res.state.user_symbols, res.state.system_loaded);

    try std.testing.expect(ion.eq.ionEqElements(elems, parsed));
}

test "ion 1.1 writer11 can emit length-prefixed system values e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const args = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .string = "hi" } },
        .{ .annotations = &.{}, .value = .{ .bool = true } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationLengthPrefixedTaggedVariadic(std.testing.allocator, &out, 1, &args);

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, null);
    try std.testing.expect(ion.eq.ionEqElements(elems, &args));
}

test "ion 1.1 writer11 can emit length-prefixed system default e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const params = [_]ion.macro.Param{
        .{ .ty = .tagged, .card = .zero_or_many, .name = "expr", .shape = null },
        .{ .ty = .tagged, .card = .zero_or_many, .name = "default_expr", .shape = null },
    };

    const expr_empty = [_]ion.value.Element{};
    const default_args = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 42 } } },
        .{ .annotations = &.{}, .value = .{ .string = "fallback" } },
    };
    const args_by_param = [_][]const ion.value.Element{ &expr_empty, &default_args };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationLengthPrefixedWithParams(std.testing.allocator, &out, 2, &params, &args_by_param, .{});

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, null);
    try std.testing.expect(ion.eq.ionEqElements(elems, &default_args));
}

test "ion 1.1 writer11 can emit qualified system values e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const arg_vals = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedValues(std.testing.allocator, &out, &arg_vals, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(ion.eq.ionEqElements(elems, &arg_vals));
}

test "ion 1.1 writer11 can emit qualified system sum e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const a: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 10 } } };
    const b: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 32 } } };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedSum(std.testing.allocator, &out, a, b, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 1);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[0].value.int == .small);
    try std.testing.expectEqual(@as(i128, 42), elems[0].value.int.small);
}

test "ion 1.1 writer11 can emit qualified system default e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const out_vals = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 4 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 5 } } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedDefault(std.testing.allocator, &out, &.{}, &out_vals, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(ion.eq.ionEqElements(elems, &out_vals));
}

test "ion 1.1 writer11 can emit qualified system annotate e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const ann_text = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .string = "x" } },
        .{ .annotations = &.{}, .value = .{ .string = "y" } },
    };
    const val: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedAnnotate(std.testing.allocator, &out, &ann_text, val, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 1);

    const sx = try ion.value.makeSymbol(&arena, "x");
    const sy = try ion.value.makeSymbol(&arena, "y");
    const anns = arena.allocator().alloc(ion.value.Symbol, 2) catch return ion.IonError.OutOfMemory;
    anns[0] = sx;
    anns[1] = sy;

    const expected = [_]ion.value.Element{.{ .annotations = anns, .value = .{ .int = .{ .small = 7 } } }};
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 writer11 can emit qualified system use e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedUse(std.testing.allocator, &out, "abcs", 2, .{});

    const res = try ion.binary11.parseTopLevelWithState(&arena, out.items);
    try std.testing.expect(res.elements.len == 0);
    try std.testing.expect(res.state.user_symbols.len == 2);
    try std.testing.expectEqualStrings("a", res.state.user_symbols[0].?);
    try std.testing.expectEqualStrings("b", res.state.user_symbols[1].?);
}

test "ion 1.1 writer11 can emit qualified system make_decimal e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const coeff: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 314 } } };
    const exp: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = -2 } } };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedMakeDecimal(std.testing.allocator, &out, coeff, exp, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 1);
    try std.testing.expect(elems[0].value == .decimal);
    try std.testing.expect(!elems[0].value.decimal.is_negative);
    try std.testing.expect(elems[0].value.decimal.coefficient == .small);
    try std.testing.expectEqual(@as(i128, 314), elems[0].value.decimal.coefficient.small);
    try std.testing.expectEqual(@as(i32, -2), elems[0].value.decimal.exponent);
}

test "ion 1.1 writer11 can emit qualified system make_timestamp e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const year: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2025 } } };
    const month: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 12 } } };
    const day: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 26 } } };
    const hour: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    const minute: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    const seconds: ion.value.Element = .{ .annotations = &.{}, .value = .{ .decimal = .{ .is_negative = false, .coefficient = .{ .small = 345 }, .exponent = -2 } } };
    const offset: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 0 } } };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedMakeTimestamp(
        std.testing.allocator,
        &out,
        year,
        month,
        day,
        hour,
        minute,
        seconds,
        offset,
        .{},
    );

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 1);
    try std.testing.expect(elems[0].value == .timestamp);
    const ts = elems[0].value.timestamp;
    try std.testing.expectEqual(@as(i32, 2025), ts.year);
    try std.testing.expectEqual(@as(?u8, 12), ts.month);
    try std.testing.expectEqual(@as(?u8, 26), ts.day);
    try std.testing.expectEqual(@as(?u8, 1), ts.hour);
    try std.testing.expectEqual(@as(?u8, 2), ts.minute);
    try std.testing.expectEqual(@as(?u8, 3), ts.second);
    try std.testing.expect(ts.fractional != null);
    try std.testing.expectEqual(@as(i32, -2), ts.fractional.?.exponent);
    try std.testing.expectEqual(@as(i128, 45), ts.fractional.?.coefficient.small);
    try std.testing.expectEqual(@as(?i16, 0), ts.offset_minutes);
}

test "ion 1.1 writer11 can emit qualified system repeat e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const count: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };
    const exprs = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedRepeat(std.testing.allocator, &out, count, &exprs, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    const expected = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } },
    };
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 writer11 can emit qualified system delta e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const deltas = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedDelta(std.testing.allocator, &out, &deltas, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    const expected = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 4 } } },
    };
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 writer11 can emit qualified system set_symbols and add_symbols directives" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    try ion.writer11.writeSystemMacroInvocationQualifiedSetSymbolsDirectiveText(std.testing.allocator, &out, &.{ "x", "y" }, .{});
    try ion.writer11.writeSystemMacroInvocationQualifiedAddSymbolsDirectiveText(std.testing.allocator, &out, &.{"z"}, .{});

    const res = try ion.binary11.parseTopLevelWithState(&arena, out.items);
    try std.testing.expect(res.elements.len == 0);
    try std.testing.expect(res.state.user_symbols.len == 3);
    try std.testing.expectEqualStrings("x", res.state.user_symbols[0].?);
    try std.testing.expectEqualStrings("y", res.state.user_symbols[1].?);
    try std.testing.expectEqualStrings("z", res.state.user_symbols[2].?);
}

test "ion 1.1 writer11 can emit qualified system flatten e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const list_items_a = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    list_items_a[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    list_items_a[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    const list_a: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_a } };

    const list_items_b = arena.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
    list_items_b[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };
    const list_b: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_b } };

    const seqs = [_]ion.value.Element{ list_a, list_b };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedFlatten(std.testing.allocator, &out, &seqs, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    const expected = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 binary11 decodes canonical qualified meta (addr 3)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const meta_args = [_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } }};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedTaggedGroup(std.testing.allocator, &out, 3, &meta_args, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 0);
}

test "ion 1.1 binary11 decodes canonical qualified flatten (addr 5)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const list_items_a = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    list_items_a[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    list_items_a[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    const list_a: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_a } };

    const list_items_b = arena.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
    list_items_b[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };
    const list_b: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_b } };

    const seqs = [_]ion.value.Element{ list_a, list_b };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedTaggedGroup(std.testing.allocator, &out, 5, &seqs, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    const expected = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 binary11 decodes canonical qualified parse_ion (addr 18)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const bytes: ion.value.Element = .{ .annotations = &.{}, .value = .{ .string = "1 2" } };
    const args = [_]ion.value.Element{bytes};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedTaggedGroup(std.testing.allocator, &out, 18, &args, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 2);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[1].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), elems[1].value.int.small);
}

test "ion 1.1 writer11 can emit canonical qualified meta/flatten/parse_ion helpers" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const meta_args = [_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } }};

    const list_items_a = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    list_items_a[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    list_items_a[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    const list_a: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_a } };

    const list_items_b = arena.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
    list_items_b[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };
    const list_b: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_b } };
    const seqs = [_]ion.value.Element{ list_a, list_b };

    const parse_parts = [_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .string = "1 2" } }};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    try ion.writer11.writeSystemMacroInvocationQualifiedMetaCanonical(std.testing.allocator, &out, &meta_args, .{});
    try ion.writer11.writeSystemMacroInvocationQualifiedFlattenCanonical(std.testing.allocator, &out, &seqs, .{});
    try ion.writer11.writeSystemMacroInvocationQualifiedParseIonCanonical(std.testing.allocator, &out, &parse_parts, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    const expected = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
    };
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 writer11 can select canonical qualified macro addrs via sys_symtab11_variant" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const meta_args = [_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } }};

    const list_items_a = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    list_items_a[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    list_items_a[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    const list_a: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_a } };

    const list_items_b = arena.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
    list_items_b[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };
    const list_b: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_b } };
    const seqs = [_]ion.value.Element{ list_a, list_b };

    const parse_parts = [_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .string = "1 2" } }};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    const opts: ion.writer11.Options = .{ .sys_symtab11_variant = .ion_rust };
    try ion.writer11.writeSystemMacroInvocationQualifiedMetaByVariant(std.testing.allocator, &out, &meta_args, opts);
    try ion.writer11.writeSystemMacroInvocationQualifiedFlattenByVariant(std.testing.allocator, &out, &seqs, opts);
    try ion.writer11.writeSystemMacroInvocationQualifiedParseIonByVariant(std.testing.allocator, &out, &parse_parts, opts);

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    const expected = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
    };
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 writer11 can emit qualified system set_macros and add_macros directives" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const mkMacroDef = struct {
        fn run(arena_: *ion.value.Arena, name: []const u8, param: ion.value.Element, body: ion.value.Element) ion.IonError!ion.value.Element {
            const name_sym = try ion.value.makeSymbol(arena_, name);
            const head_sym = try ion.value.makeSymbol(arena_, "macro");
            const params_items = arena_.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
            params_items[0] = param;
            const params_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = params_items } };
            const sx_items = arena_.allocator().alloc(ion.value.Element, 4) catch return ion.IonError.OutOfMemory;
            sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = head_sym } };
            sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = name_sym } };
            sx_items[2] = params_elem;
            sx_items[3] = body;
            return .{ .annotations = &.{}, .value = .{ .sexp = sx_items } };
        }
    }.run;

    // Macro body: (% x)
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    // Param: flex_uint::x*
    const param_x_anns = [_]ion.value.Symbol{ion.value.makeSymbolId(null, @as(?[]const u8, "flex_uint"))};
    const param_x: ion.value.Element = .{
        .annotations = @constCast(param_x_anns[0..]),
        .value = .{ .symbol = ion.value.makeSymbolId(null, @as(?[]const u8, "x*")) },
    };

    const def_a = try mkMacroDef(&arena, "a", param_x, body_elem);
    const def_b = try mkMacroDef(&arena, "b", param_x, body_elem);

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    // Set one macro (address 0), then add another (address 1).
    try ion.writer11.writeSystemMacroInvocationQualifiedSetMacrosDirective(std.testing.allocator, &out, &.{def_a}, .{});
    try ion.writer11.writeSystemMacroInvocationQualifiedAddMacrosDirective(std.testing.allocator, &out, &.{def_b}, .{});

    const macro_params = [_]ion.macro.Param{.{ .ty = .flex_uint, .card = .zero_or_many, .name = "x", .shape = null }};
    const arg_vals = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 8 } } },
    };
    const args_by_param = [_][]const ion.value.Element{&arg_vals};

    // Invoke macro at address 1 (the added macro).
    try ion.writer11.writeUserMacroInvocationAtAddressWithParams(std.testing.allocator, &out, 1, macro_params[0..], args_by_param[0..], .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(ion.eq.ionEqElements(elems, &arg_vals));
}

test "ion 1.1 writer11 can emit qualified system make_string and make_symbol e-expressions" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const parts = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .string = "a" } },
        .{ .annotations = &.{}, .value = .{ .string = "b" } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedMakeString(std.testing.allocator, &out, &parts, .{});
    try ion.writer11.writeSystemMacroInvocationQualifiedMakeSymbol(std.testing.allocator, &out, &parts, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 2);
    try std.testing.expect(elems[0].value == .string);
    try std.testing.expectEqualStrings("ab", elems[0].value.string);
    try std.testing.expect(elems[1].value == .symbol);
    try std.testing.expectEqualStrings("ab", elems[1].value.symbol.text.?);
}

test "ion 1.1 writer11 can emit qualified system make_blob e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const parts = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .blob = "a" } },
        .{ .annotations = &.{}, .value = .{ .clob = "b" } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedMakeBlob(std.testing.allocator, &out, &parts, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 1);
    try std.testing.expect(elems[0].value == .blob);
    try std.testing.expectEqualStrings("ab", elems[0].value.blob);
}

test "ion 1.1 writer11 can emit qualified system make_list and make_sexp e-expressions" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const list_items_a = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    list_items_a[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    list_items_a[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    const list_a: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_a } };

    const list_items_b = arena.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
    list_items_b[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };
    const list_b: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_b } };

    const seqs = [_]ion.value.Element{ list_a, list_b };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedMakeList(std.testing.allocator, &out, &seqs, .{});
    try ion.writer11.writeSystemMacroInvocationQualifiedMakeSexp(std.testing.allocator, &out, &seqs, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 2);
    try std.testing.expect(elems[0].value == .list);
    try std.testing.expect(elems[1].value == .sexp);

    const expected_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };

    try std.testing.expect(ion.eq.ionEqElements(elems[0].value.list, &expected_items));
    try std.testing.expect(ion.eq.ionEqElements(elems[1].value.sexp, &expected_items));
}

test "ion 1.1 writer11 can emit qualified system make_struct e-expression" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const a = try ion.value.makeSymbol(&arena, "a");
    const b = try ion.value.makeSymbol(&arena, "b");

    const st_a_fields = arena.allocator().alloc(ion.value.StructField, 1) catch return ion.IonError.OutOfMemory;
    st_a_fields[0] = .{ .name = a, .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } } };
    const st_a: ion.value.Element = .{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = st_a_fields } } };

    const st_b_fields = arena.allocator().alloc(ion.value.StructField, 1) catch return ion.IonError.OutOfMemory;
    st_b_fields[0] = .{ .name = b, .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } } };
    const st_b: ion.value.Element = .{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = st_b_fields } } };

    const structs = [_]ion.value.Element{ st_a, st_b };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedMakeStruct(std.testing.allocator, &out, &structs, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 1);
    try std.testing.expect(elems[0].value == .@"struct");

    const expected_fields = arena.allocator().alloc(ion.value.StructField, 2) catch return ion.IonError.OutOfMemory;
    expected_fields[0] = st_a_fields[0];
    expected_fields[1] = st_b_fields[0];
    const expected_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = expected_fields } } };
    const expected = [_]ion.value.Element{expected_elem};
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 writer11 can emit qualified system parse_ion and make_field e-expressions" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const bytes: ion.value.Element = .{ .annotations = &.{}, .value = .{ .string = "1 2" } };

    const name = try ion.value.makeSymbol(&arena, "a");
    const name_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .symbol = name } };
    const val_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 9 } } };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedParseIon(std.testing.allocator, &out, bytes, .{});
    try ion.writer11.writeSystemMacroInvocationQualifiedMakeField(std.testing.allocator, &out, name_elem, val_elem, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 3);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[1].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), elems[1].value.int.small);
    try std.testing.expect(elems[2].value == .@"struct");
    try std.testing.expect(elems[2].value.@"struct".fields.len == 1);
    try std.testing.expectEqualStrings("a", elems[2].value.@"struct".fields[0].name.text.?);
    try std.testing.expect(elems[2].value.@"struct".fields[0].value.value == .int);
    try std.testing.expectEqual(@as(i128, 9), elems[2].value.@"struct".fields[0].value.value.int.small);
}

test "ion 1.1 writer11 can emit qualified system none and meta e-expressions" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const meta_args = [_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } }};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationQualifiedNone(std.testing.allocator, &out);
    try ion.writer11.writeSystemMacroInvocationQualifiedMeta(std.testing.allocator, &out, &meta_args, .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(elems.len == 0);
}

test "ion 1.1 writer11 can emit length-prefixed user macro with tagless args" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m (flex_uint::x*) (% x))
    // So the invocation expands to the decoded tagless integer values.
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const macro_params = [_]ion.macro.Param{.{ .ty = .flex_uint, .card = .zero_or_many, .name = "x", .shape = null }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    const arg_vals = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };
    const args_by_param = [_][]const ion.value.Element{&arg_vals};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(std.testing.allocator, &out, 1, &macro_params, &args_by_param, .{});

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expect(ion.eq.ionEqElements(elems, &arg_vals));
}

test "ion 1.1 writer11/binary11 support macro_shape args for $ion::flatten" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m (macro_shape::$ion::flatten x) (% x))
    // So the invocation expands to the flattened sequence contents.
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .zero_or_many, .name = "x", .shape = .{ .module = "$ion", .name = "flatten" } }};
    const macro_body = [_]ion.value.Element{body_elem};

    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    const list_items_a = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    list_items_a[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    list_items_a[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    const list_a: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_a } };

    const list_items_b = arena.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
    list_items_b[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };
    const list_b: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items_b } };

    const flatten_args = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    flatten_args[0] = list_a;
    flatten_args[1] = list_b;
    const flatten_arg: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = flatten_args } };

    const args_by_param = [_][]const ion.value.Element{&.{flatten_arg}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        &macro_params,
        &args_by_param,
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    const expected = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 writer11/binary11 support macro_shape args for $ion::repeat and $ion::delta" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const p_repeat = ion.macro.Param{ .ty = .macro_shape, .card = .zero_or_many, .name = "x", .shape = .{ .module = "$ion", .name = "repeat" } };
    const p_delta = ion.macro.Param{ .ty = .macro_shape, .card = .zero_or_many, .name = "x", .shape = .{ .module = "$ion", .name = "delta" } };

    const macro_body = [_]ion.value.Element{body_elem};

    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 3);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "rep", .params = @constCast((&[_]ion.macro.Param{p_repeat})[0..]), .body = &macro_body };
    macro_defs[2] = .{ .name = "del", .params = @constCast((&[_]ion.macro.Param{p_delta})[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    const int3: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };
    const int7: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } };
    const repeat_args = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    repeat_args[0] = int3;
    repeat_args[1] = int7;
    const repeat_arg: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = repeat_args } };

    const deltas = arena.allocator().alloc(ion.value.Element, 3) catch return ion.IonError.OutOfMemory;
    deltas[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    deltas[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    deltas[2] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    const delta_arg: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = deltas } };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        &.{p_repeat},
        &.{&.{repeat_arg}},
        .{ .mactab = &mactab },
    );
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        2,
        &.{p_delta},
        &.{&.{delta_arg}},
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    const expected = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 4 } } },
    };
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 writer11/binary11 support macro_shape args for $ion::default" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const p_default = ion.macro.Param{ .ty = .macro_shape, .card = .zero_or_many, .name = "x", .shape = .{ .module = "$ion", .name = "default" } };
    const macro_body = [_]ion.value.Element{body_elem};

    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast((&[_]ion.macro.Param{p_default})[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    // Encode two default macro-shape args:
    // 1) a = () (empty group), b = (1 2) => default returns b (1 2)
    // 2) a = (9), b = (1 2) => default returns a (9)
    const empty_group: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = &.{} } };

    const b_group_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    b_group_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    b_group_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    const b_group: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = b_group_items } };

    const a_group_items = arena.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
    a_group_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 9 } } };
    const a_group: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = a_group_items } };

    const default1_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    default1_items[0] = empty_group;
    default1_items[1] = b_group;
    const default1: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = default1_items } };

    const default2_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    default2_items[0] = a_group;
    default2_items[1] = b_group;
    const default2: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = default2_items } };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        &.{p_default},
        &.{&.{ default1, default2 }},
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    const expected = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 9 } } },
    };
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 writer11/binary11 support macro_shape args for $ion::none" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const p_none = ion.macro.Param{ .ty = .macro_shape, .card = .zero_or_many, .name = "x", .shape = .{ .module = "$ion", .name = "none" } };
    const macro_body = [_]ion.value.Element{body_elem};

    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast((&[_]ion.macro.Param{p_none})[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    const none_args: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = &.{} } };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        &.{p_none},
        &.{&.{none_args}},
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expect(elems.len == 0);
}

test "ion 1.1 writer11 can emit user macro by name (unqualified + length-prefixed)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 7:
    //   (macro m (flex_uint::x*) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const macro_params = [_]ion.macro.Param{.{ .ty = .flex_uint, .card = .zero_or_many, .name = "x", .shape = null }};
    const macro_body = [_]ion.value.Element{body_elem};

    const macros = try std.testing.allocator.alloc(ion.macro.Macro, 8);
    defer std.testing.allocator.free(macros);
    @memset(macros, .{ .name = null, .params = &.{}, .body = &.{} });
    macros[7] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macros };

    const arg_vals = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 4 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 5 } } },
    };
    const args_by_param = [_][]const ion.value.Element{&arg_vals};

    // Unqualified call by name.
    var out0 = std.ArrayListUnmanaged(u8){};
    defer out0.deinit(std.testing.allocator);
    try out0.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeUserMacroInvocationUnqualifiedByNameWithParams(std.testing.allocator, &out0, &mactab, "m", args_by_param[0..], .{});
    const elems0 = try ion.binary11.parseTopLevelWithMacroTable(&arena, out0.items, &mactab);
    try std.testing.expect(ion.eq.ionEqElements(elems0, &arg_vals));

    // Length-prefixed call by name.
    var out1 = std.ArrayListUnmanaged(u8){};
    defer out1.deinit(std.testing.allocator);
    try out1.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeUserMacroInvocationLengthPrefixedByNameWithParams(std.testing.allocator, &out1, &mactab, "m", args_by_param[0..], .{});
    const elems1 = try ion.binary11.parseTopLevelWithMacroTable(&arena, out1.items, &mactab);
    try std.testing.expect(ion.eq.ionEqElements(elems1, &arg_vals));
}

test "ion 1.1 writer11 can encode macro_shape args (system $ion::make_decimal shape)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::make_decimal::x) (% x))
    // where x is a macro shape argument, encoded in the byte stream as two tagged value
    // expressions (coefficient, exponent) and decoded into a decimal element.
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "make_decimal" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    // Encode x as a sexp containing the macro shape's arguments: (coeff exp)
    const shape_args_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 12 } } };
    shape_args_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = -2 } } };
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);

    // Expected decimal: 12 * 10^-2 = 0.12 (magnitude 12, exponent -2).
    const expected: ion.value.Element = .{
        .annotations = &.{},
        .value = .{
            .decimal = .{
                .is_negative = false,
                .coefficient = .{ .small = 12 },
                .exponent = -2,
            },
        },
    };
    try std.testing.expect(elems.len == 1 and ion.eq.ionEqElements(elems, &.{expected}));
}

test "ion 1.1 writer11 can encode macro_shape args (system $ion::sum shape)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::sum::x) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "sum" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    const shape_args_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 10 } } };
    shape_args_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 32 } } };
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expectEqual(@as(i128, 42), elems[0].value.int.small);
}

test "ion 1.1 writer11 can encode macro_shape args (system $ion::parse_ion shape)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::parse_ion::x) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "parse_ion" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    // Encode x as a sexp containing the macro shape's single argument: the bytes to parse.
    const shape_args_items = arena.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = .{ .annotations = &.{}, .value = .{ .string = "1" } };
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
}

test "ion 1.1 binary11 macro_shape parse_ion is independent of ion-rust addr-16 overload inference" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::parse_ion::x) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "parse_ion" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    // Force ion-rust macro address layout inference via `$ion::(module ...)` with head SID 16.
    const anns = arena.allocator().alloc(ion.value.Symbol, 1) catch return ion.IonError.OutOfMemory;
    anns[0] = ion.value.makeSymbolId(1, null); // $ion

    const module_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    module_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(16, null) } };
    module_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "_") } };
    const module_directive: ion.value.Element = .{ .annotations = anns, .value = .{ .sexp = module_items } };

    const prefix = try ion.writer11.writeBinary11(std.testing.allocator, &.{module_directive});
    defer std.testing.allocator.free(prefix);

    // Encode x as a sexp containing the macro shape's single argument: the bytes to parse.
    const shape_args_items = arena.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = .{ .annotations = &.{}, .value = .{ .string = "1" } };
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, prefix);
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
}

test "ion 1.1 writer11 can encode macro_shape args ($ion::values yields multiple)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::values::x*) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "values" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .zero_or_many, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    // Encode x as a sexp containing the macro shape's arguments: (1 2 3)
    const shape_args_items = arena.allocator().alloc(ion.value.Element, 3) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    shape_args_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    shape_args_items[2] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    const expected = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };
    try std.testing.expect(ion.eq.ionEqElements(elems, &expected));
}

test "ion 1.1 writer11 can encode nested macro_shape args (user shape contains macro_shape)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");

    // Macro at address 2:
    //   (macro inner ($ion::make_decimal::d) (% d))
    const body_sym_d = try ion.value.makeSymbol(&arena, "d");
    const inner_body_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    inner_body_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    inner_body_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_d } };
    const inner_body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = inner_body_items } };

    const shape_decimal: ion.macro.MacroShape = .{ .module = "$ion", .name = "make_decimal" };
    const inner_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "d", .shape = shape_decimal }};
    const inner_body = [_]ion.value.Element{inner_body_elem};

    // Macro at address 1:
    //   (macro outer (inner::x) (% x))
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const outer_body_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    outer_body_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    outer_body_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const outer_body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = outer_body_items } };

    const shape_inner: ion.macro.MacroShape = .{ .module = null, .name = "inner" };
    const outer_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape_inner }};
    const outer_body = [_]ion.value.Element{outer_body_elem};

    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 3);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "outer", .params = @constCast(outer_params[0..]), .body = &outer_body };
    macro_defs[2] = .{ .name = "inner", .params = @constCast(inner_params[0..]), .body = &inner_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    // Encode x as a sexp containing the shape "inner"'s argument list, which is (d).
    // That argument d is itself a macro shape `$ion::make_decimal`, encoded by passing a sexp
    // containing (coeff exp).
    const decimal_args_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    decimal_args_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 12 } } };
    decimal_args_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = -2 } } };
    const decimal_args_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = decimal_args_items } };

    const inner_args_items = arena.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
    inner_args_items[0] = decimal_args_elem;
    const inner_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = inner_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{inner_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        outer_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);

    const expected: ion.value.Element = .{
        .annotations = &.{},
        .value = .{
            .decimal = .{
                .is_negative = false,
                .coefficient = .{ .small = 12 },
                .exponent = -2,
            },
        },
    };
    try std.testing.expect(elems.len == 1 and ion.eq.ionEqElements(elems, &.{expected}));
}

test "ion 1.1 text macro_shape supports $ion::values (multi-value binding)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::values::x*) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape_values: ion.macro.MacroShape = .{ .module = "$ion", .name = "values" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .zero_or_many, .name = "x", .shape = shape_values }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    const got = try ion.text.parseTopLevelWithMacroTable(&arena, "$ion_1_1 (:1 (1 2 3))", &mactab);
    const expected = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };
    try std.testing.expect(ion.eq.ionEqElements(got, &expected));
}

test "ion 1.1 text macro_shape supports $ion::make_string" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::make_string::x) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "make_string" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    const got = try ion.text.parseTopLevelWithMacroTable(&arena, "$ion_1_1 (:1 (\"hi\" \"there\"))", &mactab);
    try std.testing.expectEqual(@as(usize, 1), got.len);
    try std.testing.expect(got[0].value == .string);
    try std.testing.expectEqualStrings("hithere", got[0].value.string);
}

test "ion 1.1 writer11 can encode macro_shape args (system $ion::make_string shape)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::make_string::x) (% x))
    // where x is a macro shape argument encoded using the system `make_string` payload encoding.
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "make_string" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    // Encode x as a sexp containing the macro shape's arguments: ("hi" "there")
    const shape_args_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = .{ .annotations = &.{}, .value = .{ .string = "hi" } };
    shape_args_items[1] = .{ .annotations = &.{}, .value = .{ .string = "there" } };
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expect(elems.len == 1);
    try std.testing.expect(elems[0].value == .string);
    try std.testing.expectEqualStrings("hithere", elems[0].value.string);
}

test "ion 1.1 writer11 can encode macro_shape args (system $ion::make_timestamp shape)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::make_timestamp::x) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "make_timestamp" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    // Encode x as a sexp containing the macro shape's arguments:
    // (year month day hour minute seconds offset)
    const shape_args_items = arena.allocator().alloc(ion.value.Element, 7) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2025 } } };
    shape_args_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 12 } } };
    shape_args_items[2] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 26 } } };
    shape_args_items[3] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    shape_args_items[4] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    shape_args_items[5] = .{ .annotations = &.{}, .value = .{ .decimal = .{ .is_negative = false, .coefficient = .{ .small = 345 }, .exponent = -2 } } };
    shape_args_items[6] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 0 } } };
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expect(elems.len == 1);
    try std.testing.expect(elems[0].value == .timestamp);
    const ts = elems[0].value.timestamp;
    try std.testing.expectEqual(@as(i32, 2025), ts.year);
    try std.testing.expectEqual(@as(?u8, 12), ts.month);
    try std.testing.expectEqual(@as(?u8, 26), ts.day);
    try std.testing.expectEqual(@as(?u8, 1), ts.hour);
    try std.testing.expectEqual(@as(?u8, 2), ts.minute);
    try std.testing.expectEqual(@as(?u8, 3), ts.second);
    try std.testing.expect(ts.fractional != null);
    try std.testing.expectEqual(@as(i32, -2), ts.fractional.?.exponent);
    try std.testing.expectEqual(@as(i128, 45), ts.fractional.?.coefficient.small);
    try std.testing.expectEqual(@as(?i16, 0), ts.offset_minutes);
}

test "ion 1.1 writer11 can encode macro_shape args (system $ion::make_list shape)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::make_list::x) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "make_list" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    // Encode x as a sexp containing the macro shape's arguments: ([1,2] (3 4))
    const list_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    list_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    list_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    const list_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items } };

    const sexp_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    sexp_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };
    sexp_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 4 } } };
    const sexp_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = sexp_items } };

    const shape_args_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = list_elem;
    shape_args_items[1] = sexp_elem;
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expect(elems.len == 1);
    try std.testing.expect(elems[0].value == .list);
    const got = elems[0].value.list;
    try std.testing.expectEqual(@as(usize, 4), got.len);
    try std.testing.expectEqual(@as(i128, 1), got[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), got[1].value.int.small);
    try std.testing.expectEqual(@as(i128, 3), got[2].value.int.small);
    try std.testing.expectEqual(@as(i128, 4), got[3].value.int.small);
}

test "ion 1.1 writer11 can encode macro_shape args (system $ion::annotate shape)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::annotate::x) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "annotate" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    // Encode x as a sexp containing the macro shape's arguments: ("a" "b" 1)
    const shape_args_items = arena.allocator().alloc(ion.value.Element, 3) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = .{ .annotations = &.{}, .value = .{ .string = "a" } };
    shape_args_items[1] = .{ .annotations = &.{}, .value = .{ .string = "b" } };
    shape_args_items[2] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expect(elems.len == 1);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
    try std.testing.expectEqual(@as(usize, 2), elems[0].annotations.len);
    try std.testing.expectEqualStrings("a", elems[0].annotations[0].text orelse return error.TestExpectedEqual);
    try std.testing.expectEqualStrings("b", elems[0].annotations[1].text orelse return error.TestExpectedEqual);
}

test "ion 1.1 writer11 can encode macro_shape args (system $ion::make_field shape)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::make_field::x) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "make_field" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    const field_sym = try ion.value.makeSymbol(&arena, "f");

    // Encode x as a sexp containing the macro shape's arguments: (f 7)
    const shape_args_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = field_sym } };
    shape_args_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } };
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .@"struct");
    const st = elems[0].value.@"struct";
    try std.testing.expectEqual(@as(usize, 1), st.fields.len);
    try std.testing.expectEqualStrings("f", st.fields[0].name.text orelse return error.TestExpectedEqual);
    try std.testing.expect(st.fields[0].value.value == .int);
    try std.testing.expectEqual(@as(i128, 7), st.fields[0].value.value.int.small);
}

test "ion 1.1 writer11 can encode macro_shape args (system $ion::make_struct shape)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::make_struct::x) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "make_struct" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    const f_a = try ion.value.makeSymbol(&arena, "a");
    const f_b = try ion.value.makeSymbol(&arena, "b");

    const fields_a = arena.allocator().alloc(ion.value.StructField, 1) catch return ion.IonError.OutOfMemory;
    fields_a[0] = .{ .name = f_a, .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } } };
    const st_a: ion.value.Element = .{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = fields_a } } };

    const fields_b = arena.allocator().alloc(ion.value.StructField, 1) catch return ion.IonError.OutOfMemory;
    fields_b[0] = .{ .name = f_b, .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } } };
    const st_b: ion.value.Element = .{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = fields_b } } };

    // Encode x as a sexp containing the macro shape's arguments: ({a:1} {b:2})
    const shape_args_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = st_a;
    shape_args_items[1] = st_b;
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .@"struct");
    const out_st = elems[0].value.@"struct";
    try std.testing.expectEqual(@as(usize, 2), out_st.fields.len);
    try std.testing.expectEqualStrings("a", out_st.fields[0].name.text orelse return error.TestExpectedEqual);
    try std.testing.expectEqualStrings("b", out_st.fields[1].name.text orelse return error.TestExpectedEqual);
}

test "ion 1.1 writer11 can encode macro_shape args (system $ion::make_sexp shape)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m ($ion::make_sexp::x) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const shape: ion.macro.MacroShape = .{ .module = "$ion", .name = "make_sexp" };
    const macro_params = [_]ion.macro.Param{.{ .ty = .macro_shape, .card = .one, .name = "x", .shape = shape }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    // Encode x as a sexp containing the macro shape's arguments: ([1,2] (3 4))
    const list_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    list_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    list_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };
    const list_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items } };

    const sexp_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    sexp_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } };
    sexp_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 4 } } };
    const sexp_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = sexp_items } };

    const shape_args_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    shape_args_items[0] = list_elem;
    shape_args_items[1] = sexp_elem;
    const shape_arg_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = shape_args_items } };
    const args_by_param = [_][]const ion.value.Element{&.{shape_arg_elem}};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{ .mactab = &mactab },
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expect(elems.len == 1);
    try std.testing.expect(elems[0].value == .sexp);
    const got = elems[0].value.sexp;
    try std.testing.expectEqual(@as(usize, 4), got.len);
    try std.testing.expectEqual(@as(i128, 1), got[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), got[1].value.int.small);
    try std.testing.expectEqual(@as(i128, 3), got[2].value.int.small);
    try std.testing.expectEqual(@as(i128, 4), got[3].value.int.small);
}

test "ion 1.1 writer11 can emit unqualified user macro invocation (non-length-prefixed)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro at address 1:
    //   (macro m (flex_uint::x*) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const macro_params = [_]ion.macro.Param{.{ .ty = .flex_uint, .card = .zero_or_many, .name = "x", .shape = null }};
    const macro_body = [_]ion.value.Element{body_elem};
    const macro_defs = try std.testing.allocator.alloc(ion.macro.Macro, 2);
    defer std.testing.allocator.free(macro_defs);
    macro_defs[0] = .{ .name = null, .params = &.{}, .body = &.{} };
    macro_defs[1] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macro_defs };

    const arg_vals = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 9 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 10 } } },
    };
    const args_by_param = [_][]const ion.value.Element{&arg_vals};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeUserMacroInvocationAtAddressWithParams(
        std.testing.allocator,
        &out,
        1,
        macro_params[0..],
        args_by_param[0..],
        .{},
    );

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expect(ion.eq.ionEqElements(elems, &arg_vals));
}

test "ion 1.1 writer11 can emit add_symbols and use directives" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    try ion.writer11.writeAddSymbolsDirectiveText(std.testing.allocator, &out, &.{ "x", "y" });
    try ion.writer11.writeUseDirective(std.testing.allocator, &out, "abcs", 2);

    const res = try ion.binary11.parseTopLevelWithState(&arena, out.items);
    try std.testing.expect(res.elements.len == 0);
    try std.testing.expect(res.state.user_symbols.len == 4);
    try std.testing.expectEqualStrings("x", res.state.user_symbols[0].?);
    try std.testing.expectEqualStrings("y", res.state.user_symbols[1].?);
    try std.testing.expectEqualStrings("a", res.state.user_symbols[2].?);
    try std.testing.expectEqualStrings("b", res.state.user_symbols[3].?);
}

test "ion 1.1 writer11 can emit set_macros and add_macros directives" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Macro def helper to build: (macro <name> (<params...>) <body>)
    const mkMacroDef = struct {
        fn run(arena_: *ion.value.Arena, name: []const u8, param: ion.value.Element, body: ion.value.Element) ion.IonError!ion.value.Element {
            const name_sym = try ion.value.makeSymbol(arena_, name);
            const head_sym = try ion.value.makeSymbol(arena_, "macro");
            const params_items = arena_.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
            params_items[0] = param;
            const params_sx: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = params_items } };

            const items = arena_.allocator().alloc(ion.value.Element, 4) catch return ion.IonError.OutOfMemory;
            items[0] = .{ .annotations = &.{}, .value = .{ .symbol = head_sym } };
            items[1] = .{ .annotations = &.{}, .value = .{ .symbol = name_sym } };
            items[2] = params_sx;
            items[3] = body;
            return .{ .annotations = &.{}, .value = .{ .sexp = items } };
        }
    }.run;

    // Build body: (% x)
    const percent_sym = try ion.value.makeSymbol(&arena, "%");
    const x_sym = try ion.value.makeSymbol(&arena, "x");
    const body_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = percent_sym } };
    body_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = x_sym } };
    const body_expr: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_items } };

    // Param: flex_uint::x*
    const param_x_anns = [_]ion.value.Symbol{ion.value.makeSymbolId(null, @as(?[]const u8, "flex_uint"))};
    const param_x: ion.value.Element = .{
        .annotations = @constCast(param_x_anns[0..]),
        .value = .{ .symbol = ion.value.makeSymbolId(null, @as(?[]const u8, "x*")) },
    };

    const def_a = try mkMacroDef(&arena, "a", param_x, body_expr);
    const def_b = try mkMacroDef(&arena, "b", param_x, body_expr);

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });

    // Set macros (one macro => address 0), then add another (address 1).
    try ion.writer11.writeSetMacrosDirective(std.testing.allocator, &out, &.{def_a});
    try ion.writer11.writeAddMacrosDirective(std.testing.allocator, &out, &.{def_b});

    const macro_params = [_]ion.macro.Param{.{ .ty = .flex_uint, .card = .zero_or_many, .name = "x", .shape = null }};
    const arg_vals = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 8 } } },
    };
    const args_by_param = [_][]const ion.value.Element{&arg_vals};

    // Invoke macro at address 1 (the added macro).
    try ion.writer11.writeUserMacroInvocationAtAddressWithParams(std.testing.allocator, &out, 1, macro_params[0..], args_by_param[0..], .{});

    const elems = try ion.binary11.parseTopLevel(&arena, out.items);
    try std.testing.expect(ion.eq.ionEqElements(elems, &arg_vals));
}

test "ion 1.1 writer11 can emit 12-bit unqualified macro address" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const addr: usize = 100; // triggers 12-bit address encoding

    // Macro at address `addr`: (macro m (flex_uint::x*) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const macro_params = [_]ion.macro.Param{.{ .ty = .flex_uint, .card = .zero_or_many, .name = "x", .shape = null }};
    const macro_body = [_]ion.value.Element{body_elem};

    const macros = try std.testing.allocator.alloc(ion.macro.Macro, addr + 1);
    defer std.testing.allocator.free(macros);
    @memset(macros, .{ .name = null, .params = &.{}, .body = &.{} });
    macros[addr] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macros };

    const arg_vals = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };
    const args_by_param = [_][]const ion.value.Element{&arg_vals};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeUserMacroInvocationAtAddressWithParams(std.testing.allocator, &out, addr, macro_params[0..], args_by_param[0..], .{});

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expect(ion.eq.ionEqElements(elems, &arg_vals));
}

test "ion 1.1 writer11 can emit 20-bit unqualified macro address" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const addr: usize = 5000; // triggers 20-bit address encoding

    // Macro at address `addr`: (macro m (flex_uint::x*) (% x))
    const body_sym_percent = try ion.value.makeSymbol(&arena, "%");
    const body_sym_x = try ion.value.makeSymbol(&arena, "x");
    const body_sx_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    body_sx_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_percent } };
    body_sx_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = body_sym_x } };
    const body_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .sexp = body_sx_items } };

    const macro_params = [_]ion.macro.Param{.{ .ty = .flex_uint, .card = .zero_or_many, .name = "x", .shape = null }};
    const macro_body = [_]ion.value.Element{body_elem};

    const macros = try std.testing.allocator.alloc(ion.macro.Macro, addr + 1);
    defer std.testing.allocator.free(macros);
    @memset(macros, .{ .name = null, .params = &.{}, .body = &.{} });
    macros[addr] = .{ .name = "m", .params = @constCast(macro_params[0..]), .body = &macro_body };
    const mactab: ion.macro.MacroTable = .{ .macros = macros };

    const arg_vals = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 9 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 10 } } },
    };
    const args_by_param = [_][]const ion.value.Element{&arg_vals};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeUserMacroInvocationAtAddressWithParams(std.testing.allocator, &out, addr, macro_params[0..], args_by_param[0..], .{});

    const elems = try ion.binary11.parseTopLevelWithMacroTable(&arena, out.items, &mactab);
    try std.testing.expect(ion.eq.ionEqElements(elems, &arg_vals));
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
        &.{".ion"},
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
        &.{".ion"},
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
        &.{".ion"},
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
        &.{".ion"},
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

test "ion-tests 1_1 good roundtrip (lines -> binary_1_1 -> lines)" {
    const allocator = std.testing.allocator;
    const skip = try concatSkipLists(allocator, &.{ &global_skip_list, &round_trip_skip_list });
    defer allocator.free(skip);

    try walkAndTest(
        allocator,
        "ion-tests/iontestdata_1_1/good",
        &.{".ion"},
        skip,
        struct {
            fn run(path: []const u8, data: []const u8) !void {
                roundtripEq(std.testing.allocator, data, .binary_1_1, .text_lines) catch |e| {
                    std.debug.print("roundtrip failed: {s} (formats lines->binary_1_1->lines): {s}\n", .{ path, @errorName(e) });
                    return e;
                };
            }
        }.run,
    );
}

test "ion-tests conformance suite (partial)" {
    const allocator = std.testing.allocator;
    var stats: conformance.Stats = .{};
    var cat = try conformance_catalog.loadIonTestsCatalog(std.testing.allocator, "ion-tests/catalog/catalog.ion");
    defer cat.deinit();

    const Runner = struct {
        var stats_ptr: *conformance.Stats = undefined;
        var cat_ptr: *const conformance_catalog.Catalog = undefined;
        fn run(path: []const u8, data: []const u8) !void {
            conformance.runConformanceFileWithCatalog(std.testing.allocator, data, stats_ptr, cat_ptr) catch |e| {
                std.debug.print("conformance failed: {s}: {s}\n", .{ path, @errorName(e) });
                return e;
            };
        }
    };
    Runner.stats_ptr = &stats;
    Runner.cat_ptr = &cat;

    try walkAndTest(
        allocator,
        "ion-tests/conformance",
        &.{".ion"},
        &.{},
        Runner.run,
    );

    try std.testing.expect(stats.passed + stats.skipped == stats.branches);
}

test "ion-tests catalog parses (shared symbol tables)" {
    var cat = try conformance_catalog.loadIonTestsCatalog(std.testing.allocator, "ion-tests/catalog/catalog.ion");
    defer cat.deinit();

    const empty = cat.lookupSharedSymtab("empty", 1) orelse return error.TestExpectedEqual;
    try std.testing.expectEqual(@as(usize, 0), empty.symbols.len);

    const abcs1 = cat.lookupSharedSymtab("abcs", 1) orelse return error.TestExpectedEqual;
    try std.testing.expectEqual(@as(usize, 1), abcs1.symbols.len);
    try std.testing.expect(abcs1.symbols[0] != null);
    try std.testing.expectEqualStrings("a", abcs1.symbols[0].?);

    const abcs2 = cat.lookupSharedSymtab("abcs", 2) orelse return error.TestExpectedEqual;
    try std.testing.expectEqual(@as(usize, 2), abcs2.symbols.len);
    try std.testing.expectEqualStrings("a", abcs2.symbols[0].?);
    try std.testing.expectEqualStrings("b", abcs2.symbols[1].?);

    const mnop1 = cat.lookupSharedSymtab("mnop", 1) orelse return error.TestExpectedEqual;
    try std.testing.expectEqual(@as(usize, 1), mnop1.symbols.len);
    try std.testing.expectEqualStrings("m", mnop1.symbols[0].?);

    const mnop3 = cat.lookupSharedSymtab("mnop", 3) orelse return error.TestExpectedEqual;
    try std.testing.expectEqual(@as(usize, 3), mnop3.symbols.len);
    try std.testing.expectEqualStrings("m", mnop3.symbols[0].?);
    try std.testing.expectEqualStrings("n", mnop3.symbols[1].?);
    try std.testing.expectEqualStrings("o", mnop3.symbols[2].?);

    const mnop4 = cat.lookupSharedSymtab("mnop", 4) orelse return error.TestExpectedEqual;
    try std.testing.expectEqual(@as(usize, 4), mnop4.symbols.len);
    try std.testing.expect(mnop4.symbols[0] == null);
    try std.testing.expectEqualStrings("n", mnop4.symbols[1].?);
    try std.testing.expectEqualStrings("o", mnop4.symbols[2].?);
    try std.testing.expectEqualStrings("p", mnop4.symbols[3].?);
}

fn roundtripEq(allocator: std.mem.Allocator, data: []const u8, format1: ion.Format, format2: ion.Format) !void {
    var src = try ion.parseDocument(allocator, data);
    defer src.deinit();

    const b1 = try ion.serializeDocument(allocator, format1, src.elements);
    defer allocator.free(b1);
    var d1 = try parseDocumentForRoundtrip(allocator, b1);
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

fn parseDocumentForRoundtrip(allocator: std.mem.Allocator, bytes: []const u8) !ion.Document {
    // `serializeDocument(.binary_1_1, ...)` currently emits a self-contained Ion 1.1 binary stream
    // with a minimal `$ion::(module ...)` prelude. `binary11` tracks that module state separately
    // and requires an explicit resolver pass to materialize symbol texts.
    //
    // We keep the core parser behavior (conformance-driven) unchanged, and only apply the resolver
    // here so roundtrip tests validate byte<->DOM<->text parity.
    if (bytes.len >= 4 and bytes[0] == 0xE0 and bytes[1] == 0x01 and bytes[2] == 0x01 and bytes[3] == 0xEA) {
        var arena = try ion.value.Arena.init(allocator);
        errdefer arena.deinit();

        const res = try ion.binary11.parseTopLevelWithState(&arena, bytes);
        try ion.value.resolveDefaultModuleSymbols11(&arena, res.elements, res.state.user_symbols, res.state.system_loaded);
        return .{ .arena = arena, .elements = res.elements };
    }

    return ion.parseDocument(allocator, bytes);
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
        0xF9, 0x0B, 'h',  'e',
        'l',  'l',  'o',  0xFA,
        0x07, 'f',  'o',  'o',
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
        0xF7, 0x23, 0x00, 0x00,
        0x01, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00,
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
        0xFD,
        'h',
        'i',
        0xFD,
        'y',
        'o',
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
        0xF5, 0x81, 0x17, 0x21,
        0x01, 0x61, 0x01, 0x09,
        0x61, 0x02, 0x61, 0x03,
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
        0xF5, 0x17, 0x29, 0xF6,
        0x23, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
        0x00, 0x01, 0x60,
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

test "ion 1.1 binary e-expression length-prefixed system sum supports big ints" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Build a length-prefixed invocation:
    //   F5 <addr=7> <args_len> <int(2^200)> <int(1)>
    // where the large int is encoded as a long int (F6) with a 26-byte LE payload.
    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);

    var args = std.ArrayListUnmanaged(u8){};
    defer args.deinit(std.testing.allocator);

    // int(2^200)
    try args.appendSlice(std.testing.allocator, &.{ 0xF6, 0x35 });
    var pow2_200 = [_]u8{0} ** 26;
    pow2_200[25] = 0x01;
    try args.appendSlice(std.testing.allocator, &pow2_200);
    // int(1)
    try args.appendSlice(std.testing.allocator, &.{ 0x61, 0x01 });

    try bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xF5 });
    try appendFlexUIntShift1(std.testing.allocator, &bytes, 7);
    try appendFlexUIntShift1(std.testing.allocator, &bytes, args.items.len);
    try bytes.appendSlice(std.testing.allocator, args.items);

    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[0].value.int == .big);
    const bi = elems[0].value.int.big;
    try std.testing.expect(bi.toConst().positive);
    try std.testing.expectEqual(@as(usize, 201), bi.toConst().bitCountAbs());
}

test "ion 1.1 binary e-expression length-prefixed system delta supports big ints" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Build a length-prefixed invocation:
    //   F5 <addr=6> <args_len> <bitmap=10> <group len> <int(2^200)> <int(1)>
    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);

    var group = std.ArrayListUnmanaged(u8){};
    defer group.deinit(std.testing.allocator);
    try group.appendSlice(std.testing.allocator, &.{ 0xF6, 0x35 });
    var pow2_200 = [_]u8{0} ** 26;
    pow2_200[25] = 0x01;
    try group.appendSlice(std.testing.allocator, &pow2_200);
    try group.appendSlice(std.testing.allocator, &.{ 0x61, 0x01 });

    var args = std.ArrayListUnmanaged(u8){};
    defer args.deinit(std.testing.allocator);
    // Bitmap for a single variadic param: 10 (arg group).
    try args.append(std.testing.allocator, 0x02);
    try appendFlexUIntShift1(std.testing.allocator, &args, group.items.len);
    try args.appendSlice(std.testing.allocator, group.items);

    try bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xF5 });
    try appendFlexUIntShift1(std.testing.allocator, &bytes, 6);
    try appendFlexUIntShift1(std.testing.allocator, &bytes, args.items.len);
    try bytes.appendSlice(std.testing.allocator, args.items);

    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);
    try std.testing.expectEqual(@as(usize, 2), elems.len);

    for (elems) |e| {
        try std.testing.expect(e.value == .int);
        try std.testing.expect(e.value.int == .big);
        try std.testing.expect(e.value.int.big.toConst().positive);
    }

    var buf0: [26]u8 = undefined;
    var buf1: [26]u8 = undefined;
    @memset(&buf0, 0);
    @memset(&buf1, 0);
    elems[0].value.int.big.toConst().writeTwosComplement(&buf0, .big);
    elems[1].value.int.big.toConst().writeTwosComplement(&buf1, .big);

    var expected0_buf = [_]u8{0} ** 26;
    expected0_buf[0] = 0x01;
    var expected1_buf = [_]u8{0} ** 26;
    expected1_buf[0] = 0x01;
    expected1_buf[25] = 0x01;

    try std.testing.expectEqualSlices(u8, &expected0_buf, &buf0);
    try std.testing.expectEqualSlices(u8, &expected1_buf, &buf1);
}

test "ion 1.1 binary e-expression length-prefixed system make_timestamp supports big decimal seconds coefficient" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Build a decimal seconds value with a huge coefficient:
    // exponent = -50, coefficient = 3*10^50 + 1 => seconds=3, fractional=1d-50.
    const ten = try arena.makeBigInt();
    ten.set(@as(u8, 10)) catch return error.OutOfMemory;
    const pow10 = try arena.makeBigInt();
    pow10.pow(ten, 50) catch return error.OutOfMemory;
    const three = try arena.makeBigInt();
    three.set(@as(u8, 3)) catch return error.OutOfMemory;
    const scaled = try arena.makeBigInt();
    scaled.mul(three, pow10) catch return error.OutOfMemory;
    scaled.addScalar(scaled, 1) catch return error.OutOfMemory;

    const sec_decimal: ion.value.Decimal = .{
        .is_negative = false,
        .coefficient = .{ .big = scaled },
        .exponent = -50,
    };

    // Use writer11 to get the Ion 1.1 binary encoding of this decimal, then embed it as the
    // `seconds` argument to a length-prefixed `make_timestamp` invocation.
    const decimal_doc = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .decimal = sec_decimal } }};
    const decimal_bytes = try ion.writer11.writeBinary11(std.testing.allocator, decimal_doc);
    defer std.testing.allocator.free(decimal_bytes);
    const seconds_value_bytes = decimal_bytes[4..];

    // make_timestamp(year=2025, month=12, day=24, hour=1, minute=2, seconds=<big decimal>, offset absent)
    //
    // Variadic params (month/day/hour/minute/seconds/offset) are bitmap-encoded first. Here:
    // month/day/hour/minute/seconds present (01), offset absent (00) => bytes { 0x55, 0x01 }.
    var args = std.ArrayListUnmanaged(u8){};
    defer args.deinit(std.testing.allocator);
    try args.appendSlice(std.testing.allocator, &.{ 0x55, 0x01 });
    // year=2025 (int len=2, LE 0x07E9)
    try args.appendSlice(std.testing.allocator, &.{ 0x62, 0xE9, 0x07 });
    // month/day/hour/minute
    try args.appendSlice(std.testing.allocator, &.{ 0x61, 0x0C, 0x61, 0x18, 0x61, 0x01, 0x61, 0x02 });
    // seconds decimal
    try args.appendSlice(std.testing.allocator, seconds_value_bytes);

    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);
    try bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xF5 });
    try appendFlexUIntShift1(std.testing.allocator, &bytes, 12);
    try appendFlexUIntShift1(std.testing.allocator, &bytes, args.items.len);
    try bytes.appendSlice(std.testing.allocator, args.items);

    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .timestamp);
    const ts = elems[0].value.timestamp;
    try std.testing.expectEqual(@as(u8, 3), ts.second.?);
    try std.testing.expect(ts.precision == .fractional);
    try std.testing.expect(ts.fractional != null);
    const frac = ts.fractional.?;
    try std.testing.expectEqual(@as(i32, -50), frac.exponent);
    try std.testing.expect(!frac.is_negative);
    try std.testing.expect(frac.coefficient == .small);
    try std.testing.expectEqual(@as(i128, 1), frac.coefficient.small);
}

test "ion 1.1 binary set_symbols affects symbol ID text (experimental)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // IVM + `(:$ion::set_symbols "foo")` + symbol(SID=1)
    // EF 13 => system macro address 19 (set_symbols/flatten)
    // 01    => presence: one tagged value
    // 93 'foo' => short string len=3
    // E1 01 => symbol address (len=1), SID=1
    const bytes = &[_]u8{
        0xE0, 0x01, 0x01, 0xEA,
        0xEF, 0x13, 0x01, 0x93,
        0x66, 0x6F, 0x6F, 0xE1,
        0x01,
    };

    const res = try ion.binary11.parseTopLevelWithState(&arena, bytes);
    const elems = res.elements;
    try ion.value.resolveDefaultModuleSymbols11(&arena, elems, res.state.user_symbols, res.state.system_loaded);

    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .symbol);
    try std.testing.expectEqual(@as(?u32, 1), elems[0].value.symbol.sid);
    try std.testing.expect(elems[0].value.symbol.text != null);
    try std.testing.expectEqualStrings("foo", elems[0].value.symbol.text.?);
}

test "ion 1.1 binary set_macros updates macro table (experimental)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const sym_macro = try ion.value.makeSymbol(&arena, "macro");
    const sym_foo = try ion.value.makeSymbol(&arena, "foo");
    const sym_x = try ion.value.makeSymbol(&arena, "x");
    const sym_percent = try ion.value.makeSymbol(&arena, "%");

    // (macro foo (x) (% x))
    const params_items = try arena.allocator().alloc(ion.value.Element, 1);
    params_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = sym_x } };
    const params = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = params_items } };

    const body_items = try arena.allocator().alloc(ion.value.Element, 2);
    body_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = sym_percent } };
    body_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = sym_x } };
    const body = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = body_items } };

    const def_items = try arena.allocator().alloc(ion.value.Element, 4);
    def_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = sym_macro } };
    def_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = sym_foo } };
    def_items[2] = params;
    def_items[3] = body;
    const macro_def = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = def_items } };

    const macro_doc_bytes = try ion.writer11.writeBinary11(std.testing.allocator, &.{macro_def});
    defer std.testing.allocator.free(macro_doc_bytes);
    const macro_value_bytes = macro_doc_bytes[4..];

    // IVM + `(:$ion::set_macros <macro_def>)` + user macro invocation at address 0 with arg 7
    // EF 15 => system macro address 21 (meta/set_macros)
    // 01    => presence: one tagged value (the macro def)
    // 00    => user macro address 0
    // 61 07 => int(7)
    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);
    try bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xEF, 0x15, 0x01 });
    try bytes.appendSlice(std.testing.allocator, macro_value_bytes);
    try bytes.appendSlice(std.testing.allocator, &.{ 0x00, 0x61, 0x07 });

    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[0].value.int == .small);
    try std.testing.expectEqual(@as(i128, 7), elems[0].value.int.small);
}

test "ion 1.1 binary set_macros supports literal macro bodies (experimental)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const sym_macro = try ion.value.makeSymbol(&arena, "macro");
    const sym_foo = try ion.value.makeSymbol(&arena, "foo");
    const sym_x = try ion.value.makeSymbol(&arena, "x");

    // (macro foo (x) 1)
    const params_items = try arena.allocator().alloc(ion.value.Element, 1);
    params_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = sym_x } };
    const params = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = params_items } };

    const def_items = try arena.allocator().alloc(ion.value.Element, 4);
    def_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = sym_macro } };
    def_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = sym_foo } };
    def_items[2] = params;
    def_items[3] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    const macro_def = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = def_items } };

    const macro_doc_bytes = try ion.writer11.writeBinary11(std.testing.allocator, &.{macro_def});
    defer std.testing.allocator.free(macro_doc_bytes);
    const macro_value_bytes = macro_doc_bytes[4..];

    // IVM + `(:$ion::set_macros <macro_def>)` + user macro invocation at address 0 with arg 7
    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);
    try bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xEF, 0x15, 0x01 });
    try bytes.appendSlice(std.testing.allocator, macro_value_bytes);
    try bytes.appendSlice(std.testing.allocator, &.{ 0x00, 0x61, 0x07 });

    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[0].value.int == .small);
    try std.testing.expectEqual(@as(i128, 1), elems[0].value.int.small);
}

test "ion 1.1 binary use affects symbol ID text (experimental)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // IVM + `(:$ion::use "abcs" 1)` + symbol(SID=1) + symbol(SID=2)
    // EF 17 => system macro address 23 (use)
    // 01    => presence: tagged version
    // 94 'abcs' => short string len=4
    // 61 01 => int(1)
    // E1 01 => symbol address (len=1), SID=1 (imported symbol "a")
    // E1 02 => symbol address (len=1), SID=2 (system symbol "$ion")
    const bytes = &[_]u8{
        0xE0, 0x01, 0x01, 0xEA,
        0xEF, 0x17, 0x01, 0x94,
        0x61, 0x62, 0x63, 0x73,
        0x61, 0x01, 0xE1, 0x01,
        0xE1, 0x02,
    };

    const res = try ion.binary11.parseTopLevelWithState(&arena, bytes);
    const elems = res.elements;
    try ion.value.resolveDefaultModuleSymbols11(&arena, elems, res.state.user_symbols, res.state.system_loaded);

    try std.testing.expectEqual(@as(usize, 2), elems.len);
    try std.testing.expect(elems[0].value == .symbol);
    try std.testing.expectEqual(@as(?u32, 1), elems[0].value.symbol.sid);
    try std.testing.expectEqualStrings("a", elems[0].value.symbol.text.?);

    try std.testing.expect(elems[1].value == .symbol);
    try std.testing.expectEqual(@as(?u32, 2), elems[1].value.symbol.sid);
    try std.testing.expectEqualStrings("$ion", elems[1].value.symbol.text.?);
}

test "ion 1.1 binary e-expression length-prefixed system use affects symbol ID text (experimental)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // IVM + `F5 <addr=23> <args>` + symbol(SID=1) + symbol(SID=2)
    // Args encoding for signature: (use <key> [<version>])
    // - bitmap(1 byte): version present as single value => 01
    // - key: short string "abcs"
    // - version: int(1)
    var args = std.ArrayListUnmanaged(u8){};
    defer args.deinit(std.testing.allocator);
    try args.append(std.testing.allocator, 0x01); // bitmap: version present
    try args.appendSlice(std.testing.allocator, &.{ 0x94, 0x61, 0x62, 0x63, 0x73 }); // "abcs"
    try args.appendSlice(std.testing.allocator, &.{ 0x61, 0x01 }); // 1

    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);
    try bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xF5 });
    try appendFlexUIntShift1(std.testing.allocator, &bytes, 23);
    try appendFlexUIntShift1(std.testing.allocator, &bytes, args.items.len);
    try bytes.appendSlice(std.testing.allocator, args.items);
    try bytes.appendSlice(std.testing.allocator, &.{ 0xE1, 0x01, 0xE1, 0x02 });

    const res = try ion.binary11.parseTopLevelWithState(&arena, bytes.items);
    const elems = res.elements;
    try ion.value.resolveDefaultModuleSymbols11(&arena, elems, res.state.user_symbols, res.state.system_loaded);

    try std.testing.expectEqual(@as(usize, 2), elems.len);
    try std.testing.expect(elems[0].value == .symbol);
    try std.testing.expectEqualStrings("a", elems[0].value.symbol.text.?);
    try std.testing.expect(elems[1].value == .symbol);
    try std.testing.expectEqualStrings("$ion", elems[1].value.symbol.text.?);
}

test "ion 1.1 binary e-expression length-prefixed system set_macros updates macro table (experimental)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const sym_macro = try ion.value.makeSymbol(&arena, "macro");
    const sym_foo = try ion.value.makeSymbol(&arena, "foo");
    const sym_x = try ion.value.makeSymbol(&arena, "x");
    const sym_percent = try ion.value.makeSymbol(&arena, "%");

    // (macro foo (x) (% x))
    const params_items = try arena.allocator().alloc(ion.value.Element, 1);
    params_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = sym_x } };
    const params = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = params_items } };

    const body_items = try arena.allocator().alloc(ion.value.Element, 2);
    body_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = sym_percent } };
    body_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = sym_x } };
    const body = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = body_items } };

    const def_items = try arena.allocator().alloc(ion.value.Element, 4);
    def_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = sym_macro } };
    def_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = sym_foo } };
    def_items[2] = params;
    def_items[3] = body;
    const macro_def = ion.value.Element{ .annotations = &.{}, .value = .{ .sexp = def_items } };

    const macro_doc_bytes = try ion.writer11.writeBinary11(std.testing.allocator, &.{macro_def});
    defer std.testing.allocator.free(macro_doc_bytes);
    const macro_value_bytes = macro_doc_bytes[4..];

    // Args encoding for signature: (set_macros <macro_def*>)
    // - bitmap(1 byte): group present => 10
    // - group: <len> <payload> where payload is the encoded macro definition value expression
    var args = std.ArrayListUnmanaged(u8){};
    defer args.deinit(std.testing.allocator);
    try args.append(std.testing.allocator, 0x02); // bitmap: group present
    try appendFlexUIntShift1(std.testing.allocator, &args, macro_value_bytes.len);
    try args.appendSlice(std.testing.allocator, macro_value_bytes);

    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);
    try bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xF5 });
    try appendFlexUIntShift1(std.testing.allocator, &bytes, 21);
    try appendFlexUIntShift1(std.testing.allocator, &bytes, args.items.len);
    try bytes.appendSlice(std.testing.allocator, args.items);

    // Invoke user macro at address 0 with arg 7.
    try bytes.appendSlice(std.testing.allocator, &.{ 0x00, 0x61, 0x07 });

    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[0].value.int == .small);
    try std.testing.expectEqual(@as(i128, 7), elems[0].value.int.small);
}

test "ion 1.1 binary directives may not be invoked in containers (experimental)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // IVM + list(delimited) containing `(:$ion::add_symbols "")`
    // F1 => list(delimited start)
    // EF 14 => system macro address 20 (add_symbols)
    // 01 90 => presence=1, short string len=0
    // F0 => end(delimited)
    const bytes = &[_]u8{ 0xE0, 0x01, 0x01, 0xEA, 0xF1, 0xEF, 0x14, 0x01, 0x90, 0xF0 };
    try std.testing.expectError(ion.IonError.InvalidIon, ion.binary11.parseTopLevel(&arena, bytes));
}

test "ion 1.1 binary directives may not be invoked as e-expression arguments (experimental)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // IVM + `(:$ion::values (:use "abcs" 1))`
    // EF 01 => system macro address 1 (values)
    // 02    => presence: arg group
    // 01    => FlexUInt(0): delimited tagged group
    // EF 17 ... => system macro address 23 (use) (invalid here)
    // F0    => group terminator
    const bytes = &[_]u8{
        0xE0, 0x01, 0x01, 0xEA,
        0xEF, 0x01, 0x02, 0x01,
        0xEF, 0x17, 0x01, 0x94,
        0x61, 0x62, 0x63, 0x73,
        0x61, 0x01, 0xF0,
    };
    try std.testing.expectError(ion.IonError.InvalidIon, ion.binary11.parseTopLevel(&arena, bytes));
}

test "ion 1.1 binary directives may not be invoked inside length-prefixed arg groups (experimental)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // IVM + `(:$ion::values (:: (:use "abcs" 1)))`, but with the `values` argument group encoded
    // as a *length-prefixed* tagged expression group (not delimited).
    //
    // We reject `use` here because directives are valid only at the top-level.
    const payload = &[_]u8{
        0xEF, 0x17, // system macro address 23 (use)
        0x01, // presence: no arg groups
        0x94, // short string len=4
        0x61, 0x62, 0x63, 0x73, // "abcs"
        0x61, 0x01, // int(1)
    };

    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);

    try bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xEF, 0x01, 0x02 });
    try appendFlexUIntShift1(std.testing.allocator, &bytes, payload.len);
    try bytes.appendSlice(std.testing.allocator, payload);

    try std.testing.expectError(ion.IonError.InvalidIon, ion.binary11.parseTopLevel(&arena, bytes.items));
}

test "ion 1.1 binary respects ion-rust macro address layout when inferred" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Use a `$ion::(module ...)` directive with head SID 16 to force the decoder into the
    // ion-rust system symbol table variant for subsequent opcode interpretation.
    const anns = arena.allocator().alloc(ion.value.Symbol, 1) catch return ion.IonError.OutOfMemory;
    anns[0] = ion.value.makeSymbolId(1, null); // $ion

    const module_items = arena.allocator().alloc(ion.value.Element, 2) catch return ion.IonError.OutOfMemory;
    module_items[0] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(16, null) } };
    module_items[1] = .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "_") } };
    const module_directive: ion.value.Element = .{ .annotations = anns, .value = .{ .sexp = module_items } };

    const prefix = try ion.writer11.writeBinary11(std.testing.allocator, &.{module_directive});
    defer std.testing.allocator.free(prefix);

    // Under ion-rust's layout:
    // - addr 19 is always set_symbols (flatten is addr 5)
    // - addr 21 is always set_macros (meta is addr 3)
    // - addr 16 is always make_field (parse_ion is addr 18)
    //
    // These encodings are valid in the conformance-overloaded model, but should be rejected once
    // we have inferred the ion-rust variant.

    // 1) EF 19 with a non-text arg (would be treated as flatten under conformance).
    var b1 = std.ArrayListUnmanaged(u8){};
    defer b1.deinit(std.testing.allocator);
    try b1.appendSlice(std.testing.allocator, prefix);
    const list_items = arena.allocator().alloc(ion.value.Element, 1) catch return ion.IonError.OutOfMemory;
    list_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    const list_elem: ion.value.Element = .{ .annotations = &.{}, .value = .{ .list = list_items } };
    try ion.writer11.writeSystemMacroInvocationQualifiedTaggedGroup(std.testing.allocator, &b1, 19, &.{list_elem}, .{});
    try std.testing.expectError(ion.IonError.InvalidIon, ion.binary11.parseTopLevel(&arena, b1.items));

    // 2) EF 21 with a non-macro-def arg (would be treated as meta under conformance).
    var b2 = std.ArrayListUnmanaged(u8){};
    defer b2.deinit(std.testing.allocator);
    try b2.appendSlice(std.testing.allocator, prefix);
    const int_arg: ion.value.Element = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    try ion.writer11.writeSystemMacroInvocationQualifiedTaggedGroup(std.testing.allocator, &b2, 21, &.{int_arg}, .{});
    try std.testing.expectError(ion.IonError.InvalidIon, ion.binary11.parseTopLevel(&arena, b2.items));

    // 3) EF 16 with a string arg (would be treated as parse_ion under conformance).
    var b3 = std.ArrayListUnmanaged(u8){};
    defer b3.deinit(std.testing.allocator);
    try b3.appendSlice(std.testing.allocator, prefix);
    const str_arg: ion.value.Element = .{ .annotations = &.{}, .value = .{ .string = "1" } };
    try ion.writer11.writeSystemMacroInvocationQualifiedTaggedGroup(std.testing.allocator, &b3, 16, &.{str_arg}, .{});
    try std.testing.expectError(ion.IonError.InvalidIon, ion.binary11.parseTopLevel(&arena, b3.items));
}

test "ion 1.1 binary system sum supports big ints" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // E0 01 01 EA (IVM)
    // EF 07       (system sum)
    // F6 <len=26> <26-byte LE payload> (2^200)
    // 61 01       (int(1))
    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);

    bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xEF, 0x07, 0xF6, 0x35 }) catch return error.OutOfMemory;
    var pow2_200 = [_]u8{0} ** 26;
    pow2_200[25] = 0x01;
    bytes.appendSlice(std.testing.allocator, &pow2_200) catch return error.OutOfMemory;
    bytes.appendSlice(std.testing.allocator, &.{ 0x61, 0x01 }) catch return error.OutOfMemory;

    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[0].value.int == .big);
    try std.testing.expectEqual(@as(usize, 201), elems[0].value.int.big.toConst().bitCountAbs());
}

test "ion 1.1 binary system delta supports big ints" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // E0 01 01 EA (IVM)
    // EF 06       (system delta)
    // 02          (presence: arg group)
    // 01          (FlexUInt(0): delimited tagged group)
    // <values...> F0 (group terminator)
    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);

    bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xEF, 0x06, 0x02, 0x01, 0xF6, 0x35 }) catch return error.OutOfMemory;
    var pow2_200 = [_]u8{0} ** 26;
    pow2_200[25] = 0x01;
    bytes.appendSlice(std.testing.allocator, &pow2_200) catch return error.OutOfMemory;
    bytes.appendSlice(std.testing.allocator, &.{ 0x61, 0x01, 0xF0 }) catch return error.OutOfMemory;

    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);
    try std.testing.expectEqual(@as(usize, 2), elems.len);
    try std.testing.expect(elems[0].value == .int);
    try std.testing.expect(elems[1].value == .int);
    try std.testing.expect(elems[0].value.int == .big);
    try std.testing.expect(elems[1].value.int == .big);

    var expected1 = try std.math.big.int.Managed.initSet(std.testing.allocator, 1);
    defer expected1.deinit();
    try expected1.shiftLeft(&expected1, 200);

    var expected2 = try std.math.big.int.Managed.init(std.testing.allocator);
    defer expected2.deinit();
    try expected2.addScalar(&expected1, 1);

    try std.testing.expect(std.math.big.int.Const.order(elems[0].value.int.big.toConst(), expected1.toConst()) == .eq);
    try std.testing.expect(std.math.big.int.Const.order(elems[1].value.int.big.toConst(), expected2.toConst()) == .eq);
}

test "ion 1.1 binary system make_decimal supports big exponent and coefficient" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // E0 01 01 EA (IVM)
    // EF 0B       (system make_decimal)
    // coeff: F6 <len=17> <17-byte LE payload> (2^128)
    // exp:   F6 <len=17> <17-byte LE payload> (3)
    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);

    bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xEF, 0x0B, 0xF6, 0x23 }) catch return error.OutOfMemory;
    var coeff = [_]u8{0} ** 17;
    coeff[16] = 0x01;
    bytes.appendSlice(std.testing.allocator, &coeff) catch return error.OutOfMemory;

    bytes.appendSlice(std.testing.allocator, &.{ 0xF6, 0x23 }) catch return error.OutOfMemory;
    var exp = [_]u8{0} ** 17;
    exp[0] = 0x03;
    bytes.appendSlice(std.testing.allocator, &exp) catch return error.OutOfMemory;

    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .decimal);
    try std.testing.expectEqual(@as(i32, 3), elems[0].value.decimal.exponent);
    try std.testing.expect(!elems[0].value.decimal.is_negative);
    try std.testing.expect(elems[0].value.decimal.coefficient == .big);
    try std.testing.expectEqual(@as(usize, 129), elems[0].value.decimal.coefficient.big.toConst().bitCountAbs());
}

test "ion 1.1 binary system make_timestamp accepts big ints for fields" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // make_timestamp(year=2025, month=12, day=24, hour=1, minute=2, seconds=3, offset=0)
    // with all numeric fields encoded as 17-byte ints (F6) so they parse as `.big`.
    //
    // Presence u16: month/day/hour/minute/seconds/offset present => bits 0..5 = 01 => 0x0555
    // Little-endian bytes: 55 05
    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);

    bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xEF, 0x0C, 0x55, 0x05 }) catch return error.OutOfMemory;

    const appendBig = struct {
        fn run(list: *std.ArrayListUnmanaged(u8), v: u16) !void {
            try list.appendSlice(std.testing.allocator, &.{ 0xF6, 0x23 });
            var buf = [_]u8{0} ** 17;
            buf[0] = @intCast(v & 0xFF);
            buf[1] = @intCast((v >> 8) & 0xFF);
            try list.appendSlice(std.testing.allocator, &buf);
        }
    }.run;

    try appendBig(&bytes, 2025);
    try appendBig(&bytes, 12);
    try appendBig(&bytes, 24);
    try appendBig(&bytes, 1);
    try appendBig(&bytes, 2);
    try appendBig(&bytes, 3);
    try appendBig(&bytes, 0);

    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .timestamp);
    const ts = elems[0].value.timestamp;
    try std.testing.expectEqual(@as(i32, 2025), ts.year);
    try std.testing.expectEqual(@as(u8, 12), ts.month.?);
    try std.testing.expectEqual(@as(u8, 24), ts.day.?);
    try std.testing.expectEqual(@as(u8, 1), ts.hour.?);
    try std.testing.expectEqual(@as(u8, 2), ts.minute.?);
    try std.testing.expectEqual(@as(u8, 3), ts.second.?);
    try std.testing.expectEqual(@as(i16, 0), ts.offset_minutes.?);
}

test "ion 1.1 binary system make_timestamp supports big decimal seconds coefficient" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    // Build a decimal seconds value with a huge coefficient:
    // exponent = -50, coefficient = 3*10^50 + 1 => seconds=3, fractional=1d-50.
    const coeff = try arena.makeBigInt();
    coeff.set(@as(u8, 10)) catch return error.OutOfMemory;
    const pow10 = try arena.makeBigInt();
    pow10.pow(coeff, 50) catch return error.OutOfMemory;
    const three = try arena.makeBigInt();
    three.set(@as(u8, 3)) catch return error.OutOfMemory;
    const scaled = try arena.makeBigInt();
    scaled.mul(three, pow10) catch return error.OutOfMemory;
    scaled.addScalar(scaled, 1) catch return error.OutOfMemory;

    const sec_decimal: ion.value.Decimal = .{
        .is_negative = false,
        .coefficient = .{ .big = scaled },
        .exponent = -50,
    };

    // Use writer11 to get the Ion 1.1 binary encoding of this decimal, then embed it as the
    // `seconds` argument to `(:$ion::make_timestamp ...)`.
    const decimal_doc = &[_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .decimal = sec_decimal } }};
    const decimal_bytes = try ion.writer11.writeBinary11(std.testing.allocator, decimal_doc);
    defer std.testing.allocator.free(decimal_bytes);
    const seconds_value_bytes = decimal_bytes[4..];

    // make_timestamp(year=2025, month=12, day=24, hour=1, minute=2, seconds=<big decimal>, offset absent)
    //
    // Presence u16: month/day/hour/minute/seconds present => bits 0..4 = 01 => 0x0155
    // Little-endian bytes: 55 01
    var bytes = std.ArrayListUnmanaged(u8){};
    defer bytes.deinit(std.testing.allocator);

    bytes.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA, 0xEF, 0x0C, 0x55, 0x01 }) catch return error.OutOfMemory;
    // year=2025 (int len=2, LE 0x07E9)
    bytes.appendSlice(std.testing.allocator, &.{ 0x62, 0xE9, 0x07 }) catch return error.OutOfMemory;
    // month/day/hour/minute
    bytes.appendSlice(std.testing.allocator, &.{ 0x61, 0x0C, 0x61, 0x18, 0x61, 0x01, 0x61, 0x02 }) catch return error.OutOfMemory;
    // seconds decimal
    bytes.appendSlice(std.testing.allocator, seconds_value_bytes) catch return error.OutOfMemory;

    const elems = try ion.binary11.parseTopLevel(&arena, bytes.items);
    try std.testing.expectEqual(@as(usize, 1), elems.len);
    try std.testing.expect(elems[0].value == .timestamp);
    const ts = elems[0].value.timestamp;
    try std.testing.expectEqual(@as(u8, 3), ts.second.?);
    try std.testing.expect(ts.precision == .fractional);
    try std.testing.expect(ts.fractional != null);
    const frac = ts.fractional.?;
    try std.testing.expectEqual(@as(i32, -50), frac.exponent);
    try std.testing.expect(!frac.is_negative);
    try std.testing.expect(frac.coefficient == .small);
    try std.testing.expectEqual(@as(i128, 1), frac.coefficient.small);
}

test "ion 1.1 text system sum supports big ints" {
    // $ion_1_1 (:sum 2^200 1) => 2^200 + 1 (BigInt)
    var doc_bytes = std.ArrayListUnmanaged(u8){};
    defer doc_bytes.deinit(std.testing.allocator);

    try doc_bytes.appendSlice(std.testing.allocator, "$ion_1_1 (:sum 0x1");
    var i: usize = 0;
    while (i < 50) : (i += 1) try doc_bytes.append(std.testing.allocator, '0');
    try doc_bytes.appendSlice(std.testing.allocator, " 1)");

    var doc = try ion.parseDocument(std.testing.allocator, doc_bytes.items);
    defer doc.deinit();

    try std.testing.expectEqual(@as(usize, 1), doc.elements.len);
    try std.testing.expect(doc.elements[0].value == .int);
    try std.testing.expect(doc.elements[0].value.int == .big);
    const bi = doc.elements[0].value.int.big;
    try std.testing.expect(bi.toConst().positive);
    try std.testing.expectEqual(@as(usize, 201), bi.toConst().bitCountAbs());
}

test "ion 1.1 text system delta supports big ints" {
    // $ion_1_1 (:delta 2^200 1) => [2^200, 2^200+1]
    var doc_bytes = std.ArrayListUnmanaged(u8){};
    defer doc_bytes.deinit(std.testing.allocator);

    try doc_bytes.appendSlice(std.testing.allocator, "$ion_1_1 (:delta 0x1");
    var i: usize = 0;
    while (i < 50) : (i += 1) try doc_bytes.append(std.testing.allocator, '0');
    try doc_bytes.appendSlice(std.testing.allocator, " 1)");

    var doc = try ion.parseDocument(std.testing.allocator, doc_bytes.items);
    defer doc.deinit();

    try std.testing.expectEqual(@as(usize, 2), doc.elements.len);
    for (doc.elements) |e| {
        try std.testing.expect(e.value == .int);
        try std.testing.expect(e.value.int == .big);
        try std.testing.expect(e.value.int.big.toConst().positive);
    }

    var buf0: [26]u8 = undefined;
    var buf1: [26]u8 = undefined;
    @memset(&buf0, 0);
    @memset(&buf1, 0);
    doc.elements[0].value.int.big.toConst().writeTwosComplement(&buf0, .big);
    doc.elements[1].value.int.big.toConst().writeTwosComplement(&buf1, .big);

    var expected0 = [_]u8{0} ** 26;
    expected0[0] = 0x01;
    var expected1 = [_]u8{0} ** 26;
    expected1[0] = 0x01;
    expected1[25] = 0x01;

    try std.testing.expectEqualSlices(u8, &expected0, &buf0);
    try std.testing.expectEqualSlices(u8, &expected1, &buf1);
}

test "ion 1.1 text system make_decimal accepts big coefficient" {
    // $ion_1_1 (:make_decimal 2^200 0) => decimal(coefficient=2^200, exponent=0)
    var doc_bytes = std.ArrayListUnmanaged(u8){};
    defer doc_bytes.deinit(std.testing.allocator);

    try doc_bytes.appendSlice(std.testing.allocator, "$ion_1_1 (:make_decimal 0x1");
    var i: usize = 0;
    while (i < 50) : (i += 1) try doc_bytes.append(std.testing.allocator, '0');
    try doc_bytes.appendSlice(std.testing.allocator, " 0)");

    var doc = try ion.parseDocument(std.testing.allocator, doc_bytes.items);
    defer doc.deinit();

    try std.testing.expectEqual(@as(usize, 1), doc.elements.len);
    try std.testing.expect(doc.elements[0].value == .decimal);
    const d = doc.elements[0].value.decimal;
    try std.testing.expectEqual(@as(i32, 0), d.exponent);
    try std.testing.expect(!d.is_negative);
    try std.testing.expect(d.coefficient == .big);
    try std.testing.expectEqual(@as(usize, 201), d.coefficient.big.toConst().bitCountAbs());
}

test "ion 1.1 text system make_timestamp supports big decimal seconds coefficient" {
    // Build:
    //   seconds = (3*10^50 + 1)d-50 => second=3, fractional=1d-50
    var coeff = std.ArrayListUnmanaged(u8){};
    defer coeff.deinit(std.testing.allocator);
    try coeff.append(std.testing.allocator, '3');
    var i: usize = 0;
    while (i < 49) : (i += 1) try coeff.append(std.testing.allocator, '0');
    try coeff.append(std.testing.allocator, '1');

    var doc_bytes = std.ArrayListUnmanaged(u8){};
    defer doc_bytes.deinit(std.testing.allocator);
    try doc_bytes.appendSlice(std.testing.allocator, "$ion_1_1 (:make_timestamp 2025 12 24 1 2 ");
    try doc_bytes.appendSlice(std.testing.allocator, coeff.items);
    try doc_bytes.appendSlice(std.testing.allocator, "d-50)");

    var doc = try ion.parseDocument(std.testing.allocator, doc_bytes.items);
    defer doc.deinit();

    try std.testing.expectEqual(@as(usize, 1), doc.elements.len);
    try std.testing.expect(doc.elements[0].value == .timestamp);
    const ts = doc.elements[0].value.timestamp;
    try std.testing.expectEqual(@as(i32, 2025), ts.year);
    try std.testing.expectEqual(@as(u8, 12), ts.month.?);
    try std.testing.expectEqual(@as(u8, 24), ts.day.?);
    try std.testing.expectEqual(@as(u8, 1), ts.hour.?);
    try std.testing.expectEqual(@as(u8, 2), ts.minute.?);
    try std.testing.expectEqual(@as(u8, 3), ts.second.?);
    try std.testing.expect(ts.precision == .fractional);
    try std.testing.expect(ts.fractional != null);
    const frac = ts.fractional.?;
    try std.testing.expectEqual(@as(i32, -50), frac.exponent);
    try std.testing.expect(!frac.is_negative);
    try std.testing.expect(frac.coefficient == .small);
    try std.testing.expectEqual(@as(i128, 1), frac.coefficient.small);
}

test "ion 1.1 binary writer roundtrip (basic)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const list_items = try arena.allocator().alloc(ion.value.Element, 2);
    list_items[0] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } };
    list_items[1] = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } };

    const struct_fields = try arena.allocator().alloc(ion.value.StructField, 3);
    struct_fields[0] = .{
        .name = .{ .sid = null, .text = "foo" },
        .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
    };
    struct_fields[1] = .{
        .name = .{ .sid = null, .text = "bar" },
        .value = .{ .annotations = &.{}, .value = .{ .string = "x" } },
    };
    struct_fields[2] = .{
        .name = .{ .sid = 200, .text = null },
        .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 9 } } },
    };

    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .string = "hello" } },
        .{ .annotations = &.{}, .value = .{ .symbol = .{ .sid = null, .text = "sym" } } },
        .{ .annotations = &.{}, .value = .{ .symbol = .{ .sid = 200, .text = null } } },
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

test "ion 1.1 binary writer roundtrip (annotations)" {
    var ann_text_arr = [_]ion.value.Symbol{.{ .sid = null, .text = "ann" }};
    var ann_sids_arr = [_]ion.value.Symbol{
        .{ .sid = 1, .text = null },
        .{ .sid = 2, .text = null },
        .{ .sid = 3, .text = null },
    };
    const ann_text: []ion.value.Symbol = ann_text_arr[0..];
    const ann_sids: []ion.value.Symbol = ann_sids_arr[0..];

    const doc = &[_]ion.value.Element{
        .{ .annotations = ann_text, .value = .{ .int = .{ .small = 7 } } },
        .{ .annotations = ann_sids, .value = .{ .string = "x" } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();

    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}

test "ion 1.1 binary_1_1 serialize rejects sid-only annotations" {
    var ann_sids_arr = [_]ion.value.Symbol{
        .{ .sid = 200, .text = null },
        .{ .sid = 201, .text = null },
    };
    const ann_sids: []ion.value.Symbol = ann_sids_arr[0..];

    const doc = &[_]ion.value.Element{
        .{ .annotations = ann_sids, .value = .{ .string = "x" } },
    };

    try std.testing.expectError(ion.IonError.InvalidIon, ion.serializeDocument(std.testing.allocator, .binary_1_1, doc));
}

test "ion 1.1 binary_1_1 serialize rejects sid-only field names" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const struct_fields = try arena.allocator().alloc(ion.value.StructField, 1);
    struct_fields[0] = .{
        .name = .{ .sid = 200, .text = null },
        .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
    };

    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = struct_fields } } },
    };

    try std.testing.expectError(ion.IonError.InvalidIon, ion.serializeDocument(std.testing.allocator, .binary_1_1, doc));
}

test "ion 1.1 binary writer roundtrip (typed nulls)" {
    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .null = .null } },
        .{ .annotations = &.{}, .value = .{ .null = .bool } },
        .{ .annotations = &.{}, .value = .{ .null = .int } },
        .{ .annotations = &.{}, .value = .{ .null = .float } },
        .{ .annotations = &.{}, .value = .{ .null = .decimal } },
        .{ .annotations = &.{}, .value = .{ .null = .timestamp } },
        .{ .annotations = &.{}, .value = .{ .null = .string } },
        .{ .annotations = &.{}, .value = .{ .null = .symbol } },
        .{ .annotations = &.{}, .value = .{ .null = .blob } },
        .{ .annotations = &.{}, .value = .{ .null = .clob } },
        .{ .annotations = &.{}, .value = .{ .null = .list } },
        .{ .annotations = &.{}, .value = .{ .null = .sexp } },
        .{ .annotations = &.{}, .value = .{ .null = .@"struct" } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();

    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}

test "ion 1.1 writer11 can emit length-prefixed containers" {
    var list_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
    };
    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .list = &.{} } },
        .{ .annotations = &.{}, .value = .{ .sexp = &.{} } },
        .{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = &.{} } } },
        .{ .annotations = &.{}, .value = .{ .list = list_items[0..] } },
    };

    const bytes = try ion.writer11.writeBinary11WithOptions(std.testing.allocator, doc, .{ .container_encoding = .length_prefixed });
    defer std.testing.allocator.free(bytes);

    try std.testing.expect(bytes.len >= 7);
    try std.testing.expectEqual(@as(u8, 0xE0), bytes[0]);
    try std.testing.expectEqual(@as(u8, 0x01), bytes[1]);
    try std.testing.expectEqual(@as(u8, 0x01), bytes[2]);
    try std.testing.expectEqual(@as(u8, 0xEA), bytes[3]);

    // First three values are empty containers: B0 (list), C0 (sexp), D0 (struct).
    try std.testing.expectEqual(@as(u8, 0xB0), bytes[4]);
    try std.testing.expectEqual(@as(u8, 0xC0), bytes[5]);
    try std.testing.expectEqual(@as(u8, 0xD0), bytes[6]);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}

test "ion 1.1 text can apply $ion::(module ...) to install user macros" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const input =
        "$ion_1_1\n" ++
        "$ion::(module _ (macros (macro m () 1)) (symbols _))\n" ++
        "(:m) (:0)\n";

    const got = try ion.text.parseTopLevel(&arena, input);
    try std.testing.expectEqual(@as(usize, 2), got.len);
    for (got) |e| {
        try std.testing.expectEqual(@as(usize, 0), e.annotations.len);
        try std.testing.expect(e.value == .int);
        switch (e.value.int) {
            .small => |v| try std.testing.expectEqual(@as(i128, 1), v),
            else => return error.TestExpectedEqual,
        }
    }
}

test "ion 1.1 text can apply $1::(module ...) directive" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const input =
        "$ion_1_1\n" ++
        "$1::(module _ (macros (macro m () 1)) (symbols _))\n" ++
        "(:m)\n";

    const got = try ion.text.parseTopLevel(&arena, input);
    try std.testing.expectEqual(@as(usize, 1), got.len);
    try std.testing.expect(got[0].value == .int);
    switch (got[0].value.int) {
        .small => |v| try std.testing.expectEqual(@as(i128, 1), v),
        else => return error.TestExpectedEqual,
    }
}

test "ion 1.1 binary writer roundtrip (timestamps long form)" {
    const frac: ion.value.Decimal = .{ .is_negative = false, .coefficient = .{ .small = 123 }, .exponent = -3 };
    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = null,
            .day = null,
            .hour = null,
            .minute = null,
            .second = null,
            .fractional = null,
            .offset_minutes = null,
            .precision = .year,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = null,
            .hour = null,
            .minute = null,
            .second = null,
            .fractional = null,
            .offset_minutes = null,
            .precision = .month,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = null,
            .minute = null,
            .second = null,
            .fractional = null,
            .offset_minutes = null,
            .precision = .day,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = null,
            .fractional = null,
            .offset_minutes = null,
            .precision = .minute,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = 3,
            .fractional = null,
            .offset_minutes = 0,
            .precision = .second,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = 3,
            .fractional = frac,
            .offset_minutes = -480,
            .precision = .fractional,
        } } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();

    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}

test "ion 1.1 binary writer roundtrip (timestamp long big fractional coefficient)" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const bi = try arena.makeBigInt();
    try bi.set(@as(u8, 1));
    try bi.shiftLeft(bi, 200);
    try std.testing.expectEqual(@as(usize, 201), bi.toConst().bitCountAbs());

    const frac: ion.value.Decimal = .{
        .is_negative = false,
        .coefficient = .{ .big = bi },
        .exponent = -20,
    };

    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = 3,
            .fractional = frac,
            .offset_minutes = null,
            .precision = .fractional,
        } } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();

    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}

test "ion 1.1 binary writer emits delimited containers" {
    var list_items_arr = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
    };
    var sexp_items_arr = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
    };
    const list_items: []ion.value.Element = list_items_arr[0..];
    const sexp_items: []ion.value.Element = sexp_items_arr[0..];

    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .list = list_items } },
        .{ .annotations = &.{}, .value = .{ .sexp = sexp_items } },
        .{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = &.{} } } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    try std.testing.expect(std.mem.indexOfScalar(u8, bytes, 0xF1) != null);
    try std.testing.expect(std.mem.indexOfScalar(u8, bytes, 0xF2) != null);
    try std.testing.expect(std.mem.indexOfScalar(u8, bytes, 0xF3) != null);
    // Struct close marker is FlexInt(0) (0x01) followed by the FlexSym escape byte 0xF0.
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0x01, 0xF0 }) != null);
}

test "ion 1.1 binary writer uses EE for system symbols" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = .{ .sid = null, .text = "$ion" } } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    // 0xEE <addr>
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0xEE, 0x01 }) != null);

    const parsed = try ion.binary11.parseTopLevel(&arena, bytes);
    try std.testing.expectEqual(@as(usize, 1), parsed.len);
    try std.testing.expect(parsed[0].value == .symbol);
    try std.testing.expectEqualStrings("$ion", parsed[0].value.symbol.text orelse return error.TestExpectedEqual);
}

test "ion 1.1 binary writer uses FlexSym escape for system field names" {
    var arena = try ion.value.Arena.init(std.testing.allocator);
    defer arena.deinit();

    const struct_fields = try arena.allocator().alloc(ion.value.StructField, 1);
    struct_fields[0] = .{
        .name = .{ .sid = null, .text = "$ion" },
        .value = .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
    };
    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .@"struct" = .{ .fields = struct_fields } } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    // F3 (struct open), then FlexSym escape for address 1 ($ion): 01 61.
    try std.testing.expect(std.mem.indexOf(u8, bytes, &.{ 0xF3, 0x01, 0x61, 0x61, 0x01 }) != null);

    const parsed = try ion.binary11.parseTopLevel(&arena, bytes);
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}

test "ion 1.1 binary writer emits float widths" {
    // 1.5 is exactly representable as f16 -> should be encoded as 0x6B (f16).
    // 1 + 2^-23 is exactly representable as f32 but not f16 -> should be encoded as 0x6C (f32).
    // 1 + 2^-52 is only exactly representable as f64 -> should be encoded as 0x6D (f64).
    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .float = 1.5 } },
        .{ .annotations = &.{}, .value = .{ .float = 1.00000011920928955078125 } },
        .{ .annotations = &.{}, .value = .{ .float = 1.0000000000000002220446049250313080847263336181640625 } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    try std.testing.expect(std.mem.indexOfScalar(u8, bytes, 0x6B) != null);
    try std.testing.expect(std.mem.indexOfScalar(u8, bytes, 0x6C) != null);
    try std.testing.expect(std.mem.indexOfScalar(u8, bytes, 0x6D) != null);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();

    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}

test "ion 1.1 binary writer encodes positive big int with sign bit set" {
    // 2^127 cannot be represented as i128, so it uses the BigInt path. It requires a leading 0x00
    // sign-extension byte in two's complement to remain positive.
    var b = std.math.big.int.Managed.init(std.testing.allocator) catch return error.OutOfMemory;
    defer b.deinit();

    // Two's complement LE for 2^127: 17 bytes with byte[15]=0x80 and byte[16]=0x00.
    var tc: [17]u8 = [_]u8{0} ** 17;
    tc[15] = 0x80;
    tc[16] = 0x00;
    {
        const bit_count: usize = tc.len * 8;
        const limb_bits: usize = @bitSizeOf(std.math.big.Limb);
        const needed_limbs: usize = (bit_count + limb_bits - 1) / limb_bits;
        b.ensureCapacity(needed_limbs) catch return error.OutOfMemory;
        var m = b.toMutable();
        m.readTwosComplement(&tc, bit_count, .little, .signed);
        b.setMetadata(m.positive, m.len);
    }

    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .big = &b } } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}

test "ion 1.1 binary writer encodes negative big int with sign extension" {
    // -2^128 cannot be represented as i128, so it uses the BigInt path.
    var b = std.math.big.int.Managed.init(std.testing.allocator) catch return error.OutOfMemory;
    defer b.deinit();

    // Two's complement LE for -2^128: 17 bytes with byte[16]=0xFF and bytes[0..16]=0x00.
    var tc: [17]u8 = [_]u8{0} ** 17;
    tc[16] = 0xFF;
    {
        const bit_count: usize = tc.len * 8;
        const limb_bits: usize = @bitSizeOf(std.math.big.Limb);
        const needed_limbs: usize = (bit_count + limb_bits - 1) / limb_bits;
        b.ensureCapacity(needed_limbs) catch return error.OutOfMemory;
        var m = b.toMutable();
        m.readTwosComplement(&tc, bit_count, .little, .signed);
        b.setMetadata(m.positive, m.len);
    }

    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .big = &b } } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}

test "ion 1.1 binary writer emits short timestamps" {
    const ms: ion.value.Decimal = .{ .is_negative = false, .coefficient = .{ .small = 5 }, .exponent = -3 };
    const doc = &[_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = null,
            .day = null,
            .hour = null,
            .minute = null,
            .second = null,
            .fractional = null,
            .offset_minutes = null,
            .precision = .year,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = null,
            .hour = null,
            .minute = null,
            .second = null,
            .fractional = null,
            .offset_minutes = null,
            .precision = .month,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = null,
            .minute = null,
            .second = null,
            .fractional = null,
            .offset_minutes = null,
            .precision = .day,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = null,
            .fractional = null,
            .offset_minutes = null,
            .precision = .minute,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = 3,
            .fractional = null,
            .offset_minutes = 0,
            .precision = .second,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = 3,
            .fractional = ms,
            .offset_minutes = 0,
            .precision = .fractional,
        } } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    // Expect at least one short timestamp opcode in 0x80..0x8F.
    var saw_short = false;
    for (bytes) |b| {
        if (b >= 0x80 and b <= 0x8F) {
            saw_short = true;
            break;
        }
    }
    try std.testing.expect(saw_short);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expect(ion.eq.ionEqElements(doc, parsed));
}

test "ion 1.1 binary writer emits short timestamp variants" {
    const ms5: ion.value.Decimal = .{ .is_negative = false, .coefficient = .{ .small = 5 }, .exponent = -3 };
    const us123456: ion.value.Decimal = .{ .is_negative = false, .coefficient = .{ .small = 123456 }, .exponent = -6 };
    const ns7: ion.value.Decimal = .{ .is_negative = false, .coefficient = .{ .small = 7 }, .exponent = -9 };

    const doc = &[_]ion.value.Element{
        // UTC/unknown-offset microseconds (0x86)
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = 3,
            .fractional = us123456,
            .offset_minutes = null,
            .precision = .fractional,
        } } },
        // UTC/unknown-offset nanoseconds (0x87)
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = 3,
            .fractional = ns7,
            .offset_minutes = null,
            .precision = .fractional,
        } } },
        // Known offset minute/second/ms (0x88/0x89/0x8A)
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = null,
            .fractional = null,
            .offset_minutes = -480,
            .precision = .minute,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = 3,
            .fractional = null,
            .offset_minutes = -480,
            .precision = .second,
        } } },
        .{ .annotations = &.{}, .value = .{ .timestamp = .{
            .year = 2025,
            .month = 12,
            .day = 24,
            .hour = 1,
            .minute = 2,
            .second = 3,
            .fractional = ms5,
            .offset_minutes = -480,
            .precision = .fractional,
        } } },
    };

    const bytes = try ion.writer11.writeBinary11(std.testing.allocator, doc);
    defer std.testing.allocator.free(bytes);

    try std.testing.expect(std.mem.indexOfScalar(u8, bytes, 0x86) != null);
    try std.testing.expect(std.mem.indexOfScalar(u8, bytes, 0x87) != null);
    try std.testing.expect(std.mem.indexOfScalar(u8, bytes, 0x88) != null);
    try std.testing.expect(std.mem.indexOfScalar(u8, bytes, 0x89) != null);
    try std.testing.expect(std.mem.indexOfScalar(u8, bytes, 0x8A) != null);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    if (!ion.eq.ionEqElements(doc, parsed)) {
        const dumpTs = struct {
            fn run(prefix: []const u8, ts: ion.value.Timestamp) void {
                std.debug.print(
                    "{s} y={d} m={any} d={any} hh={any} mm={any} ss={any} off={any} prec={any} frac={any}\n",
                    .{ prefix, ts.year, ts.month, ts.day, ts.hour, ts.minute, ts.second, ts.offset_minutes, ts.precision, ts.fractional },
                );
            }
        }.run;

        std.debug.print("writer bytes len={d}\n", .{bytes.len});
        var i: usize = 0;
        while (i < bytes.len) : (i += 1) {
            std.debug.print("{X:0>2} ", .{bytes[i]});
            if ((i + 1) % 16 == 0) std.debug.print("\n", .{});
        }
        std.debug.print("\n", .{});

        std.debug.print("doc.len={d} parsed.len={d}\n", .{ doc.len, parsed.len });
        const n = @min(doc.len, parsed.len);
        for (0..n) |idx| {
            if (!ion.eq.ionEqElement(doc[idx], parsed[idx])) {
                std.debug.print("mismatch at idx={d}\n", .{idx});
                if (doc[idx].value == .timestamp) dumpTs("expected:", doc[idx].value.timestamp);
                if (parsed[idx].value == .timestamp) dumpTs("actual:  ", parsed[idx].value.timestamp);
                break;
            }
        }
        return error.TestUnexpectedResult;
    }
}

test "ion 1.1 binary module macro_table clause enables user macro invocation" {
    var params = [_]ion.macro.Param{
        .{ .ty = .tagged, .card = .one, .name = "x", .shape = null },
    };

    var var_ref_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "%x") } },
    };
    var body_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .sexp = var_ref_items[0..] } },
    };

    const m: ion.macro.Macro = .{
        .name = "id",
        .params = params[0..],
        .body = body_items[0..],
    };
    var macros = [_]ion.macro.Macro{m};
    const tab: ion.macro.MacroTable = .{ .base_addr = ion.macro.system_macro_count, .macros = macros[0..] };

    const arg_elem = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 7 } } },
    };
    const args_by_param = [_][]const ion.value.Element{arg_elem[0..]};

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);

    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeIonSystemModuleDirectivePrelude(std.testing.allocator, &out, &.{}, &tab, .{});
    try ion.writer11.writeUserMacroInvocationAtAddressWithParams(
        std.testing.allocator,
        &out,
        ion.macro.system_macro_count,
        params[0..],
        args_by_param[0..],
        .{},
    );

    const bytes = try out.toOwnedSlice(std.testing.allocator);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expectEqual(@as(usize, 1), parsed.len);
    try std.testing.expect(parsed[0].annotations.len == 0);
    try std.testing.expect(parsed[0].value == .int);
    try std.testing.expectEqual(@as(i128, 7), parsed[0].value.int.small);
}

test "ion 1.1 binary e-expression F5: meta produces no values" {
    const args = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationLengthPrefixedTaggedVariadic(
        std.testing.allocator,
        &out,
        3, // meta
        args[0..],
    );

    const bytes = try out.toOwnedSlice(std.testing.allocator);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expectEqual(@as(usize, 0), parsed.len);
}

test "ion 1.1 binary e-expression F5: flatten concatenates sequences" {
    var list_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 2 } } },
    };
    var sexp_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 3 } } },
        .{ .annotations = &.{}, .value = .{ .int = .{ .small = 4 } } },
    };
    const seqs = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .list = list_items[0..] } },
        .{ .annotations = &.{}, .value = .{ .sexp = sexp_items[0..] } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationLengthPrefixedTaggedVariadic(
        std.testing.allocator,
        &out,
        5, // flatten
        seqs[0..],
    );

    const bytes = try out.toOwnedSlice(std.testing.allocator);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expectEqual(@as(usize, 4), parsed.len);
    for (parsed, 0..) |e, i| {
        try std.testing.expect(e.annotations.len == 0);
        try std.testing.expect(e.value == .int);
        try std.testing.expectEqual(@as(i128, @intCast(i + 1)), e.value.int.small);
    }
}

test "ion 1.1 binary e-expression F5: make_field produces a single-field struct" {
    const params = [_]ion.macro.Param{
        .{ .ty = .tagged, .card = .one, .name = "name", .shape = null },
        .{ .ty = .tagged, .card = .one, .name = "value", .shape = null },
    };

    const name_args = [_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "a") } }};
    const value_args = [_]ion.value.Element{.{ .annotations = &.{}, .value = .{ .int = .{ .small = 1 } } }};
    const args_by_param = [_][]const ion.value.Element{ name_args[0..], value_args[0..] };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationLengthPrefixedWithParams(
        std.testing.allocator,
        &out,
        16, // make_field
        params[0..],
        args_by_param[0..],
        .{},
    );

    const bytes = try out.toOwnedSlice(std.testing.allocator);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expectEqual(@as(usize, 1), parsed.len);
    try std.testing.expect(parsed[0].annotations.len == 0);
    try std.testing.expect(parsed[0].value == .@"struct");
    const st = parsed[0].value.@"struct";
    try std.testing.expectEqual(@as(usize, 1), st.fields.len);
    try std.testing.expect(st.fields[0].name.text != null and std.mem.eql(u8, st.fields[0].name.text.?, "a"));
    try std.testing.expect(st.fields[0].value.value == .int);
    try std.testing.expectEqual(@as(i128, 1), st.fields[0].value.value.int.small);
}

test "ion 1.1 binary e-expression F5: parse_ion parses embedded Ion bytes" {
    const args = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .string = "1 2" } },
    };

    var out = std.ArrayListUnmanaged(u8){};
    defer out.deinit(std.testing.allocator);
    try out.appendSlice(std.testing.allocator, &.{ 0xE0, 0x01, 0x01, 0xEA });
    try ion.writer11.writeSystemMacroInvocationLengthPrefixedTaggedVariadic(
        std.testing.allocator,
        &out,
        18, // parse_ion
        args[0..],
    );

    const bytes = try out.toOwnedSlice(std.testing.allocator);
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevel(&parsed_arena, bytes);
    try std.testing.expectEqual(@as(usize, 2), parsed.len);
    try std.testing.expect(parsed[0].value == .int);
    try std.testing.expect(parsed[1].value == .int);
    try std.testing.expectEqual(@as(i128, 1), parsed[0].value.int.small);
    try std.testing.expectEqual(@as(i128, 2), parsed[1].value.int.small);
}

test "ion 1.1 binary module directive accepts symbol_table list wrapper" {
    var sym_list_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .string = "a" } },
        .{ .annotations = &.{}, .value = .{ .string = "b" } },
    };
    const sym_list_elem = ion.value.Element{ .annotations = &.{}, .value = .{ .list = sym_list_items[0..] } };

    var symbol_table_clause_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "symbol_table") } },
        sym_list_elem,
    };
    var macro_table_clause_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "macro_table") } },
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "_") } },
    };

    var module_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "module") } },
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "_") } },
        .{ .annotations = &.{}, .value = .{ .sexp = symbol_table_clause_items[0..] } },
        .{ .annotations = &.{}, .value = .{ .sexp = macro_table_clause_items[0..] } },
    };

    var anns = [_]ion.value.Symbol{ion.value.makeSymbolId(null, "$ion")};
    const doc = &[_]ion.value.Element{
        .{ .annotations = anns[0..], .value = .{ .sexp = module_items[0..] } },
    };

    const bytes = try ion.writer11.writeBinary11WithOptions(std.testing.allocator, doc, .{ .symbol_encoding = .addresses });
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevelWithState(&parsed_arena, bytes);
    try std.testing.expectEqual(@as(usize, 0), parsed.elements.len);
    try std.testing.expect(parsed.state.system_loaded);
    try std.testing.expectEqual(@as(usize, 2), parsed.state.user_symbols.len);
    try std.testing.expect(parsed.state.user_symbols[0] != null and std.mem.eql(u8, parsed.state.user_symbols[0].?, "a"));
    try std.testing.expect(parsed.state.user_symbols[1] != null and std.mem.eql(u8, parsed.state.user_symbols[1].?, "b"));
}

test "ion 1.1 binary module directive symbol_table underscore appends" {
    var sym_list1_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .string = "a" } },
    };
    var sym_list2_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .string = "b" } },
        .{ .annotations = &.{}, .value = .{ .string = "c" } },
    };
    const sym_list1_elem = ion.value.Element{ .annotations = &.{}, .value = .{ .list = sym_list1_items[0..] } };
    const sym_list2_elem = ion.value.Element{ .annotations = &.{}, .value = .{ .list = sym_list2_items[0..] } };

    var clause1_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "symbol_table") } },
        sym_list1_elem,
    };
    var clause2_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "symbol_table") } },
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "_") } },
        sym_list2_elem,
    };
    var macro_table_clause_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "macro_table") } },
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "_") } },
    };

    var module1_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "module") } },
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "_") } },
        .{ .annotations = &.{}, .value = .{ .sexp = clause1_items[0..] } },
        .{ .annotations = &.{}, .value = .{ .sexp = macro_table_clause_items[0..] } },
    };
    var module2_items = [_]ion.value.Element{
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "module") } },
        .{ .annotations = &.{}, .value = .{ .symbol = ion.value.makeSymbolId(null, "_") } },
        .{ .annotations = &.{}, .value = .{ .sexp = clause2_items[0..] } },
        .{ .annotations = &.{}, .value = .{ .sexp = macro_table_clause_items[0..] } },
    };

    var anns = [_]ion.value.Symbol{ion.value.makeSymbolId(null, "$ion")};
    const doc = &[_]ion.value.Element{
        .{ .annotations = anns[0..], .value = .{ .sexp = module1_items[0..] } },
        .{ .annotations = anns[0..], .value = .{ .sexp = module2_items[0..] } },
    };

    const bytes = try ion.writer11.writeBinary11WithOptions(std.testing.allocator, doc, .{ .symbol_encoding = .addresses });
    defer std.testing.allocator.free(bytes);

    var parsed_arena = try ion.value.Arena.init(std.testing.allocator);
    defer parsed_arena.deinit();
    const parsed = try ion.binary11.parseTopLevelWithState(&parsed_arena, bytes);
    try std.testing.expectEqual(@as(usize, 0), parsed.elements.len);
    try std.testing.expect(parsed.state.system_loaded);
    try std.testing.expectEqual(@as(usize, 3), parsed.state.user_symbols.len);
    try std.testing.expect(parsed.state.user_symbols[0] != null and std.mem.eql(u8, parsed.state.user_symbols[0].?, "a"));
    try std.testing.expect(parsed.state.user_symbols[1] != null and std.mem.eql(u8, parsed.state.user_symbols[1].?, "b"));
    try std.testing.expect(parsed.state.user_symbols[2] != null and std.mem.eql(u8, parsed.state.user_symbols[2].?, "c"));
}
