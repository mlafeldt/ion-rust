const std = @import("std");
const conformance = @import("conformance/runner.zig");

const Entry = struct {
    path: []const u8,
    skipped: u64,
};

fn hasSuffix(path: []const u8, suffix: []const u8) bool {
    return std.mem.endsWith(u8, path, suffix);
}

fn addStats(dst: *conformance.Stats, src: conformance.Stats) void {
    dst.cases += src.cases;
    dst.branches += src.branches;
    dst.passed += src.passed;
    dst.skipped += src.skipped;
}

fn lessBySkipped(_: void, a: Entry, b: Entry) bool {
    if (a.skipped != b.skipped) return a.skipped > b.skipped;
    return std.mem.lessThan(u8, a.path, b.path);
}

fn parseArgs(gpa: std.mem.Allocator) !struct { root: []const u8, top: usize } {
    var it = try std.process.argsWithAllocator(gpa);
    defer it.deinit();

    _ = it.next(); // exe

    var root: []const u8 = "../ion-tests/conformance";
    var top: usize = 10;

    while (it.next()) |arg| {
        if (std.mem.eql(u8, arg, "--top")) {
            const n = it.next() orelse return error.InvalidArgs;
            top = try std.fmt.parseInt(usize, n, 10);
            continue;
        }
        if (std.mem.eql(u8, arg, "--help")) return error.Help;
        root = arg;
    }

    return .{ .root = root, .top = top };
}

pub fn main() !void {
    var gpa_impl = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_impl.deinit();
    const gpa = gpa_impl.allocator();

    const args = parseArgs(gpa) catch |e| switch (e) {
        error.Help => {
            std.debug.print(
                "usage: conformance_totals [conformance_dir] [--top N]\n" ++
                    "default dir: ../ion-tests/conformance\n",
                .{},
            );
            return;
        },
        else => return e,
    };

    var dir = try std.fs.cwd().openDir(args.root, .{ .iterate = true });
    defer dir.close();

    var walker = try dir.walk(gpa);
    defer walker.deinit();

    var totals: conformance.Stats = .{};
    var entries = std.ArrayListUnmanaged(Entry){};
    defer {
        for (entries.items) |e| gpa.free(e.path);
        entries.deinit(gpa);
    }

    while (try walker.next()) |it| {
        if (it.kind != .file) continue;
        if (!hasSuffix(it.path, ".ion")) continue;

        const full_path = try std.fs.path.join(gpa, &.{ args.root, it.path });
        defer gpa.free(full_path);

        const data = try std.fs.cwd().readFileAlloc(gpa, full_path, 128 * 1024 * 1024);
        defer gpa.free(data);

        var st: conformance.Stats = .{};
        conformance.runConformanceFile(gpa, data, &st) catch |e| {
            std.debug.print("conformance failed: {s}: {s}\n", .{ full_path, @errorName(e) });
            return e;
        };

        addStats(&totals, st);

        const owned_path = try gpa.dupe(u8, full_path);
        try entries.append(gpa, .{ .path = owned_path, .skipped = st.skipped });
    }

    std.mem.sort(Entry, entries.items, {}, lessBySkipped);

    std.debug.print("Total branches: {d}\n", .{totals.branches});
    std.debug.print("Passed: {d}\n", .{totals.passed});
    std.debug.print("Skipped (unsupported): {d}\n", .{totals.skipped});
    std.debug.print("\nLargest remaining skip buckets (by file)\n\n", .{});

    const top_n = @min(args.top, entries.items.len);
    var i: usize = 0;
    while (i < top_n) : (i += 1) {
        const e = entries.items[i];
        if (e.skipped == 0) break;
        std.debug.print("{d}) `{s}`: skipped={d}\n", .{ i + 1, e.path, e.skipped });
    }
}

