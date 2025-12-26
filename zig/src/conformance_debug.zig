const std = @import("std");
const runner = @import("conformance/runner.zig");
const conformance_catalog = @import("conformance/catalog.zig");

pub fn main() !void {
    var gpa_impl = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_impl.deinit();
    const gpa = gpa_impl.allocator();

    var args_it = try std.process.argsWithAllocator(gpa);
    defer args_it.deinit();

    _ = args_it.next(); // exe
    const path = args_it.next() orelse {
        std.debug.print("usage: conformance_debug <path>\n", .{});
        return error.InvalidArgs;
    };

    const data = try std.fs.cwd().readFileAlloc(gpa, path, 128 * 1024 * 1024);
    defer gpa.free(data);

    var cat = try conformance_catalog.loadIonTestsCatalogDefault(gpa);
    defer cat.deinit();

    var stats: runner.Stats = .{};
    runner.runConformanceFileWithCatalog(gpa, data, &stats, &cat) catch |e| {
        std.debug.print("conformance failed: {s}: {s}\n", .{ path, @errorName(e) });
        std.debug.print("cases={d} branches={d} passed={d} skipped={d}\n", .{ stats.cases, stats.branches, stats.passed, stats.skipped });
        return e;
    };

    std.debug.print("OK: {s}\n", .{path});
    std.debug.print("cases={d} branches={d} passed={d} skipped={d}\n", .{ stats.cases, stats.branches, stats.passed, stats.skipped });
}
