const std = @import("std");
const ion = @import("ion");

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);
    if (args.len != 2) {
        std.debug.print("usage: {s} <path>\n", .{args[0]});
        return error.InvalidArgs;
    }

    const path = args[1];
    const data = try std.fs.cwd().readFileAlloc(gpa, path, 128 * 1024 * 1024);
    defer gpa.free(data);

    var doc = try ion.parseDocument(gpa, data);
    defer doc.deinit();

    // Mini roundtrip (compact -> pretty), mirroring the reduced-pair harness behavior.
    const b1 = try ion.serializeDocument(gpa, .text_compact, doc.elements);
    defer gpa.free(b1);
    var d1 = try ion.parseDocument(gpa, b1);
    defer d1.deinit();

    const b2 = try ion.serializeDocument(gpa, .text_pretty, d1.elements);
    defer gpa.free(b2);
    var d2 = try ion.parseDocument(gpa, b2);
    defer d2.deinit();

    if (!ion.eq.ionEqElements(doc.elements, d2.elements)) return error.RoundTripFailed;

    // Force a small amount of traversal so dead-code-elimination doesn't skip everything in Release.
    var count: usize = 0;
    for (doc.elements) |_| count += 1;
    std.debug.print("elements: {d}\n", .{count});
}
