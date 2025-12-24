//! Zig build script for the Ion Zig port.
//!
//! `zig build test` runs the Zig `ion-tests` harness without invoking Cargo.

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    // Performance: the test harness walks thousands of `ion-tests` fixtures. Running in Debug can
    // take orders of magnitude longer than the Rust suite, so default to `ReleaseFast` and let
    // callers opt into Debug with `-Doptimize=Debug` when they need it.
    const optimize = b.option(std.builtin.OptimizeMode, "optimize", "Optimization mode") orelse .ReleaseFast;

    const root_mod = b.createModule(.{
        .root_source_file = b.path("src/tests.zig"),
        .target = target,
        .optimize = optimize,
    });

    const tests = b.addTest(.{
        .root_module = root_mod,
    });

    const run = b.addRunArtifact(tests);
    run.setCwd(b.path(".."));

    const test_step = b.step("test", "Run ion-tests against the Zig harness");
    test_step.dependOn(&run.step);
}
