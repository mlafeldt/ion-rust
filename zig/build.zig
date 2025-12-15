//! Zig build script for the Ion Zig port.
//!
//! `zig build test` runs the Zig `ion-tests` harness without invoking Cargo.

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

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
