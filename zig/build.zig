const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Build the Rust static library that the Zig test harness links against.
    const cargo_build = b.addSystemCommand(&.{
        "cargo",
        "build",
        "--release",
        "--features",
        "zig-ffi",
    });
    cargo_build.setCwd(b.path(".."));

    const root_mod = b.createModule(.{
        .root_source_file = b.path("src/tests.zig"),
        .target = target,
        .optimize = optimize,
    });

    const tests = b.addTest(.{
        .root_module = root_mod,
    });
    tests.step.dependOn(&cargo_build.step);
    tests.linkLibC();
    tests.linkFramework("CoreFoundation");
    tests.addObjectFile(b.path("../target/release/libion_rs.a"));

    const run = b.addRunArtifact(tests);
    run.step.dependOn(&cargo_build.step);
    run.setCwd(b.path(".."));

    const test_step = b.step("test", "Run ion-tests against the Zig harness");
    test_step.dependOn(&run.step);
}
