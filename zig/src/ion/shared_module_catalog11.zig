//! Minimal Ion 1.1 shared module catalog used by the conformance suite.
//!
//! The conformance suite models `use` as importing symbols into the default module address space.
//! This is not a general-purpose catalog API; it exists so both the conformance runner and the
//! Ion 1.1 parsers can share the same tiny catalog data set.

const std = @import("std");

pub const Entry = struct {
    name: []const u8,
    version: u32,
    symbols: []const []const u8,
};

// Minimal Ion 1.1 shared module catalog required by `ion-tests/conformance/system_macros/use.ion`.
const entries = [_]Entry{
    .{ .name = "abcs", .version = 1, .symbols = &.{"a"} },
    .{ .name = "abcs", .version = 2, .symbols = &.{ "a", "b" } },
    .{ .name = "mnop", .version = 1, .symbols = &.{"m"} },
};

pub fn lookup(name: []const u8, version: u32) ?Entry {
    for (entries) |e| {
        if (e.version == version and std.mem.eql(u8, e.name, name)) return e;
    }
    return null;
}
