//! Ion structural equality helpers.
//!
//! Used by the Zig `ion-tests` harness to validate:
//! - equiv/non-equiv group semantics
//! - roundtrip equivalence across formats
//!
//! Notable semantics:
//! - NaN compares equal to NaN.
//! - Signed zero for floats is treated as distinct.
//! - Struct field comparison is order-insensitive.

const std = @import("std");
const value = @import("value.zig");

pub fn ionEqInt(a: value.Int, b: value.Int) bool {
    return switch (a) {
        .small => |ai| switch (b) {
            .small => |bi| ai == bi,
            .big => |bb| blk: {
                const bi = bb.toConst().toInt(i128) catch break :blk false;
                break :blk ai == bi;
            },
        },
        .big => |aa| switch (b) {
            .small => |bi| blk: {
                const ai = aa.toConst().toInt(i128) catch break :blk false;
                break :blk ai == bi;
            },
            .big => |bb| aa.eql(bb),
        },
    };
}

/// Symbol equality: compares by `text` when available, otherwise by SID presence/value.
pub fn ionEqSymbol(a: value.Symbol, b: value.Symbol) bool {
    if (a.text != null and b.text != null) return std.mem.eql(u8, a.text.?, b.text.?);
    if (a.text == null and b.text == null) {
        if (a.sid != null and b.sid != null) return a.sid.? == b.sid.?;
        return a.sid == b.sid;
    }
    return false;
}

/// Float equality for Ion equivalence checks (NaN==NaN; signed zero distinguished).
pub fn ionEqF64(a: f64, b: f64) bool {
    if (std.math.isNan(a)) return std.math.isNan(b);
    if (a == 0.0 and b == 0.0) {
        // signed zero matters
        return std.math.signbit(a) == std.math.signbit(b);
    }
    return a == b;
}

/// Decimal equality (representation-sensitive).
pub fn ionEqDecimal(a: value.Decimal, b: value.Decimal) bool {
    return a.is_negative == b.is_negative and ionEqInt(a.coefficient, b.coefficient) and a.exponent == b.exponent;
}

/// Timestamp equality (representation-sensitive for stored fields).
pub fn ionEqTimestamp(a: value.Timestamp, b: value.Timestamp) bool {
    return a.year == b.year and
        a.month == b.month and
        a.day == b.day and
        a.hour == b.hour and
        a.minute == b.minute and
        a.second == b.second and
        (if (a.fractional == null and b.fractional == null) true else if (a.fractional == null or b.fractional == null) false else ionEqDecimal(a.fractional.?, b.fractional.?)) and
        a.offset_minutes == b.offset_minutes and
        a.precision == b.precision;
}

/// Value equality for Ion equivalence checks.
pub fn ionEqValue(a: value.Value, b: value.Value) bool {
    if (@as(value.IonType, a) != @as(value.IonType, b)) return false;
    return switch (a) {
        .null => |t| t == b.null,
        .bool => |v| v == b.bool,
        .int => |v| ionEqInt(v, b.int),
        .float => |v| ionEqF64(v, b.float),
        .decimal => |v| ionEqDecimal(v, b.decimal),
        .timestamp => |v| ionEqTimestamp(v, b.timestamp),
        .symbol => |v| ionEqSymbol(v, b.symbol),
        .string => |v| std.mem.eql(u8, v, b.string),
        .clob => |v| std.mem.eql(u8, v, b.clob),
        .blob => |v| std.mem.eql(u8, v, b.blob),
        .list => |v| ionEqElements(v, b.list),
        .sexp => |v| ionEqElements(v, b.sexp),
        .@"struct" => |v| ionEqStruct(v, b.@"struct"),
    };
}

/// Element equality: compares annotations (order-sensitive) and values.
pub fn ionEqElement(a: value.Element, b: value.Element) bool {
    if (a.annotations.len != b.annotations.len) return false;
    for (a.annotations, b.annotations) |aa, bb| {
        if (!ionEqSymbol(aa, bb)) return false;
    }
    return ionEqValue(a.value, b.value);
}

/// Slice equality for sequences (order-sensitive).
pub fn ionEqElements(a: []const value.Element, b: []const value.Element) bool {
    if (a.len != b.len) return false;
    for (a, b) |ea, eb| {
        if (!ionEqElement(ea, eb)) return false;
    }
    return true;
}

fn ionEqStructFields(a_fields: []const value.StructField, b_fields: []const value.StructField) bool {
    // Implement the same logic as ion-rust's Struct::fields_eq with a reverse check.
    // For each field name in a, b must have same count and contain IonEq equivalents.
    var i: usize = 0;
    while (i < a_fields.len) : (i += 1) {
        const name = a_fields[i].name;
        var a_count: usize = 0;
        var b_count: usize = 0;
        // Count occurrences.
        for (a_fields) |f| {
            if (ionEqSymbol(f.name, name)) a_count += 1;
        }
        for (b_fields) |f| {
            if (ionEqSymbol(f.name, name)) b_count += 1;
        }
        if (a_count != b_count) return false;

        // For each a value with this name, find any b value with this name that is IonEq.
        for (a_fields) |af| {
            if (!ionEqSymbol(af.name, name)) continue;
            var found = false;
            for (b_fields) |bf| {
                if (!ionEqSymbol(bf.name, name)) continue;
                if (ionEqElement(af.value, bf.value)) {
                    found = true;
                    break;
                }
            }
            if (!found) return false;
        }
    }
    return true;
}

/// Struct equality: compares fields as an order-insensitive multiset.
pub fn ionEqStruct(a: value.Struct, b: value.Struct) bool {
    if (a.fields.len != b.fields.len) return false;
    return ionEqStructFields(a.fields, b.fields) and ionEqStructFields(b.fields, a.fields);
}
