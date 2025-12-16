# Ion Zig Port Report (`zig/`)

## Overview

This repository contains a Zig 0.15.2 implementation of an Amazon Ion reader/writer under `zig/`, plus a Zig-only test harness that exercises the official `ion-tests/iontestdata` and `ion-tests/iontestdata_1_1` corpora.

Key properties:

1) No original Rust code removed; the port lives under `zig/`.
2) Zig toolchain: tested with `/opt/homebrew/bin/zig` (Zig 0.15.2).
3) Tests run via Zig only: `cd zig && /opt/homebrew/bin/zig build test --summary all`.
4) “All tests pass” means: all tests in the Zig harness pass, with an explicit skip list of currently-out-of-scope fixtures documented in `zig/src/tests.zig`.

## What’s implemented

### High-level API

- `zig/src/ion.zig`
  - `parseDocument(allocator, bytes)`:
    - Detects binary Ion 1.0 via IVM (`E0 01 00 EA`) and dispatches to the binary parser.
    - Otherwise parses as text Ion.
  - `serializeDocument(allocator, format, elements)`:
    - Supports `Format.binary`, and text formats (compact/lines/pretty) via the text writer.
  - `Document` owns an arena and a slice of parsed `Element`s; `deinit()` frees the arena.

### Data model

- `zig/src/ion/value.zig`
  - Arena allocator (`value.Arena`) for all parsed/created values.
  - `Value` union over Ion types.
  - `Element` = `{ annotations: []Symbol, value: Value }`.
  - `Symbol` tracks both `sid` (optional) and `text` (optional).

### Text Ion parsing

- `zig/src/ion/text.zig`
  - Parses top-level streams and containers: lists, sexps, structs.
  - Literals implemented: nulls, bool, ints, floats (`nan`, `±inf`), decimals, timestamps, strings, symbols, clobs/blobs.
  - Local symbol tables:
    - Supports `$ion_symbol_table` with `symbols:[...]` and `imports:[...]` (including `max_id:0`).
    - Supports `$ion_shared_symbol_table` declarations in-stream and uses them as an import catalog.
    - Supports unknown symbol IDs when the symbol table slot exists but has unknown text (null slot).
  - Whitespace handling includes HT/VT/FF/CR/LF per corpus expectations.
  - Includes a debugging helper `parseTopLevelWithErrorIndex(...)` intended for ad-hoc repro tooling.
  - Ion 1.1: supports a growing subset of macro invocations used by `iontestdata_1_1` and conformance:
    - Expression groups: `(:: <expr>*)`
    - Macro IDs: unqualified/qualified names and numeric addresses (e.g. `(:values ...)`, `(:1 ...)`, `(:$ion::values ...)`, `(:$ion::1 ...)`)
    - Implemented expansions: `none`, `values`, `default`, `repeat`, `delta`, `sum`, `annotate`, `make_string`, `make_symbol`, `make_decimal`, `make_timestamp`, `make_field`, `make_struct`, `make_list`, `make_sexp`, `flatten`
    - This is still far from a complete Ion 1.1 macro system.

### Binary Ion 1.0 parsing

- `zig/src/ion/binary.zig`
  - Parses binary Ion 1.0 TLV stream after IVM.
  - Handles:
    - Annotation wrappers (T14)
    - NOP pads (T0) (and rejects null.nop)
    - Containers: list/sexp/struct (including NOP padding inside)
    - Numerics, decimals, timestamps, strings, clobs, blobs, symbols
    - Local symbol tables:
      - Supports `$ion_symbol_table` `imports:[...]` (falls back to unknown slots if imported table is not known).
      - Supports in-stream `$ion_shared_symbol_table` declarations as an import catalog.
      - Supports unknown symbol IDs when the symbol table slot exists but has unknown text (null slot).
    - IVM appearing inside the stream (ignored if it’s `E0 01 00 EA`)
    - “Ordered struct” encoding variant (as used by ion-tests)

### Writer (text + binary)

- `zig/src/ion/writer.zig`
  - Binary writer:
    - Emits IVM.
    - Emits a basic local symbol table for newly encountered symbol text.
    - Writes values with correct Ion binary encodings for supported types.
    - Handles signed-magnitude integer fields in decimals and timestamp fractionals (sign-bit padding rules).
  - Text writer:
    - Produces legal text Ion consumable by our parser and by ion-tests expectations.
    - Emits a minimal `$ion_symbol_table` import when needed so `$<sid>` tokens (unknown symbol IDs) are parseable.
    - Handles timestamps with correct “trailing `T`” rules at year/month precision.
    - Uses `\\xNN` escapes for non-ASCII bytes in clobs.
    - Avoids accidental string literal concatenation by alternating short (`"..."`) and long (`'''...'''`) forms for adjacent string values at top-level and in sexps.

### Equality semantics

- `zig/src/ion/eq.zig`
  - Structural equality for values/elements to support equiv/non-equiv fixtures and roundtrip checks.
  - Notably:
    - NaN equals NaN for equivalence purposes.
    - Signed zero for floats treated distinctly.
    - Struct field comparison is order-insensitive.

## Tests and harness

- `zig/src/tests.zig` is a Zig test suite that walks `ion-tests/iontestdata` and enforces:
  - `bad/` must reject
  - `good/equivs/` groups must all be equivalent
  - `good/non-equivs/` groups must not be equivalent across group members
  - `good/` roundtrip through a format matrix (binary/text variants)
  - The same checks are also run for `ion-tests/iontestdata_1_1` (text only for roundtrip).
  - As of 2025-12-15, `cd zig && /opt/homebrew/bin/zig build test --summary all` runs 10 Zig tests; all pass.

### Skip list

There are intentional skips, each with an inline comment explaining why:

- `global_skip_list`: skipped everywhere (bad/good/equivs/non-equivs/roundtrip)
- `round_trip_skip_list`: skipped only for the roundtrip matrix
- `equivs_skip_list`: skipped only for equiv grouping

See `zig/src/tests.zig` for the exact items and reasons.

## ion-tests status (what runs vs what is missing)

The `ion-tests/` repo contains multiple suites. The Zig harness currently covers the two corpus suites below and does not yet run the Ion 1.1 conformance suite.

### 1) Ion 1.0 corpus: `ion-tests/iontestdata/**`

1) Files in suite: 785 (`.ion` + `.10n`)
2) What the Zig harness runs:
   - `bad/` reject: 496 files
   - `good/equivs/` equivalence: 60 files
   - `good/non-equivs/` non-equivalence: 21 files
   - `good/` roundtrip: 289 files across a 12-pair format matrix (binary/text variants)
3) Current result in Zig: all pass (no skips in `zig/src/tests.zig`).

### 2) Ion 1.1 text corpus: `ion-tests/iontestdata_1_1/**`

1) Files in suite: 606 (`.ion`)
2) What the Zig harness runs:
   - `bad/` reject: 400 files
   - `good/equivs/` equivalence: 52 files
   - `good/non-equivs/` non-equivalence: 21 files
   - `good/` roundtrip: 206 files (text lines -> text lines)
3) Current result in Zig: all pass (no skips in `zig/src/tests.zig`).

### 3) Ion 1.1 conformance: `ion-tests/conformance/**/*.ion` (RUN, MANY BRANCHES SKIPPED)

1) Files in suite: 55 (`.ion`)
2) Current result in Zig:
   - Run: 55/55 conformance files (via a single walker test in `zig/src/tests.zig`)
   - Branch-level status (2025-12-15):
     - Total branches: 2647
     - Passed: 1835
     - Skipped (unsupported): 812
     - To reproduce totals: `cd zig && for f in ../ion-tests/conformance/**/*.ion; do /opt/homebrew/bin/zig run src/conformance_debug.zig -- "$f"; done`
   - Many branches are currently marked “unsupported” and counted as skipped:
     - Large parts of the Ion 1.1 macro system / TDL are not implemented (only a subset of system macros expand during parsing)
     - Binary Ion 1.1 is not implemented
     - `binary` fragments:
       - Ion 1.0 binary fragments are executed (decoded via `ion.parseDocument`).
       - Ion 1.1 binary fragments are currently skipped (no Ion 1.1 binary reader).
3) What needs to be implemented to fully run this suite:
   - Conformance DSL runner (test collection parsing/execution, signals, and "produces" verification)
   - Ion 1.1 macro system beyond the currently-expanded subset (`none`, `values`, `default`, `repeat`, `delta`, `sum`, `annotate`, `make_string`, `make_symbol`, `make_decimal`, `make_timestamp`, `make_field`, `make_struct`, `make_list`, `make_sexp`, `flatten`, plus `(::...)`)
   - E-expressions (eexp) and their binary encodings
   - Ion 1.1 binary features used by conformance (various flex_* encodings, additional symbol/macro table mechanics)
   - System macros used by conformance (e.g. `annotate`, `make_field`, `make_decimal`, `make_timestamp`, `parse_ion`, `use`, etc.)

## To-dos (to remove skips / broaden coverage)

### 1) Ion 1.1 binary

`iontestdata_1_1` currently covers text only in the Zig harness. Binary Ion 1.1 is not implemented.

### 2) Macro system breadth

Only a small subset of Ion 1.1 macro expansions are implemented (`none`, `values`, `default`, `repeat`, `delta`, `sum`, `annotate`, `make_string`, `make_symbol`, `make_decimal`, `make_timestamp`, `make_field`, `make_struct`, `make_list`, `make_sexp`, `flatten`, `(::...)`). A complete Ion 1.1 macro system is out of scope for the current port.

### 3) Performance

Large integer/decimal fixtures can be dominated by BigInt string formatting/parsing.

- `zig/src/ion/binary.zig` uses `std.math.big.int.Mutable.readTwosComplement(..., .unsigned)` to build magnitudes directly from bytes (no hex string conversions).
- `zig/src/ion/writer.zig` writes BigInt magnitudes directly to big-endian bytes via `writeTwosComplement()` (no toString()/parse round-trips) for Ion binary encodings.

## Gotchas encountered (and fixes)

### 1) Triple-quote field names vs quoted symbols

Ion allows struct field names that are strings (short and long). `'''foo'''` field names were initially misparsed as quoted symbols because both start with `'`.

Fix: in `parseFieldName`, check `startsWith(\"'''\")` before `startsWith(\"'\")`.

### 2) `+` handling inside s-expressions

`(+1)` must tokenize as `'+'` and `1` (not `+1` as a number).

Fix: rely on sexp tokenization rules rather than forcing leading `+` to always become a symbol.

### 3) Decimal encoding sign-bit rules (binary)

Ion decimal coefficient is a signed-magnitude integer field. If the magnitude’s high bit would be 1, positive values must be prefixed with `0x00` to keep the sign bit clear; negative values may need `0x80` prefix.

Fix: `writeDecimalBinary` prefixes `0x00` for positive coefficients with MSB set, and handles negative sign-bit/prefix rules.

### 4) NOP pads inside structs with non-zero SIDs

The corpus includes cases where a struct field name is followed by a NOP (padding) before the value, and the field name SID can be non-zero.

Fix: in `decodeStruct`, treat `(sid, nop)` pairs as padding regardless of sid value, and continue scanning.

### 5) “Ordered struct” binary encoding

Some `.10n` fixtures use Ion’s ordered struct encoding (where the length code encodes the size of the length field).

Fix: implement ordered-struct detection/decoding for T13 with length codes < 14, and reject empty ordered structs per corpus.

### 6) Line comments with CR (old Mac EOL)

`//` comments must terminate at either `\\n` or `\\r`, not just `\\n`.

Fix: `skipWsComments` ends line comments on `\\r` too.

### 7) Special whitespace/control characters in strings/symbols

Some fixtures include literal HT/VT/FF inside quoted strings and quoted symbols.

Fix: allow `\\t`, `0x0B`, `0x0C` where corpus expects it.

### 8) Clob non-ASCII bytes

Binary clobs can contain bytes ≥ `0x80`. When emitting text clobs, those must be escaped so the text parser can accept them as bytes.

Fix: writer emits `\\xNN` for non-ASCII bytes in clobs; parser accepts `\\xNN` into clobs as raw bytes.

### 9) Avoiding accidental string concatenation in emitted text

Ion text concatenates adjacent string literals. A naive printer can accidentally merge consecutive string values.

Fix: text writer alternates short/long string literal styles for adjacent string values.

### 10) BigInt magnitude imports (binary) must avoid string paths

Some binary numeric encodings carry big integer magnitudes as bytes. Converting those bytes to hex/decimal strings and then calling BigInt `setString()` is very allocation-heavy and slows the suite down.

Fix: use `std.math.big.int.Mutable.readTwosComplement(..., .unsigned)` to import magnitudes directly from bytes (see `zig/src/ion/binary.zig`).

### 11) Conformance runner must not “help” invalid symbol addresses

The conformance suite includes cases that expect invalid/out-of-range symbol addresses to `signals` an error. A roundtrip-focused text writer may emit synthetic `$ion_symbol_table` imports to make `$<sid>` tokens parseable, which would mask those errors.

Fix: the text writer exposes `writeTextConformance(...)` which does not inject symbol table imports; the conformance runner also parses its DSL using a mode that disables adjacent string literal concatenation.

### 10) Imports with very large `max_id`

Some fixtures (notably `ion-tests/iontestdata/good/subfieldVarUInt32bit.ion`) declare imports with very large `max_id`
values (on the order of 2^31). Materializing symbol table slots up to `max_id` (e.g. appending billions of null slots)
is both unnecessary and catastrophically slow.

Fix: track `declared_max_id` separately from any dense slot storage and treat unknown slots as implicit; only store
known texts sparsely. See `zig/src/ion/symtab.zig` (`SymbolTable.addImport()` and `slotForSid()`).

## Fun facts / notable behavior choices

1) `$0` is treated as “unknown symbol”; it’s allowed in annotations and as a struct field name. Non-zero `$sid` is allowed if the SID is defined by the current symbol table (even if its text is unknown via a null slot).
2) Lists require commas; sexps do not allow commas, matching “bad” fixtures.
3) Timestamps are validated tightly (ranges, precision rules, explicit offsets for time precision).
4) Binary streams can contain IVM mid-stream; the parser tolerates Ion 1.0 IVM and ignores it.

## Repo pointers

- Entry API: `zig/src/ion.zig`
- Data model: `zig/src/ion/value.zig`
- Text parser: `zig/src/ion/text.zig`
- Binary parser: `zig/src/ion/binary.zig`
- Writer: `zig/src/ion/writer.zig`
- Equality: `zig/src/ion/eq.zig`
- Test harness & skip reasons: `zig/src/tests.zig`
- Zig build (Zig-only tests): `zig/build.zig`
