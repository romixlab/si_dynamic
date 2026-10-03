# si_dynamic features and roadmap

This file is the single source of truth for what si_dynamic does, what is broken and what is planned, for humans
and AI agents alike. [CHANGELOG.md](CHANGELOG.md) records what changed and when; this file records the current
state.

Last full review: 3 Oct 2026 (commit `b14b5aa`, 0.1.0). Built from the code and the tests; the bugs marked
*(verified 3 Oct 2026)* were reproduced with a throwaway test on that date.

## How to use this file

- **Status** of each item:
  - ✅ done
  - 🚧 in progress or partially done (the note says what is missing)
  - 🐛 implemented, but with known bugs
  - ⬜ stub: types or API exist but do nothing yet
  - 📋 planned
  - 💡 idea, not committed to
  - ⛔ blocked (the note says on what)
  - 🔍 probably done or obsolete, needs a check before closing
- **IDs** (`UNIT-2`, `NUM-3`) are stable: never renumber or reuse one. New items take the next free number of their
  area. Use the ID in commit messages, CHANGELOG entries and code `TODO`s (`// TODO(EXPR-1): ...`).
- Items are grouped by area. Each area lists what works first, then open items by priority.
- When finishing work, update the item in the same commit: mark it ✅, add a pointer (function, grammar rule,
  test) and move it up to the done items of its area. Don't delete done items. Items that turn out obsolete go to
  [Dropped and superseded](#dropped-and-superseded) with a one-line reason.
- A bug you find but don't fix gets an entry (🐛 on the feature, or a new item) with the input that triggers it.
- Small code-level gaps stay as `TODO` comments; only those that limit users or block a feature get an item.

## Units and prefixes (`UNIT`)

- ✅ **UNIT-1 SI base and derived units**: the 7 base units and 22 derived ones (`BaseUnit`, `KNOWN_UNITS`), each
  with `name()`, `symbol()` and dimension vector `exp()` (`SIExp`).
- ✅ **UNIT-2 All SI prefixes**: quecto to quetta, `u` / `μ` / `µ` for micro, `k` / `K` for kilo. Look-ahead in the
  grammar keeps `m` (meter) apart from `mV`.
- ✅ **UNIT-3 Unit exponents**: `m^2`, superscripts `m²`, `s⁻¹` (exponent fits in `i8`).
- ✅ **UNIT-4 Unknown units**: any identifier parses as `BaseUnit::Named` (`10mVDC` → milli + `VDC`), with an empty
  symbol and a zero dimension vector.
- ✅ **UNIT-5 Serde**: `Unit`, `BaseUnit`, `Prefix`, `SIExp`, `Quantity` derive `Serialize` / `Deserialize`.
- 🐛 **UNIT-6 Gram handled as kilogram**: `g` maps to `BaseUnit::Kilogram` without adjusting the prefix, so
  `10 g` gives 10 kg and `10 kg` becomes `kkg` with value 10000 *(verified 3 Oct 2026)*. Needs a gram base with
  kilogram as the SI base, or the prefix shifted by -3 on parse.
- 🐛 **UNIT-7 Degree Celsius only standalone**: `°C` can't take a prefix or exponent and has no offset handling
  against kelvin.
- 📋 **UNIT-8 Superscript exponents in `Display`**: `Unit` prints `m^2` instead of `m²` (TODO in `Display for
  Unit`). Check rvariant's round-trip tests when changing it.
- 💡 **UNIT-9 Named units with dimensions**: let callers register `Named` units with a symbol and a dimension
  vector (`VDC` = volt), so conversions between them work.

## Numbers and quantities (`NUM`)

- ✅ **NUM-1 `Quantity::parse`**: number plus optional unit, spaces optional (`10V`, `4.7 uF`, ` 10 V `). Keeps the
  number as text, `as_f32()` applies the prefix.
- ✅ **NUM-2 Unicode minus** (`−`, U+2212) and `-` for negative numbers.
- 🐛 **NUM-3 Prefix not raised to the exponent**: `Quantity::as_f32` multiplies by the prefix once, so `1 km^2`
  gives 1000 instead of 1e6 *(verified 3 Oct 2026)*.
- 🐛 **NUM-4 Exponent notation without a unit**: `Quantity::parse("1e3")` fails with `Internal("expected unit")`;
  `2.5e-3 V` works *(verified 3 Oct 2026)*.
- 📋 **NUM-5 `f64` and exact values**: only `as_f32` exists. Add `as_f64` and keep integer values exact for callers
  that need them (rvariant converts between number types).
- 📋 **NUM-6 Error messages**: `Error::Internal` strings name grammar rules (`"expected simple_number"`), not what
  was wrong with the input. Give users a message they can act on, with the position.

## Resistance (`RES`)

- ✅ **RES-1 `OhmF32::parse`**: plain numbers, prefixes as decimal point (`4k7`, `1k2`), `R` / `r` / `Ω` / `Ohm` /
  `Ohms`, prefixes `k M G T m u n` with or without the unit (`5k`, `499kR`, `12 kOhms`, `1 mΩ`).
- 🐛 **RES-2 Exponents in resistance**: `OhmF32::parse("1e3")`, `"1.5e3"` and `"2e-3"` fail with
  `Internal("simple_number")` *(verified 3 Oct 2026)*. `parse_any_number_f32` reads the exponent from the wrong
  pair, and negative exponents are rejected by the `u32` conversion.

## Unit expressions (`EXPR`)

- ⬜ **EXPR-1 `SIExpr::parse`**: the grammar parses `10*V/us`, `10 V/us`, parentheses, `*` / `⋅` / `/`, but the
  function prints the parse tree with `println!` and returns `SIExpr::Num("")`. `Quantity::parse("1 m/s")` fails.
- 📋 **EXPR-2 Dimension check**: reduce an expression to an `SIExp` and compare units by dimension (`V/A` = `Ω`),
  for conversions in rvariant.

## Project (`PRJ`)

- ✅ **PRJ-1 Published on crates.io** (0.1.0).
- 📋 **PRJ-2 README and docs**: crate-level docs with examples of accepted inputs; doc comments on the public
  types.
- 📋 **PRJ-3 Tests**: 5 unit tests (`src/lib.rs`), `expr()` is all commented out. Add tests for every bug above
  before fixing it, and a table test of accepted / rejected inputs.

## Dropped and superseded

(none yet)
