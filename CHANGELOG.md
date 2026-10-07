# Changelog

All notable changes to si_dynamic. The format follows [Keep a Changelog](https://keepachangelog.com/), versions
follow [Semantic Versioning](https://semver.org/). Feature IDs refer to [FEATURES.md](FEATURES.md).

## [Unreleased]

## [0.2.0] - 2026-10-07

### Added

- AGENTS.md, FEATURES.md, README.md and this changelog.

## [0.1.0] - 2026-09-07

First release on crates.io. Reconstructed from git history.

### Added

- Pest grammar for SI base and derived units, all prefixes, exponents and superscripts (UNIT-1, UNIT-2, UNIT-3).
- `Quantity::parse`: number plus unit, `as_f32()` (NUM-1); unknown units as `BaseUnit::Named` (UNIT-4);
  `KNOWN_UNITS`.
- `OhmF32::parse` for resistance values like `4k7`, `499kR`, `12 kOhms` (RES-1).
- `SIExpr::parse` grammar for unit expressions (EXPR-1, not evaluated yet).
