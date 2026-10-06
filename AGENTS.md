# Working on si_dynamic

Guidance for AI agents and contributors. Read this before changing code.

si_dynamic parses SI quantities and units from text at runtime: `4.7 uF`, `10mV`, `4k7` (resistance), units with
prefixes and exponents, and (planned) unit expressions like `m/s²`. Published on crates.io. Its main user is
rvariant (`Variant::SI`), and through it egui_tabular and mx3, where it parses component parameters typed by people
or imported from CSV and supplier data, so lenient input and exact results both matter.

## FEATURES.md is the source of truth

[FEATURES.md](FEATURES.md) lists every feature with its status, every known bug, and what is planned, with stable
IDs per area (`UNIT-2`, `NUM-3`, ...).

- **Read the relevant area before starting.** Several known bugs are recorded with the input that triggers them.
- **Name IDs with a short slug when talking to the user** (answers, plans, summaries, tables):
  `UNIT-6 gram-prefix`, never a bare `UNIT-6`. The slug is 2-4 kebab-case words from the item's title. Commit
  messages, CHANGELOG and code `TODO`s keep the bare ID.
- **Update it in the same commit** as the code: mark items ✅/🚧/🐛 with a pointer to the code, add bugs you find
  but don't fix (next free ID of the area), move obsolete items to *Dropped and superseded*. Never renumber or
  reuse IDs.
- Don't track status anywhere else (README checklists, TODO files). Code `TODO`s that matter reference an ID:
  `// TODO(EXPR-1): ...`.

## CHANGELOG.md records every change

[CHANGELOG.md](CHANGELOG.md) is the history, FEATURES.md the current state; keep both.

- Every change a user of the crate would notice gets an entry under `## [Unreleased]` in the same commit:
  `### Added`, `### Changed`, `### Fixed`, `### Removed`. Short, with the feature ID in parentheses. Mark API
  breaks with **Breaking:**, and say when an input now parses to a different value.
- Pure refactors and typo fixes don't need an entry.
- A commit that bumps the version (see *Versions*) moves the `[Unreleased]` entries under a new
  `## [x.y.z] - YYYY-MM-DD` heading and leaves `[Unreleased]` empty, so every version has its own section.
- Questions like "what's new" or "what changed since X" are answered from CHANGELOG.md, newest sections first
  (the user's version or date as the cutoff), with FEATURES.md for current status.

The tpm repo's `/sync-repos` reads this file to log progress, so a missing entry means work nobody sees.

## Layout

One crate.

- `grammar/si.pest` — the pest grammar: units, prefixes, numbers, superscripts, the special resistance syntax.
  Prefix rules use look-ahead (`&("k" ~ ident)`) so `m` alone is meter and `mV` is milli-volt; the
  `*_unconditional` variants are for resistance (`4k7`).
- `src/lib.rs` — `BaseUnit` (SI base and derived units plus `Named` for anything else), `Unit` (prefix, base,
  exponent), `SIExp` (dimension vector), `Prefix`, `Quantity::parse`, `OhmF32::parse`, `SIExpr::parse` (stub),
  tests at the bottom.

rvariant (`../rvariant/src/si.rs`) is the main consumer. After an API or behaviour change, build and test
rvariant against this checkout (it takes si_dynamic by path) and say what it needs to follow.

## Commands

```sh
cargo build
cargo clippy --all-targets -- -D warnings
cargo fmt
cargo test
cd ../rvariant && cargo test --all-features   # main downstream user
```

Before declaring a change done: build, clippy without warnings, fmt, tests, and rvariant's tests.

## Code conventions

- Parse errors are `Error` values, never panics: no `unwrap`/`expect` on input-derived data, no `println!` left in
  library code.
- A new accepted spelling goes into the grammar and a test in the same commit. Check it doesn't change how an
  existing input parses (prefix look-ahead makes this easy to break: `m`, `T`, `G`, `R`).
- Don't lose precision silently: keep the number text in `Quantity`, convert at the edge.

## Tests

Unit tests in `src/lib.rs` (`mod tests`), one per kind of input, asserting prefix, base, exponent and value. A bug
fix starts with a failing test with the exact input that misbehaves.

## Commits

Conventional Commits: `feat: ...`, `fix: ...`, `refactor: ...`, `build: ...`. Short imperative summary, blank
line, body with what and why; reference feature IDs (`fix: gram prefix no longer doubles to kkg (UNIT-6)`).

Never commit on your own initiative. When a change is done, update FEATURES.md and CHANGELOG.md, then show the
proposed commit message and the files to stage, and ask. Approval covers that one commit only. Never push or
publish; the user's tooling does that.

## Versions

Every commit with real work bumps the version in the same commit (manifest + CHANGELOG entry), so any build
traces back to a commit:
- Patch for fixes and small changes, minor for features or anything breaking before 1.0, major only when the
  owner says so. In a workspace, only the crates that changed.
- Docs-only, CI-only and no-behaviour-change refactors skip it; a burst of follow-up fixes shares one bump.
- CLIs print version, git SHA and build time in `--version`, e.g. `tool 0.4.2 (a1b2c3d-dirty, built 3 Oct 2026
  18:20)`: a small `build.rs` without extra crates (`git rev-parse --short HEAD`, `-dirty` when
  `git status --porcelain` isn't empty, `rerun-if-changed` on `.git/HEAD` and `.git/index`, `unknown` without
  git). Firmware reports the same through `fw_info`. When touching a CLI that lacks it, add it.
