# si_dynamic

Parse SI quantities and units from text at runtime.

```rust
use si_dynamic::{OhmF32, Prefix, BaseUnit, Quantity};

let q = Quantity::parse("4.7 uF")?;
assert_eq!(q.unit.prefix, Prefix::Micro);
assert_eq!(q.unit.base, BaseUnit::Farad);

let r = OhmF32::parse("4k7")?;   // 4700 Ω
```

All SI base and derived units and prefixes, exponents (`m^2`, `m²`), unknown units kept by name (`10mVDC`), and
the resistance shorthand used on schematics and BOMs (`4k7`, `499kR`, `12 kOhms`).

What works, known bugs and plans: [FEATURES.md](FEATURES.md). Changes: [CHANGELOG.md](CHANGELOG.md).

License: MIT.
