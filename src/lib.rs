use pest::Parser;
use pest::iterators::Pair;
use pest_derive::Parser;
use serde::{Deserialize, Serialize};
use std::fmt::{Display, Formatter};
use std::num::{ParseFloatError, ParseIntError};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum BaseUnit {
    Second,
    Meter,
    Kilogram,
    Ampere,
    Kelvin,
    Mole,
    Candela,

    Radian,
    Steradian,
    Hertz,
    Newton,
    Pascal,
    Joule,
    Watt,
    Coulomb,
    Volt,
    Farad,
    Ohm,
    Siemens,
    Weber,
    Tesla,
    Henry,
    DegreeCelsius,
    Lumen,
    Lux,
    Becquerel,
    Gray,
    Sievert,
    Katal,
    Named {
        name: String,
        symbol: String,
        exp: SIExp,
    },
    Unitless,
    // NamedStatic {
    //     name: &'static str,
    //     symbol: &'static str,
    //     exp: SIExp,
    // },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Unit {
    pub prefix: Prefix,
    pub base: BaseUnit,
    pub exp: i8,
}

impl Unit {
    pub fn unit() -> Self {
        Unit {
            prefix: Prefix::Unit,
            base: BaseUnit::Unitless,
            exp: 1,
        }
    }

    pub fn base(base: BaseUnit) -> Self {
        Unit {
            prefix: Prefix::Unit,
            base,
            exp: 1,
        }
    }
}

impl Display for Unit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.exp == 1 {
            write!(f, "{}{}", self.prefix, self.base)
        } else {
            // TODO: use superscript
            write!(f, "{}{}^{}", self.prefix, self.base, self.exp)
        }
    }
}

pub const KNOWN_UNITS: [BaseUnit; 7 + 22] = [
    BaseUnit::Second,
    BaseUnit::Meter,
    BaseUnit::Kilogram,
    BaseUnit::Ampere,
    BaseUnit::Kelvin,
    BaseUnit::Mole,
    BaseUnit::Candela,
    BaseUnit::Radian,
    BaseUnit::Steradian,
    BaseUnit::Hertz,
    BaseUnit::Newton,
    BaseUnit::Pascal,
    BaseUnit::Joule,
    BaseUnit::Watt,
    BaseUnit::Coulomb,
    BaseUnit::Volt,
    BaseUnit::Farad,
    BaseUnit::Ohm,
    BaseUnit::Siemens,
    BaseUnit::Weber,
    BaseUnit::Tesla,
    BaseUnit::Henry,
    BaseUnit::DegreeCelsius,
    BaseUnit::Lumen,
    BaseUnit::Lux,
    BaseUnit::Becquerel,
    BaseUnit::Gray,
    BaseUnit::Sievert,
    BaseUnit::Katal,
];

impl BaseUnit {
    pub fn exp(&self) -> SIExp {
        match self {
            BaseUnit::Second => SIExp::new_reduced(0, 0, 1, 0),
            BaseUnit::Meter => SIExp::new_reduced(1, 0, 0, 0),
            BaseUnit::Kilogram => SIExp::new_reduced(0, 1, 0, 0),
            BaseUnit::Ampere => SIExp::new_reduced(0, 0, 0, 1),
            BaseUnit::Kelvin => SIExp::new(0, 0, 0, 0, 1, 0, 0),
            BaseUnit::Mole => SIExp::new(0, 0, 0, 0, 0, 1, 0),
            BaseUnit::Candela => SIExp::new(0, 0, 0, 0, 0, 0, 1),
            BaseUnit::Radian => SIExp::new_reduced(0, 0, 0, 0),
            BaseUnit::Steradian => SIExp::new_reduced(0, 0, 0, 0),
            BaseUnit::Hertz => SIExp::new_reduced(0, 0, -1, 0),
            BaseUnit::Newton => SIExp::new_reduced(1, 1, -2, 0),
            BaseUnit::Pascal => SIExp::new_reduced(-1, 1, -2, 0),
            BaseUnit::Joule => SIExp::new_reduced(2, 1, -2, 0),
            BaseUnit::Watt => SIExp::new_reduced(2, 1, -3, 0),
            BaseUnit::Coulomb => SIExp::new_reduced(0, 0, 1, 1),
            BaseUnit::Volt => SIExp::new_reduced(2, 1, -3, -1),
            BaseUnit::Farad => SIExp::new_reduced(-2, -1, 4, 2),
            BaseUnit::Ohm => SIExp::new_reduced(2, 1, -3, -2),
            BaseUnit::Siemens => SIExp::new_reduced(-2, -1, 3, 2),
            BaseUnit::Weber => SIExp::new_reduced(2, 1, -2, -1),
            BaseUnit::Tesla => SIExp::new_reduced(0, 1, -2, -1),
            BaseUnit::Henry => SIExp::new_reduced(2, 1, -2, -2),
            BaseUnit::DegreeCelsius => SIExp::new(0, 0, 0, 0, 1, 0, 0),
            BaseUnit::Lumen => SIExp::new(0, 0, 0, 0, 0, 0, 1),
            BaseUnit::Lux => SIExp::new(-2, 0, 0, 0, 0, 0, 1),
            BaseUnit::Becquerel => SIExp::new_reduced(0, 0, -1, 0),
            BaseUnit::Gray => SIExp::new_reduced(2, 0, -2, 0),
            BaseUnit::Sievert => SIExp::new_reduced(2, 0, -2, 0),
            BaseUnit::Katal => SIExp::new(0, 0, -1, 0, 0, 1, 0),
            BaseUnit::Named { exp, .. } => *exp,
            // SIUnit::NamedStatic { exp, .. } => *exp,
            BaseUnit::Unitless => SIExp::new_reduced(0, 0, 0, 0),
        }
    }

    pub fn name(&self) -> &str {
        match self {
            BaseUnit::Second => "Second",
            BaseUnit::Meter => "Meter",
            BaseUnit::Kilogram => "Kilogram",
            BaseUnit::Ampere => "Ampere",
            BaseUnit::Kelvin => "Kelvin",
            BaseUnit::Mole => "Mole",
            BaseUnit::Candela => "Candela",
            BaseUnit::Radian => "Radian",
            BaseUnit::Steradian => "Steradian",
            BaseUnit::Hertz => "Hertz",
            BaseUnit::Newton => "Newton",
            BaseUnit::Pascal => "Pascal",
            BaseUnit::Joule => "Joule",
            BaseUnit::Watt => "Watt",
            BaseUnit::Coulomb => "Coulomb",
            BaseUnit::Volt => "Volt",
            BaseUnit::Farad => "Farad",
            BaseUnit::Ohm => "Ohm",
            BaseUnit::Siemens => "Siemens",
            BaseUnit::Weber => "Weber",
            BaseUnit::Tesla => "Tesla",
            BaseUnit::Henry => "Henry",
            BaseUnit::DegreeCelsius => "Degree Celsius",
            BaseUnit::Lumen => "Lumen",
            BaseUnit::Lux => "Lux",
            BaseUnit::Becquerel => "Becquerel",
            BaseUnit::Gray => "Gray",
            BaseUnit::Sievert => "Sievert",
            BaseUnit::Katal => "Katal",
            BaseUnit::Named { name, .. } => name.as_str(),
            BaseUnit::Unitless => "Unitless",
        }
    }

    pub fn symbol(&self) -> &str {
        match self {
            BaseUnit::Second => "s",
            BaseUnit::Meter => "m",
            BaseUnit::Kilogram => "kg",
            BaseUnit::Ampere => "A",
            BaseUnit::Kelvin => "K",
            BaseUnit::Mole => "mol",
            BaseUnit::Candela => "cd",
            BaseUnit::Radian => "rad",
            BaseUnit::Steradian => "sr",
            BaseUnit::Hertz => "Hz",
            BaseUnit::Newton => "N",
            BaseUnit::Pascal => "Pa",
            BaseUnit::Joule => "J",
            BaseUnit::Watt => "W",
            BaseUnit::Coulomb => "C",
            BaseUnit::Volt => "V",
            BaseUnit::Farad => "F",
            BaseUnit::Ohm => "Ω",
            BaseUnit::Siemens => "S",
            BaseUnit::Weber => "Wb",
            BaseUnit::Tesla => "T",
            BaseUnit::Henry => "H",
            BaseUnit::DegreeCelsius => "°C",
            BaseUnit::Lumen => "lm",
            BaseUnit::Lux => "lx",
            BaseUnit::Becquerel => "Bq",
            BaseUnit::Gray => "Gy",
            BaseUnit::Sievert => "Sv",
            BaseUnit::Katal => "kat",
            BaseUnit::Named { name, .. } => name.as_str(),
            // SIUnit::NamedStatic { name, .. } => name,
            BaseUnit::Unitless => "()",
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SIExp(pub [i8; 7]);

impl SIExp {
    pub const fn new(
        meter: i8,
        kilogram: i8,
        second: i8,
        ampere: i8,
        kelvin: i8,
        mole: i8,
        candela: i8,
    ) -> Self {
        SIExp([meter, kilogram, second, ampere, kelvin, mole, candela])
    }

    pub const fn new_reduced(meter: i8, kilogram: i8, second: i8, ampere: i8) -> Self {
        SIExp([meter, kilogram, second, ampere, 0, 0, 0])
    }

    pub fn meter(&self) -> i8 {
        self.0[0]
    }

    pub fn kilogram(&self) -> i8 {
        self.0[1]
    }

    pub fn second(&self) -> i8 {
        self.0[2]
    }

    pub fn ampere(&self) -> i8 {
        self.0[3]
    }

    pub fn kelvin(&self) -> i8 {
        self.0[4]
    }

    pub fn mole(&self) -> i8 {
        self.0[5]
    }

    pub fn candela(&self) -> i8 {
        self.0[6]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Quantity {
    pub number: String,
    pub unit: Unit,
}

impl Quantity {
    pub fn parse(s: impl AsRef<str>) -> Result<Quantity, Error> {
        let mut p = SIParser::parse(Rule::si_number, s.as_ref())?
            .into_iter()
            .next()
            .ok_or(Error::Internal("expected si_number".into()))?
            .into_inner();
        let number = p
            .next()
            .ok_or(Error::Internal("expected number".into()))?
            .as_str();
        let unit = if let Some(unit) = p.next() {
            parse_unit(unit)?
        } else {
            Unit::unit()
        };
        Ok(Quantity {
            number: number.to_string(),
            unit,
        })
    }

    pub fn as_f32(&self) -> Result<f32, ParseFloatError> {
        let number = self.number.parse::<f32>()?;
        Ok(number * self.unit.prefix.as_f32())
    }
}

fn parse_unit(p: Pair<Rule>) -> Result<Unit, Error> {
    if !matches!(p.as_rule(), Rule::unit) {
        return Err(Error::Internal("expected unit".into()));
    }
    let mut p = p.into_inner();
    let prefix_or_raw_unit = p
        .next()
        .ok_or(Error::Internal("expected prefix or unit".into()))?;
    let (prefix, raw_unit) = if prefix_or_raw_unit.as_rule() == Rule::prefix {
        let raw_unit = p
            .next()
            .ok_or(Error::Internal("expected raw_unit".into()))?;
        (parse_prefix(prefix_or_raw_unit)?, raw_unit)
    } else {
        (Prefix::Unit, prefix_or_raw_unit)
    };
    let base = parse_raw_unit(raw_unit)?;
    let exp = if let Some(num) = p.next() {
        parse_integer_number_i64(num)?
    } else {
        1
    };
    let exp =
        i8::try_from(exp).map_err(|_| Error::Internal("unit exponent must fit in i8".into()))?;
    Ok(Unit { prefix, base, exp })
}

fn parse_raw_unit(p: Pair<Rule>) -> Result<BaseUnit, Error> {
    if !matches!(p.as_rule(), Rule::raw_unit) {
        return Err(Error::Internal("expected raw_unit".into()));
    }
    let raw_unit = p.into_inner().next().ok_or(Error::Internal("".into()))?;
    let unit = match raw_unit.as_rule() {
        Rule::second => BaseUnit::Second,
        Rule::meter => BaseUnit::Meter,
        Rule::gram => BaseUnit::Kilogram, // prefix handled separately
        Rule::ampere => BaseUnit::Ampere,
        Rule::kelvin => BaseUnit::Kelvin,
        Rule::mole => BaseUnit::Mole,
        Rule::candela => BaseUnit::Candela,

        Rule::radian => BaseUnit::Radian,
        Rule::steradian => BaseUnit::Steradian,
        Rule::hertz => BaseUnit::Hertz,
        Rule::newton => BaseUnit::Newton,
        Rule::pascal => BaseUnit::Pascal,
        Rule::joule => BaseUnit::Joule,
        Rule::watt => BaseUnit::Watt,
        Rule::coulomb => BaseUnit::Coulomb,
        Rule::volt => BaseUnit::Volt,
        Rule::farad => BaseUnit::Farad,
        Rule::ohm => BaseUnit::Ohm,
        Rule::siemens => BaseUnit::Siemens,
        Rule::weber => BaseUnit::Weber,
        Rule::tesla => BaseUnit::Tesla,
        Rule::henry => BaseUnit::Henry,
        Rule::celsius => BaseUnit::DegreeCelsius,
        Rule::lumen => BaseUnit::Lumen,
        Rule::lux => BaseUnit::Lux,
        Rule::becquerel => BaseUnit::Becquerel,
        Rule::gray => BaseUnit::Gray,
        Rule::sievert => BaseUnit::Sievert,
        Rule::katal => BaseUnit::Katal,

        Rule::ident => BaseUnit::Named {
            name: raw_unit.as_str().to_string(),
            symbol: "".to_string(),
            exp: SIExp::new_reduced(0, 0, 0, 0),
        },
        _ => return Err(Error::Internal("unhandled raw_unit".into())),
    };
    Ok(unit)
}

pub enum SIExpr {
    Num(String),
    Unit { prefix: Prefix, unit: Unit },
    Mul((Box<SIExpr>, Box<SIExpr>)),
    Div((Box<SIExpr>, Box<SIExpr>)),
}

impl SIExpr {
    pub fn parse(s: impl AsRef<str>) -> Result<SIExpr, Error> {
        let p = SIParser::parse(Rule::si_expr, s.as_ref())?;
        println!("{p:#?}");
        // Err(Error::Internal("unimplemented".into()))
        Ok(SIExpr::Num("".into()))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Prefix {
    Milli,
    Micro,
    Nano,
    Pico,

    Kilo,
    Mega,
    Giga,

    Unit,

    Deca,
    Hecto,
    Tera,
    Peta,
    Exa,
    Zetta,
    Yotta,
    Ronna,
    Quetta,

    Deci,
    Centi,
    Femto,
    Atto,
    Zepto,
    Yocto,
    Ronto,
    Quecto,
}

pub struct OhmF32(pub f32);

#[derive(Debug)]
pub enum Error {
    Pest(pest::error::Error<Rule>),
    Float(ParseFloatError),
    Int(ParseIntError),
    Internal(String),
}

impl From<pest::error::Error<Rule>> for Error {
    fn from(e: pest::error::Error<Rule>) -> Self {
        Error::Pest(e)
    }
}

impl From<ParseFloatError> for Error {
    fn from(e: ParseFloatError) -> Self {
        Error::Float(e)
    }
}

impl From<ParseIntError> for Error {
    fn from(e: ParseIntError) -> Self {
        Error::Int(e)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Pest(e) => write!(f, "{}", e),
            Error::Float(e) => write!(f, "{}", e),
            Error::Int(e) => write!(f, "{}", e),
            Error::Internal(e) => write!(f, "Internal: {}", e),
        }
    }
}

fn expected_rule(name: &'static str) -> Error {
    Error::Internal(name.to_string())
}

impl Prefix {
    pub fn as_f32(&self) -> f32 {
        match self {
            Prefix::Milli => 1e-3,
            Prefix::Micro => 1e-6,
            Prefix::Nano => 1e-9,
            Prefix::Pico => 1e-12,
            Prefix::Kilo => 1e3,
            Prefix::Mega => 1e6,
            Prefix::Giga => 1e9,
            Prefix::Unit => 1e0,
            Prefix::Deca => 1e1,
            Prefix::Hecto => 1e2,
            Prefix::Tera => 1e12,
            Prefix::Peta => 1e15,
            Prefix::Exa => 1e18,
            Prefix::Zetta => 1e21,
            Prefix::Yotta => 1e24,
            Prefix::Ronna => 1e27,
            Prefix::Quetta => 1e30,
            Prefix::Deci => 1e-1,
            Prefix::Centi => 1e-2,
            Prefix::Femto => 1e-15,
            Prefix::Atto => 1e-18,
            Prefix::Zepto => 1e-21,
            Prefix::Yocto => 1e-24,
            Prefix::Ronto => 1e-27,
            Prefix::Quecto => 1e-30,
        }
    }

    pub fn symbol(&self) -> &'static str {
        match self {
            Prefix::Milli => "m",
            Prefix::Micro => "μ", // U+03BC
            Prefix::Nano => "n",
            Prefix::Pico => "p",
            Prefix::Kilo => "k",
            Prefix::Mega => "M",
            Prefix::Giga => "G",
            Prefix::Unit => "",
            Prefix::Deca => "da",
            Prefix::Hecto => "h",
            Prefix::Tera => "T",
            Prefix::Peta => "P",
            Prefix::Exa => "E",
            Prefix::Zetta => "Z",
            Prefix::Yotta => "Y",
            Prefix::Ronna => "R",
            Prefix::Quetta => "Q",
            Prefix::Deci => "d",
            Prefix::Centi => "c",
            Prefix::Femto => "f",
            Prefix::Atto => "a",
            Prefix::Zepto => "z",
            Prefix::Yocto => "y",
            Prefix::Ronto => "r",
            Prefix::Quecto => "q",
        }
    }
}

impl Display for Prefix {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.symbol())
    }
}

#[derive(Parser)]
#[grammar = "grammar/si.pest"]
struct SIParser;

impl OhmF32 {
    pub fn parse(s: impl AsRef<str>) -> Result<OhmF32, Error> {
        let p = SIParser::parse(Rule::resistance, s.as_ref())?;
        // println!("{p:#?}");
        let mut resistance = p
            .into_iter()
            .next()
            .ok_or(expected_rule("resistance"))?
            .into_inner();
        let value = resistance
            .next()
            .ok_or(expected_rule("number_prefix_allowed"))?;
        let value = parse_any_number_f32(value)?;

        if resistance.peek().map(|p| p.as_rule()) == Some(Rule::EOI) {
            return Ok(OhmF32(value));
        }
        let p = resistance
            .next()
            .ok_or(expected_rule("ohm_unit"))?
            .into_inner()
            .next()
            .ok_or(expected_rule("prefix or ohm_or_r"))?;
        let prefix = match p.as_rule() {
            Rule::r_prefix => parse_prefix(p)?,
            Rule::ohm_or_r => Prefix::Unit,
            _ => return Err(Error::Internal("wrong resistance rule".to_owned())),
        };

        Ok(OhmF32(value * prefix.as_f32()))
    }
}

fn parse_any_number_f32(num: Pair<Rule>) -> Result<f32, Error> {
    if !matches!(num.as_rule(), Rule::number | Rule::r_number) {
        return Err(Error::Internal(
            "expected number or number_prefix_allowed".into(),
        ));
    }
    let mut p = num.into_inner();
    let int = parse_integer_number_i64(p.next().ok_or(expected_rule("integer_number"))?)?;
    let Some(tail) = p.next() else {
        return Ok(int as f32);
    };
    match tail.as_rule() {
        Rule::exponent => {
            let exp = parse_integer_number_i64(p.next().ok_or(expected_rule("simple_number"))?)?;
            let exp: u32 = exp
                .try_into()
                .map_err(|_| Error::Internal("exponent is too big".into()))?;
            Ok(int as f32 * 10u64.pow(exp) as f32)
        }
        Rule::raw_number => {
            let frac: f32 = format!("0.{}", tail.as_str()).parse()?;
            let exp = if let Some(p) = p.next() {
                let exp = parse_integer_number_i64(p)?;
                let exp: u32 = exp
                    .try_into()
                    .map_err(|_| Error::Internal("exponent is too big".into()))?;
                exp
            } else {
                0
            };
            Ok((int as f32 + frac) * 10u64.pow(exp) as f32)
        }
        Rule::prefix | Rule::r_prefix => {
            let prefix = parse_prefix(tail)?;
            let frac = if let Some(frac) = p.next() {
                let frac: f32 = format!("0.{}", frac.as_str()).parse()?;
                frac
            } else {
                0.0
            };
            Ok((int as f32 + frac) * prefix.as_f32())
        }
        _ => Err(Error::Internal("unexpected rule".into())),
    }
}

fn parse_integer_number_i64(rule: Pair<Rule>) -> Result<i64, Error> {
    if rule.as_rule() != Rule::integer_number {
        return Err(Error::Internal("expected simple_number".into()));
    }
    let mut p = rule.into_inner();
    let minus_or_raw_number = p.next().ok_or(expected_rule("minus or raw_number"))?;
    let is_minus = minus_or_raw_number.as_rule() == Rule::minus;
    let int = if is_minus {
        let int = p.next().ok_or(expected_rule("integer"))?.into_inner();
        int.as_str()
    } else {
        minus_or_raw_number.as_str()
    };
    let v: i64 = int.parse()?;
    if is_minus { Ok(-v) } else { Ok(v) }
}

fn parse_prefix(rule: Pair<Rule>) -> Result<Prefix, Error> {
    let rule = rule.into_inner().next().ok_or(expected_rule("prefix"))?;
    let prefix = match rule.as_rule() {
        Rule::quetta => Prefix::Quetta,
        Rule::ronna => Prefix::Ronna,
        Rule::yotta => Prefix::Yotta,
        Rule::zetta => Prefix::Zetta,
        Rule::exa => Prefix::Exa,
        Rule::peta => Prefix::Peta,
        Rule::tera => Prefix::Tera,
        Rule::tera_unconditional => Prefix::Tera,
        Rule::giga => Prefix::Giga,
        Rule::giga_unconditional => Prefix::Giga,
        Rule::mega => Prefix::Mega,
        Rule::mega_unconditional => Prefix::Mega,
        Rule::kilo => Prefix::Kilo,
        Rule::kilo_unconditional => Prefix::Kilo,
        Rule::hecto => Prefix::Hecto,
        Rule::deca => Prefix::Deca,
        Rule::deci => Prefix::Deci,
        Rule::centi => Prefix::Centi,
        Rule::milli => Prefix::Milli,
        Rule::milli_unconditional => Prefix::Milli,
        Rule::micro => Prefix::Micro,
        Rule::micro_unconditional => Prefix::Micro,
        Rule::nano => Prefix::Nano,
        Rule::nano_unconditional => Prefix::Nano,
        Rule::pico => Prefix::Pico,
        Rule::femto => Prefix::Femto,
        Rule::atto => Prefix::Atto,
        Rule::zepto => Prefix::Zepto,
        Rule::yocto => Prefix::Yocto,
        Rule::ronto => Prefix::Ronto,
        Rule::quecto => Prefix::Quecto,
        _ => return Err(Error::Internal("expected prefix rule".into())),
    };
    Ok(prefix)
}

impl Display for BaseUnit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.symbol())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use float_cmp::approx_eq;

    #[test]
    fn expr() {
        // let pairs = SIParser::parse(Rule::si_number, "10kg").unwrap();
        // println!("{pairs:#?}");
        // let pairs = SIParser::parse(Rule::si_number, "10 V/s").unwrap();
        // println!("{pairs:#?}");
        // let _expr = SIExpr::parse("10*V/us").unwrap();
        // println!("{pairs:#?}");
        // let v = SIValueF32::parse("9.80665 m/s²").unwrap();
        // assert_eq!(v.value, 9.80665);
        // assert_eq!(v.unit, SIUnit::new_reduced_exp(-2, 1, 0, 0));
        // let _expr = SIExpr::parse("1 m/s⁻²").unwrap();
        // println!("{pairs:#?}");
        // let pairs = SIParser::parse(Rule::si_number, "9.8 m/s^2").unwrap();
        // println!("{pairs:#?}");
        // let pairs = SIParser::parse(Rule::si_number, "1 m/s^-2").unwrap();
        // println!("{pairs:#?}");
    }

    #[test]
    fn si_number_voltage() {
        let num = Quantity::parse("10V").unwrap();
        assert_eq!(num.number, "10");
        assert_eq!(num.unit.prefix, Prefix::Unit);
        assert_eq!(num.unit.base, BaseUnit::Volt);
        assert_eq!(num.unit.exp, 1);
        assert!(approx_eq!(f32, num.as_f32().unwrap(), 10.0, ulps = 2));

        let num = Quantity::parse("10mV").unwrap();
        assert_eq!(num.number, "10");
        assert_eq!(num.unit.prefix, Prefix::Milli);
        assert_eq!(num.unit.base, BaseUnit::Volt);
        assert_eq!(num.unit.exp, 1);
        assert!(approx_eq!(f32, num.as_f32().unwrap(), 0.01, ulps = 2));

        let num = Quantity::parse("10mVDC").unwrap();
        assert_eq!(num.number, "10");
        assert_eq!(num.unit.prefix, Prefix::Milli);
        assert_eq!(num.unit.base.name(), "VDC");
    }

    #[test]
    fn si_number_capacitance() {
        let num = Quantity::parse("4.7 uF").unwrap();
        assert_eq!(num.number, "4.7");
        assert_eq!(num.unit.prefix, Prefix::Micro);
        assert_eq!(num.unit.base, BaseUnit::Farad);
        assert_eq!(num.unit.exp, 1);
        assert!(approx_eq!(f32, num.as_f32().unwrap(), 4.7e-6, ulps = 2));

        let num = Quantity::parse("4.7 µF").unwrap();
        assert_eq!(num.number, "4.7");
        assert_eq!(num.unit.prefix, Prefix::Micro);
        assert_eq!(num.unit.base, BaseUnit::Farad);
        assert_eq!(num.unit.exp, 1);
        assert!(approx_eq!(f32, num.as_f32().unwrap(), 4.7e-6, ulps = 2));
    }

    #[test]
    fn expr_leading_number() {
        let _expr = SIExpr::parse("10*V/us").unwrap();
        let _expr = SIExpr::parse("10 V/us").unwrap();
        let _expr = SIExpr::parse("  10 V/us").unwrap();
        let _expr = SIExpr::parse(" 10V ").unwrap();
        let _expr = SIExpr::parse("10").unwrap();
    }

    #[test]
    fn resistance_values() {
        let v = OhmF32::parse("100").unwrap();
        assert_eq!(v.0, 100.0);

        let v = OhmF32::parse("5k").unwrap();
        assert_eq!(v.0, 5000.0);

        let v = OhmF32::parse("5M").unwrap();
        assert_eq!(v.0, 5_000_000.0);

        let v = OhmF32::parse("5G").unwrap();
        assert_eq!(v.0, 5_000_000_000.0);

        let v = OhmF32::parse("1R").unwrap();
        assert_eq!(v.0, 1.0);

        let v = OhmF32::parse("15.5").unwrap();
        assert_eq!(v.0, 15.5);

        let v = OhmF32::parse("5.55R").unwrap();
        assert_eq!(v.0, 5.55);

        let v = OhmF32::parse("1.0k").unwrap();
        assert_eq!(v.0, 1000.0);

        let v = OhmF32::parse("1k2").unwrap();
        assert_eq!(v.0, 1200.0);

        let v = OhmF32::parse("10 kΩ").unwrap();
        assert_eq!(v.0, 10_000.0);

        let v = OhmF32::parse("5Ω").unwrap();
        assert_eq!(v.0, 5.0);

        let v = OhmF32::parse("1 mΩ").unwrap();
        assert_eq!(v.0, 0.001);

        let v = OhmF32::parse("1μΩ").unwrap();
        assert_eq!(v.0, 0.000001);

        let v = OhmF32::parse(" 0 ").unwrap();
        assert_eq!(v.0, 0.0);

        let v = OhmF32::parse(" 0  R ").unwrap();
        assert_eq!(v.0, 0.0);

        let v = OhmF32::parse("49r").unwrap();
        assert_eq!(v.0, 49.0);

        let v = OhmF32::parse(" 499kR ").unwrap();
        assert_eq!(v.0, 499_000.0);

        let v = OhmF32::parse("12 kOhms").unwrap();
        assert_eq!(v.0, 12000.0);

        let v = OhmF32::parse("2 mOhms").unwrap();
        assert_eq!(v.0, 0.002);
    }
}
