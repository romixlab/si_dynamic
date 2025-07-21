use pest::Parser;
use pest::iterators::Pair;
use pest_derive::Parser;
use std::num::{ParseFloatError, ParseIntError};

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
pub struct SIValueF32 {
    value: f32,
    pub unit: SIUnit,
}

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
pub struct SIUnit {
    pub second: Unit,
    pub meter: Unit,
    pub gram: Unit,
    pub ampere: Unit,
    pub kelvin: Unit,
    pub mole: Unit,
    pub candela: Unit,
}

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
pub struct Unit {
    pub prefix: Prefix,
    pub exponent: i8,
}

#[derive(Debug, Copy, Clone, PartialEq, PartialOrd)]
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

fn expected_rule(name: &'static str) -> Error {
    Error::Internal(name.to_string())
}

impl SIUnit {
    pub fn new_reduced(second: Unit, meter: Unit, gram: Unit, ampere: Unit) -> Self {
        SIUnit {
            second,
            meter,
            gram,
            ampere,
            kelvin: Unit::unit(),
            mole: Unit::unit(),
            candela: Unit::unit(),
        }
    }

    pub fn new_reduced_exp(second: i8, meter: i8, gram: i8, ampere: i8) -> Self {
        SIUnit {
            second: Unit::exp(second),
            meter: Unit::exp(meter),
            gram: Unit::exp(gram),
            ampere: Unit::exp(ampere),
            kelvin: Unit::unit(),
            mole: Unit::unit(),
            candela: Unit::unit(),
        }
    }
}

impl Unit {
    pub fn unit() -> Self {
        Unit {
            prefix: Prefix::Unit,
            exponent: 0,
        }
    }

    pub fn exp(exponent: i8) -> Self {
        Unit {
            prefix: Prefix::Unit,
            exponent,
        }
    }
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
}

// pub enum Error {
//     Parse(pest::error::Error<Rule>)
// }

#[derive(Parser)]
#[grammar = "grammar/si.pest"]
struct SIParser;

impl SIValueF32 {
    pub fn parse(s: impl AsRef<str>) -> Result<SIValueF32, pest::error::Error<Rule>> {
        let p = SIParser::parse(Rule::si_number, s.as_ref())?;
        println!("{p:#?}");

        Ok(SIValueF32 {
            value: 0.0,
            unit: SIUnit::new_reduced(Unit::unit(), Unit::unit(), Unit::unit(), Unit::unit()),
        })
    }
}

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
    let int = parse_integer_number_u64(p.next().ok_or(expected_rule("integer_number"))?)?;
    let Some(tail) = p.next() else {
        return Ok(int as f32);
    };
    match tail.as_rule() {
        Rule::exponent => {
            let exp = parse_integer_number_u64(p.next().ok_or(expected_rule("simple_number"))?)?;
            let exp: u32 = exp
                .try_into()
                .map_err(|_| Error::Internal("exponent is too big".into()))?;
            Ok(int as f32 * 10u64.pow(exp) as f32)
        }
        Rule::raw_number => {
            let frac: f32 = format!("0.{}", tail.as_str()).parse()?;
            let exp = if let Some(p) = p.next() {
                let exp = parse_integer_number_u64(p)?;
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

fn parse_integer_number_u64(rule: Pair<Rule>) -> Result<u64, Error> {
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
    let v: u64 = int.parse()?;
    Ok(v)
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
        Rule::giga => Prefix::Giga,
        Rule::mega => Prefix::Mega,
        Rule::kilo => Prefix::Kilo,
        Rule::hecto => Prefix::Hecto,
        Rule::deca => Prefix::Deca,
        Rule::deci => Prefix::Deci,
        Rule::centi => Prefix::Centi,
        Rule::milli => Prefix::Milli,
        Rule::micro => Prefix::Micro,
        Rule::nano => Prefix::Nano,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        // let pairs = SIParser::parse(Rule::si_number, "10kg").unwrap();
        // println!("{pairs:#?}");
        // let pairs = SIParser::parse(Rule::si_number, "10 V/s").unwrap();
        // println!("{pairs:#?}");
        // let pairs = SIParser::parse(Rule::si_number, "10 V/us").unwrap();
        // println!("{pairs:#?}");
        let v = SIValueF32::parse("9.80665 m/s²").unwrap();
        assert_eq!(v.value, 9.80665);
        assert_eq!(v.unit, SIUnit::new_reduced_exp(-2, 1, 0, 0));
        // let pairs = SIParser::parse(Rule::si_number, "1 m/s⁻²").unwrap();
        // println!("{pairs:#?}");
        // let pairs = SIParser::parse(Rule::si_number, "9.8 m/s^2").unwrap();
        // println!("{pairs:#?}");
        // let pairs = SIParser::parse(Rule::si_number, "1 m/s^-2").unwrap();
        // println!("{pairs:#?}");
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
    }
}
