use pest_derive::Parser;
use pest::Parser;

pub struct SIValueF32 {
    pub value: f32,
    pub unit: SIUnit,
}

pub struct SIUnit {
    pub second: Unit,
    pub meter: Unit,
    pub gram: Unit,
    pub ampere: Unit,
    pub kelvin: Unit,
    pub mole: Unit,
    pub candela: Unit
}

pub struct Unit {
    pub prefix: Prefix,
    pub exponent: i8,
}

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

// pub enum Error {
//     Parse(pest::error::Error<Rule>)
// }

#[derive(Parser)]
#[grammar = "grammar/si.pest"]
struct SIParser;

impl SIValueF32 {
    pub fn parse(s: impl AsRef<str>) -> Result<SIValueF32, pest::error::Error<Rule>> {
        let p = SIParser::parse(Rule::si_number, s.as_ref())?;

        Ok(SIValueF32 {
            value,
            unit,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let pairs = SIParser::parse(Rule::si_number, "10kg").unwrap();
        println!("{pairs:#?}");
        let pairs = SIParser::parse(Rule::si_number, "10 V/s").unwrap();
        println!("{pairs:#?}");
        let pairs = SIParser::parse(Rule::si_number, "10 V/us").unwrap();
        println!("{pairs:#?}");
        // let pairs = SIParser::parse(Rule::si_number, "9.8 m/s²").unwrap();
        // println!("{pairs:#?}");
        // let pairs = SIParser::parse(Rule::si_number, "1 m/s⁻²").unwrap();
        // println!("{pairs:#?}");
        // let pairs = SIParser::parse(Rule::si_number, "9.8 m/s^2").unwrap();
        // println!("{pairs:#?}");
        // let pairs = SIParser::parse(Rule::si_number, "1 m/s^-2").unwrap();
        // println!("{pairs:#?}");
    }

    #[test]
    fn resistance_values() {
        let (v, w) = parse_resistance_value("100").unwrap();
        assert_eq!(v.0, 100.0);
        assert!(w.is_none());
        // assert_eq!(v.1, "100Ω");

        let (v, w) = parse_resistance_value("5k").unwrap();
        assert_eq!(v.0, 5000.0);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value("5M").unwrap();
        assert_eq!(v.0, 5_000_000.0);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value("5G").unwrap();
        assert_eq!(v.0, 5_000_000_000.0);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value("1R").unwrap();
        assert_eq!(v.0, 1.0);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value("15.5").unwrap();
        assert_eq!(v.0, 15.5);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value("5.53R").unwrap();
        assert_eq!(v.0, 5.53);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value("1.0k").unwrap();
        assert_eq!(v.0, 1000.0);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value("1k2").unwrap();
        assert_eq!(v.0, 1200.0);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value("10 kΩ").unwrap();
        assert_eq!(v.0, 10_000.0);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value("5Ω").unwrap();
        assert_eq!(v.0, 5.0);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value("1mΩ").unwrap();
        assert_eq!(v.0, 0.001);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value("1μΩ").unwrap();
        assert_eq!(v.0, 0.000001);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value(" 0 ").unwrap();
        assert_eq!(v.0, 0.0);
        assert!(w.is_none());

        let (v, w) = parse_resistance_value(" 0  R ").unwrap();
        assert_eq!(v.0, 0.0);
        assert!(matches!(w, Some(PassiveValueParseWarning::RedundantSpace)));

        let (v, w) = parse_resistance_value("49r").unwrap();
        assert_eq!(v.0, 49.0);
        assert!(matches!(w, Some(PassiveValueParseWarning::SmallR)));

        let (v, w) = parse_resistance_value(" 499kR ").unwrap();
        assert_eq!(v.0, 499_000.0);
        assert!(matches!(
            w,
            Some(PassiveValueParseWarning::BigRInsteadOfOhmSymbol)
        ));
    }
}
