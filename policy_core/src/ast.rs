//! The abstract syntax tree for the PDL.
//!
//! The structs defined in this module can be exported to `lalrpop`.

use crate::{
    expr::{Aggregation, Expr, BinaryOp},
    policy::Schema,
};

/// Defines the type of the privacy scheme that should be applied.
#[derive(Clone, Debug, PartialEq)]
pub enum PrivacyScheme {
    /// Differential privacy with epsilon and delta.
    DifferentialPrivacy(f64, f64),
    /// t-closesness with parameter `t`.
    TCloseness(usize),
}

/// Scheme for ensuring privacy.
#[derive(Clone)]
pub enum Scheme {
    Redact,
    Filter(Box<Expr>),
    Op {
        ops: Vec<Aggregation>,
        privacy: PrivacyScheme,
    },

    /// s1 (and | or) s2.
    Binary {
        lhs: Box<Scheme>,
        binary_op: BinaryOp,
        rhs: Box<Scheme>,
    },
}

/// Policy clauses.
#[derive(Clone)]
pub enum Clause {
    Allow {
        attribute_list: Vec<String>,
        schema: Vec<Scheme>,
    },
    /// Deny access on a list of attributes.
    Deny(Vec<String>),
}

/// The root node of the policy AST.
#[derive(Clone)]
pub struct Policy {
    schema: Schema,
    clause: Vec<Clause>,
}

#[cfg(test)]
mod test {
    use crate::policy_parser;

    #[test]
    fn pdl_can_parse_numbers() {
        let num_str = [
            "+1", "+1.", "+.1", "+0.1", "1", "1.", " .1", "0.1", "((0.))", "((+1.0))",
        ];
        let num_parser = policy_parser::NumParser::new();
        for num in num_str {
            assert!(num_parser.parse(num).is_ok(), "parse failed: `{num}`");
        }
    }

    #[test]
    fn pdl_can_parse_keyword() {
        let keywords = [
            "allow",
            "Allow",
            " aLLOW",
            "AlLoW    ",
            "denY ",
            "scheMe   ",
            "filTer  ",
            "   RoW",
        ];
        let keyword_parser = policy_parser::KeywordParser::new();

        for keyword in keywords {
            assert!(
                keyword_parser.parse(keyword).is_ok(),
                "parse failed: `{keyword}`"
            );
        }
    }

    #[test]
    fn pdl_can_parse_scheme() {
        let schemes = [
            "differential_privacy(1)",
            "Dp(2,4)",
            "k_anon(3)",
            "T_closeness(3.1415926535)",
            "L_diversity(-999)",
        ];
        let scheme_parser = policy_parser::SchemeParser::new();

        for scheme in schemes {
            assert!(
                scheme_parser.parse(scheme).is_ok(),
                "parse failed: `{scheme}`"
            );
        }
    }

    #[test]
    fn pdl_can_parse_attribute_list() {
        let list = "((attribute (foo: str, bar: i64, baz: f32, __test: bool, (_random_data_abcd777: String))))";

        assert!(policy_parser::AttributeListParser::new()
            .parse(list)
            .is_ok());
    }
}
