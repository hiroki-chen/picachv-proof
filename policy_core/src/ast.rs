//! The abstract syntax tree for the PDL.
//!
//! The structs defined in this module can be exported to `lalrpop`.

use crate::{
    expr::{Aggregation, BinaryOp, Expr},
    policy::Schema,
    types::DataType,
};

#[cfg(feature = "ast-serde")]
use serde::{Deserialize, Serialize};

/// Defines the type of the privacy scheme that should be applied.
#[cfg_attr(feature = "ast-serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, PartialEq)]
pub enum PrivacyScheme {
    /// Differential privacy with epsilon and delta.
    DifferentialPrivacy(f64, f64),
    /// t-closesness with parameter `t`.
    TCloseness(usize),
}

/// Scheme for ensuring privacy.
#[cfg_attr(feature = "ast-serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
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
#[cfg_attr(feature = "ast-serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug)]
pub enum Clause {
    Allow {
        attribute_list: Vec<String>,
        scheme: Vec<Scheme>,
    },
    /// Deny access on a list of attributes.
    Deny(Vec<String>),
}

impl Clause {
    pub fn attribute_list_mut(&mut self) -> &mut Vec<String> {
        match self {
            Self::Allow { attribute_list, .. } | Self::Deny(attribute_list) => attribute_list,
        }
    }
}

/// The root node of the policy AST.
#[cfg_attr(feature = "ast-serde", derive(Serialize, Deserialize))]
#[derive(Clone, Debug, Default)]
pub struct Policy {
    name: String,
    schema: Schema,
    clause: Vec<Clause>,
}

impl Policy {
    #[inline]
    /// Constructs a policy node from the parsed AST sub-trees.
    pub fn new(name: String, schema: Schema, clause: Vec<Clause>) -> Self {
        Self {
            name,
            schema,
            clause,
        }
    }

    #[inline]
    pub fn name(&self) -> &str {
        self.name.as_ref()
    }

    pub fn schema_mut(&mut self) -> &mut Vec<(String, DataType)> {
        &mut self.schema
    }

    pub fn schema(&self) -> &[(String, DataType)] {
        self.schema.as_ref()
    }

    pub fn clause(&self) -> &[Clause] {
        self.clause.as_ref()
    }

    /// Performs the postprocessing that removes duplications.
    pub fn postprocess(&mut self) {}

    pub fn clause_mut(&mut self) -> &mut Vec<Clause> {
        &mut self.clause
    }
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

    #[test]
    #[cfg(feature = "ast-serde")]
    fn pdl_can_serialize_policies() {
        let simple_policy = r#"
            FOO ATTRIBUTE(foo: i64, bar: f32, baz: u64):
            (
                Deny (foo, baz), Deny (foo), Allow(foo),
            )
        "#;
        let policy = policy_parser::PolicyParser::new().parse(simple_policy);

        assert!(policy.is_ok());

        let policy = serde_json::to_string(&policy.unwrap()).unwrap();

        assert_eq!(
            r#"{"name":"FOO","schema":[["foo","Int64"],["bar","Float32"],["baz","UInt64"]],"clause":[{"Deny":["foo","baz"]},{"Deny":["foo"]},{"Allow":{"attribute_list":["foo"],"scheme":[]}}]}"#,
            policy
        );
    }
}
