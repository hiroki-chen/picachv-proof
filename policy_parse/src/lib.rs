use lalrpop_util::lalrpop_mod;

#[cfg(test)]
lalrpop_mod!(test_parser, "/grammar/test.rs");

lalrpop_mod!(policy_parser, "/grammar/policy_definition_language.rs");

pub mod ast;

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parser_works() {
        assert!(test_parser::TermParser::new().parse("22").is_ok());
    }

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
            "differential_privacy",
            "Dp",
            "k_anon",
            "T_closeness",
            "L_diversity",
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
