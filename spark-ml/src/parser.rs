//! SparkML parser

use std::collections::HashSet;

use once_cell::sync::Lazy;
use pest::error::{Error, ErrorVariant};
use pest::iterators::Pair;
use pest::pratt_parser::{Assoc, Op, PrattParser};
use pest_derive::Parser;

mod ast;
mod context;
mod module;
mod value;

static RESERVED_WORDS: Lazy<HashSet<&str>> = Lazy::new(|| {
    [
        "else", "export", "ext", "false", "fn", "from", "if", "repeat", "sub", "true",
    ]
    .into()
});

/// The parser result.
pub(crate) type ParseResult<T> = Result<T, Box<Error<Rule>>>;

/// SparkML parser
#[derive(Parser)]
#[grammar = "grammar/spark-ml.pest"] // relative to project `src`
pub struct SparkMLParser {
    algebraic: PrattParser<Rule>,
    boolean: PrattParser<Rule>,
}

impl Default for SparkMLParser {
    fn default() -> Self {
        let algebraic = PrattParser::new()
            .op(Op::infix(Rule::ADD, Assoc::Left) | Op::infix(Rule::SUB, Assoc::Left))
            .op(Op::infix(Rule::MUL, Assoc::Left)
                | Op::infix(Rule::DIV, Assoc::Left)
                | Op::infix(Rule::MOD, Assoc::Left))
            .op(Op::prefix(Rule::NEG));

        let boolean = PrattParser::new()
            .op(Op::infix(Rule::OR, Assoc::Left))
            .op(Op::infix(Rule::AND, Assoc::Left))
            .op(Op::infix(Rule::EQ, Assoc::Left) | Op::infix(Rule::NEQ, Assoc::Left))
            .op(Op::infix(Rule::LT, Assoc::Left)
                | Op::infix(Rule::LT_EQ, Assoc::Left)
                | Op::infix(Rule::GT, Assoc::Left)
                | Op::infix(Rule::GT_EQ, Assoc::Left))
            .op(Op::prefix(Rule::NOT));

        Self { algebraic, boolean }
    }
}

fn custom_error(pair: &Pair<Rule>, message: &str) -> Box<Error<Rule>> {
    Box::new(Error::new_from_span(
        ErrorVariant::CustomError {
            message: message.to_string(),
        },
        pair.as_span(),
    ))
}
