//! SparkML parser

use std::collections::HashSet;

use once_cell::sync::Lazy;
use pest::error::{Error, ErrorVariant};
use pest::iterators::Pair;
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
pub struct SparkMLParser;

fn custom_error(pair: &Pair<Rule>, message: &str) -> Box<Error<Rule>> {
    Box::new(Error::new_from_span(
        ErrorVariant::CustomError {
            message: message.to_string(),
        },
        pair.as_span(),
    ))
}
