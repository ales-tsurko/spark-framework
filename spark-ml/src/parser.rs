use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar/spark-ml.pest"] // relative to project `src`
pub struct SparkMLParser;

#[cfg(test)]
mod tests {
    use super::*;
    use pest::{iterators::Pair, Parser};

    #[test]
    fn it_works() {
        let input = include_str!("../test_input/test.sprk");
        let pairs = SparkMLParser::parse(Rule::module, input).unwrap();
    }
}
