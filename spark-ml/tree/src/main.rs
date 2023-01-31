//! This is a tool for the parser's development. It supposed to run using watchexec and contineously
//! see how the input is parsed (as on the pest' site).
//!
//! This tool is very simple you should pass the file with test input as the argument. It doesn't
//! have any error handlings and not supposed to be used in production.
//!
//! ```
//! cargo run -q --bin tree -- spark-ml/test_input/test.sprk
//! ```

use std::{fs, env};

use pest_tools::parser_tree_as_string;
use pest::Parser;
use spark_ml::parser::{SparkMLParser, Rule};

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        panic!("You should pass the file with test input as the argument");
    }

    let input = fs::read_to_string(&args[1]).expect("Can't read the file");

    match SparkMLParser::parse(Rule::module, &input) {
        Ok(pairs) => println!("{}", parser_tree_as_string(pairs)),
        Err(e) => println!("Error: {:?}", e),
    }
}
