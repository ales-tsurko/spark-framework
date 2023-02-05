//! SparkML parser

use std::collections::HashMap;
use std::fmt::Display;
use std::path::{Path, PathBuf};

use pest::error::{Error, ErrorVariant};
use pest::iterators::{Pair, Pairs};
use pest::Parser;
use pest_derive::Parser;

type ParseResult<T> = Result<T, Box<Error<Rule>>>;

/// SparkML parser
#[derive(Parser)]
#[grammar = "grammar/spark-ml.pest"] // relative to project `src`
pub struct SparkMLParser;

impl SparkMLParser {
    /// Parse the string and return [`Module`](self::Module) on success.
    pub fn parse_str(input: &str) -> Result<Module, Box<Error<Rule>>> {
        let mut pairs = SparkMLParser::parse(Rule::module, input)?;
        let pair = pairs.next().unwrap();
        Module::from_pair(pair)
    }
}

/// Represents a SparkML module.
pub struct Module {
    ext_resources: HashMap<ExtResource, usize>,
    ext_res_incr: Box<dyn FnMut() -> usize>,
}

impl Default for Module {
    fn default() -> Self {
        Self {
            ext_resources: HashMap::new(),
            ext_res_incr: Box::new(new_incr()),
        }
    }
}

impl Module {
    pub const EXTENSION: &'static str = "sprk";

    pub fn from_pair(pair: Pair<Rule>) -> ParseResult<Self> {
        match pair.as_rule() {
            Rule::module => Self::parse_top_inner(pair.into_inner()),
            _ => Err(custom_error(&pair, "Expected module")),
        }
    }

    fn parse_top_inner(pairs: Pairs<Rule>) -> ParseResult<Self> {
        let mut module = Self::default();

        for pair in pairs {
            match pair.as_rule() {
                Rule::ext_resource => module.add_ext_resource(pair)?,
                Rule::sub_resource => todo!(),
                Rule::assignment => todo!(),
                Rule::node => todo!(),
                Rule::signal_def => todo!(),
                Rule::animation_def => todo!(),
                Rule::func_def => todo!(),
                Rule::export => todo!(),
                Rule::if_expr => todo!(),
                Rule::repeat_expr => todo!(),
                Rule::call => todo!(),
                _ => (),
            }
        }

        Ok(module)
    }

    fn add_ext_resource(&mut self, pair: Pair<Rule>) -> ParseResult<()> {
        let pair = pair.into_inner().next().unwrap();
        let (value, id) = match pair.as_rule() {
            Rule::ID => (ExtResource::StdLib(pair.as_str().into()), 0),
            Rule::STRING => (
                ExtResource::from_string_rule(pair.clone().into_inner().next().unwrap())?,
                (self.ext_res_incr)(),
            ),
            _ => unreachable!(),
        };

        match self.ext_resources.insert(value.clone(), id) {
            None => Ok(()),
            Some(_) => Err(custom_error(
                &pair,
                &format!("The {} already imported", value),
            )),
        }
    }
}

/// An external resource.
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum ExtResource {
    StdLib(Id),
    Module(PathBuf),
    Scene(PathBuf),
    GdScript(PathBuf),
    Image(PathBuf),
}

impl Display for ExtResource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StdLib(id) => write!(f, "std lib res://{}", id.0),
            Self::Module(path) => write!(f, "module res://{}", path.display()),
            Self::Scene(path) => write!(f, "scene res://{}", path.display()),
            Self::GdScript(path) => write!(f, "script res://{}", path.display()),
            Self::Image(path) => write!(f, "image res://{}", path.display()),
        }
    }
}

/// ID representation.
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct Id(String);

impl From<String> for Id {
    fn from(s: String) -> Self {
        Self(s)
    }
}

impl From<&str> for Id {
    fn from(s: &str) -> Self {
        Self(s.to_string())
    }
}

fn new_incr() -> impl FnMut() -> usize {
    let mut i = 0;

    move || -> usize {
        i += 1;
        i
    }
}

impl ExtResource {
    pub fn from_string_rule(pair: Pair<Rule>) -> ParseResult<Self> {
        let path = Path::new(pair.as_str());
        match path.extension() {
            None => Err(custom_error(&pair, "Expected resource path.")),
            Some(ext) => match ext.to_str().unwrap() {
                // list of supported image formats
                // https://docs.godotengine.org/en/stable/tutorials/assets_pipeline/importing_images.html?highlight=png#supported-image-formats
                "bpm" | "dds" | "exr" | "hdr" | "jpg" | "jpeg" | "png" | "tga" | "svg" | "svgz"
                | "webp" => Ok(ExtResource::Image(path.to_path_buf())),
                "gd" => Ok(ExtResource::GdScript(path.to_path_buf())),
                Module::EXTENSION => Ok(ExtResource::Module(path.to_path_buf())),
                "tscn" => Ok(ExtResource::Scene(path.to_path_buf())),
                _ => Err(custom_error(&pair, "Unsupported resource type.")),
            },
        }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_input() {
        // should not panic
        let _ = SparkMLParser::parse_str("").unwrap();
    }

    #[test]
    fn test_ext_resource() {
        let output = SparkMLParser::parse_str(
            r#"
            ext "Path.sprk"
            ext "Path.tscn"
            ext math
            ext "Path.gd"
            ext "Path.png"
            "#,
        );

        let expected: HashMap<ExtResource, usize> = [
            (ExtResource::Module("Path.sprk".into()), 1),
            (ExtResource::Scene("Path.tscn".into()), 2),
            (ExtResource::StdLib("math".into()), 0),
            (ExtResource::GdScript("Path.gd".into()), 3),
            (ExtResource::Image("Path.png".into()), 4),
        ]
        .into();

        let result = output.unwrap().ext_resources;

        assert_eq!(result.len(), expected.len());

        for (res, id) in expected {
            assert_eq!(id, result[&res]);
        }

        let output = SparkMLParser::parse_str(
            r#"
            ext "Path.sprk"
            ext "Path.sprk"
            "#,
        );

        assert!(output.is_err());

        let output = SparkMLParser::parse_str(
            r#"
            ext "Path.foo"
            "#,
        );

        assert!(output.is_err());
    }
}
