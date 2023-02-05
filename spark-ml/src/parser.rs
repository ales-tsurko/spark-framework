//! SparkML parser

use std::collections::HashMap;
use std::fmt::Display;
use std::mem;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::str::FromStr;

use pest::error::{Error, ErrorVariant};
use pest::iterators::{Pair, Pairs};
use pest::Parser;
use pest_derive::Parser;

/// The parser result.
pub type ParseResult<T> = Result<T, Box<Error<Rule>>>;

/// SparkML parser
#[derive(Parser)]
#[grammar = "grammar/spark-ml.pest"] // relative to project `src`
pub struct SparkMLParser;

/// Represents a SparkML module.
pub struct Module {
    ext_resources: HashMap<ExtResource, usize>,
    ext_res_incr: Box<dyn FnMut() -> usize>,
    variables: Rc<Context<Value>>,
    // functions: Rc<Context<Function>>,
}

impl Default for Module {
    fn default() -> Self {
        Self {
            ext_resources: HashMap::new(),
            ext_res_incr: new_incr(),
            variables: Rc::new(Context::<Value>::default()),
        }
    }
}

impl Module {
    pub const EXTENSION: &'static str = "sprk";

    fn from_top_pair(pair: Pair<Rule>) -> ParseResult<Self> {
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
                Rule::assignment => todo!(),
                Rule::func_def => todo!(),
                Rule::export => todo!(),
                Rule::if_expr => todo!(),
                Rule::repeat_expr => todo!(),
                Rule::call => todo!(),
                Rule::node => todo!(),
                Rule::signal_def => todo!(),
                Rule::animation_def => todo!(),
                Rule::sub_resource => todo!(),
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

impl FromStr for Module {
    type Err = Box<Error<Rule>>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut pairs = SparkMLParser::parse(Rule::module, s)?;
        let pair = pairs.next().unwrap();
        Self::from_top_pair(pair)
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
            Self::StdLib(id) => write!(f, "lib {}", id.0),
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

fn new_incr() -> Box<dyn FnMut() -> usize> {
    let mut i = 0;
    Box::new(move || -> usize {
        i += 1;
        i
    })
}

impl ExtResource {
    pub fn from_string_rule(pair: Pair<Rule>) -> ParseResult<Self> {
        let path = Path::new(pair.as_str());
        match path.extension() {
            None => Err(custom_error(&pair, "Expected resource path.")),
            Some(ext) => match ext.to_str().unwrap() {
                // list of supported image formats
                // https://docs.godotengine.org/en/stable/tutorials/assets_pipeline/importing_images.html
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

/// Context is a scoped storage for variables and functions.
#[derive(Debug)]
struct Context<T> {
    table: HashMap<Id, T>,
    parent: Option<Rc<Self>>,
}

impl<T> Context<T> {
    fn with_parent(parent: Rc<Self>) -> Self {
        Self {
            parent: Some(parent),
            table: HashMap::new(),
        }
    }
}

impl Default for Context<Value> {
    fn default() -> Self {
        Self {
            table: HashMap::new(),
            parent: None,
        }
    }
}

impl Context<Value> {
    fn assign_var(&mut self, pair: &Pair<Rule>, id: Id, value: Value) -> ParseResult<()> {
        match self.table.get_mut(&id) {
            None => {
                self.table.insert(id, value);
                Ok(())
            }
            Some(val) => {
                if mem::discriminant(val) != mem::discriminant(&value) {
                    return Err(custom_error(
                        &pair,
                        &format!(
                            "Type mismatch: expected {} found {}",
                            val.ty_name(),
                            value.ty_name()
                        ),
                    ));
                }
                *val = value;
                Ok(())
            }
        }
    }
}

#[derive(Debug)]
enum Value {
    Node,
    Object,
    String(String),
    Boolean(bool),
    List,
    Number(f64),
    GdValue,
}

impl Value {
    fn ty_name(&self) -> &'static str {
        match self {
            Self::Node => "Node",
            Self::Object => "Object",
            Self::String(_) => "String",
            Self::Boolean(_) => "Boolean",
            Self::List => "List",
            Self::Number(_) => "Number",
            Self::GdValue => "GdValue",
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
        let _ = Module::from_str("").unwrap();
    }

    #[test]
    fn test_ext_resources() {
        let output: ParseResult<Module> = r#"
            ext "Path.sprk"
            ext "Path.tscn"
            ext math
            ext "Path.gd"
            ext "Path.png"
            "#
        .parse();

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

        // import the same resource twice not allowed
        let output: ParseResult<Module> = r#"
            ext "Path.sprk"
            ext "Path.sprk"
            "#
        .parse();

        assert!(output.is_err());

        // unknown resource type
        let output: ParseResult<Module> = r#"
            ext "Path.foo"
            "#
        .parse();

        assert!(output.is_err());
    }

    #[test]
    fn test_context() {
        let mut context = Context::<Value>::default();
        // we need it just to pass something
        let pair = SparkMLParser::parse(Rule::module, "\n")
            .unwrap()
            .next()
            .unwrap();

        // assign a variable
        assert!(context.table.get(&"foo".into()).is_none());

        assert!(context
            .assign_var(&pair, "foo".into(), Value::Boolean(true))
            .is_ok());

        assert!(matches!(
            context.table.get(&"foo".into()),
            Some(Value::Boolean(true))
        ));

        // re-assign a variable
        assert!(context
            .assign_var(&pair, "foo".into(), Value::Boolean(false))
            .is_ok());

        assert!(matches!(
            context.table.get(&"foo".into()),
            Some(Value::Boolean(false))
        ));

        // type mismatch
        assert!(context
            .assign_var(&pair, "foo".into(), Value::Number(1.0))
            .is_err());
    }
}
