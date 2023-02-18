use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::str::FromStr;

use pest::error::Error;
use pest::iterators::{Pair, Pairs};
use pest::Parser;

use crate::parser::context::Context;
use crate::parser::value::Id;
use crate::parser::{ast, ast::Ast};
use crate::parser::{custom_error, ParseResult, Rule, SparkMLParser};

/// Represents a SparkML module.
pub(crate) struct Module {
    ext_resources: HashMap<ExtResource, usize>,
    ext_res_incr: Box<dyn FnMut() -> usize>,
    context: Context,
    exports_func: HashSet<Id>,
    exports_var: HashSet<Id>,
    parser: SparkMLParser,
}

impl Default for Module {
    fn default() -> Self {
        Self {
            ext_resources: HashMap::new(),
            ext_res_incr: new_incr(),
            context: Default::default(),
            exports_func: Default::default(),
            exports_var: Default::default(),
            parser: Default::default(),
        }
    }
}

impl Module {
    pub(crate) const EXTENSION: &'static str = "sprk";

    fn from_top_pair(pair: Pair<Rule>) -> ParseResult<Self> {
        match pair.as_rule() {
            Rule::module => Self::parse_top_inner(pair.into_inner()),
            _ => Err(custom_error(&pair, "Expected module")),
        }
    }

    fn parse_top_inner(pairs: Pairs<Rule>) -> ParseResult<Self> {
        let mut module = Self::default();

        let (func_defs, rest): (Vec<Pair<Rule>>, Vec<Pair<Rule>>) = pairs.partition(|pair| {
            matches!(pair.as_rule(), Rule::func_def) || matches!(pair.as_rule(), Rule::export_func)
        });

        // we need to define all functions first, to be able to call them from expressions
        module.process_func_defs(func_defs)?;

        for pair in rest {
            match pair.as_rule() {
                Rule::ext_resource => module.add_ext_resource(pair)?,
                Rule::assignment => {
                    ast::parse_assignment(pair.clone(), &module.parser)?
                        .eval(&pair, module.context.clone())?;
                    ()
                }
                Rule::export_var => todo!(),
                Rule::if_expr => todo!(),
                Rule::repeat_expr => todo!(),
                Rule::call => todo!(),
                Rule::node => todo!(),
                Rule::sub_resource => todo!(),
                _ => (),
            }
        }

        Ok(module)
    }

    fn process_func_defs(&mut self, pairs: Vec<Pair<Rule>>) -> ParseResult<()> {
        for pair in pairs {
            let (exports, pair) = if matches!(pair.as_rule(), Rule::export_func) {
                (true, pair.into_inner().next().unwrap())
            } else {
                (false, pair)
            };

            let expr = ast::parse_func_def(pair.clone(), &self.parser)?;
            if let Ast::FunctionDef(ref func) = expr {
                let id = func.name.clone();
                expr.eval(&pair, self.context.clone())?;

                if exports {
                    self.exports_func.insert(id);
                }
            } else {
                unreachable!()
            }
        }

        Ok(())
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

fn new_incr() -> Box<dyn FnMut() -> usize> {
    let mut i = 0;
    Box::new(move || -> usize {
        i += 1;
        i
    })
}

/// An external resource.
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub(crate) enum ExtResource {
    StdLib(Id),
    Module(PathBuf),
    Scene(PathBuf),
    GdScript(PathBuf),
    Image(PathBuf),
}

impl std::fmt::Display for ExtResource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StdLib(id) => write!(f, "lib {}", id.as_str()),
            Self::Module(path) => write!(f, "module res://{}", path.display()),
            Self::Scene(path) => write!(f, "scene res://{}", path.display()),
            Self::GdScript(path) => write!(f, "script res://{}", path.display()),
            Self::Image(path) => write!(f, "image res://{}", path.display()),
        }
    }
}

impl ExtResource {
    pub(crate) fn from_string_rule(pair: Pair<Rule>) -> ParseResult<Self> {
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
}
