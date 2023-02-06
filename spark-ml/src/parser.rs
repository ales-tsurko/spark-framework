//! SparkML parser

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::mem;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::str::FromStr;

use once_cell::sync::Lazy;
use pest::error::{Error, ErrorVariant};
use pest::iterators::{Pair, Pairs};
use pest::Parser;
use pest_derive::Parser;

static RESERVED_WORDS: Lazy<HashSet<&str>> = Lazy::new(|| {
    [
        "else", "export", "ext", "false", "fn", "from", "if", "repeat", "sub", "true",
    ]
    .into()
});

/// The parser result.
pub type ParseResult<T> = Result<T, Box<Error<Rule>>>;

/// SparkML parser
#[derive(Parser)]
#[grammar = "grammar/spark-ml.pest"] // relative to project `src`
pub struct SparkMLParser;

impl SparkMLParser {
    fn parse_expression(pair: Pair<Rule>) -> ParseResult<Expression> {
        match pair.as_rule() {
            Rule::node => todo!(),
            Rule::node_anon => todo!(),
            Rule::assignment => Self::parse_assignment(pair),
            Rule::if_expr => todo!(),
            Rule::repeat_expr => todo!(),
            Rule::algebraic_expr => todo!(),
            Rule::bool_expr => todo!(),
            Rule::BOOL => Ok(Expression::Value(Value::Boolean(
                pair.as_str().parse().unwrap(),
            ))),
            Rule::call => todo!(),
            Rule::list => todo!(),
            Rule::NUMBER => Ok(Expression::Value(Value::Number(
                pair.as_str().parse().unwrap(),
            ))),
            Rule::STRING => Ok(Expression::Value(Value::String(
                pair.into_inner().next().unwrap().as_str().into(),
            ))),
            Rule::GD_VALUE => Ok(Expression::Value(Value::GdValue(
                pair.into_inner().next().unwrap().as_str().into(),
            ))),
            _ => unreachable!(),
        }
    }

    fn parse_assignment(pair: Pair<Rule>) -> ParseResult<Expression> {
        let mut pairs = pair.into_inner();
        let id = pairs.next().unwrap();
        let expression = pairs.next().unwrap();

        if RESERVED_WORDS.contains(id.as_str()) {
            return Err(custom_error(
                &id,
                &format!("{} is a reserved keyword", id.as_str()),
            ));
        }

        Ok(Expression::Assignment(
            id.as_str().into(),
            Box::new(Self::parse_expression(expression)?),
        ))
    }

    fn parse_func_def(
        pair: Pair<Rule>,
        context: Rc<RefCell<Context<Value>>>,
        ftable: Rc<RefCell<Context<Function>>>,
    ) -> ParseResult<Function> {
        let mut inner = pair.into_inner();
        let id: Id = inner.next().unwrap().as_str().into();
        let args = Self::parse_func_args(inner.next().unwrap())?;
        let body = Self::parse_body(inner.next().unwrap(), context, ftable)?;

        Ok(Function::new(id, args, body))
    }

    fn parse_func_args(pair: Pair<Rule>) -> ParseResult<Vec<Id>> {
        pair.into_inner().map(|id| Ok(id.as_str().into())).collect()
    }

    fn parse_body(
        pair: Pair<Rule>,
        parent_context: Rc<RefCell<Context<Value>>>,
        ftable: Rc<RefCell<Context<Function>>>,
    ) -> ParseResult<Body> {
        let context = Rc::new(RefCell::new(Context::<Value>::with_parent(parent_context)));
        let expressions: Vec<Expression> = pair
            .into_inner()
            .map(Self::parse_expression)
            .collect::<ParseResult<Vec<Expression>>>()?;

        Ok(Body::new(context, ftable, expressions))
    }
}

#[derive(Debug, PartialEq)]
enum Expression {
    Assignment(Id, Box<Expression>),
    Value(Value),
    Function(Id, Vec<Expression>),
    If,
    Repeat,
    Algebraic,
    Boolean,
    List(Vec<Expression>),
}

impl Expression {
    fn eval(
        &self,
        pair: &Pair<Rule>,
        context: &mut Context<Value>,
        ftable: &Context<Function>,
    ) -> ParseResult<Value> {
        match self {
            Expression::Value(val) => Ok(val.clone()),
            Expression::Assignment(id, expression) => {
                let value = expression.eval(pair, context, ftable)?;
                context.assign_var(pair, id.clone(), value.clone())?;
                Ok(value)
            }
            Expression::Function(id, args) => {
                if let Some(function) = ftable.table.get(&id) {
                    function.call_with_args(pair, args)
                } else {
                    Err(custom_error(pair, &format!("Function {} not found", id.0)))
                }
            }
            _ => todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
#[non_exhaustive]
enum Value {
    Node,
    Object(HashMap<Id, Value>),
    String(String),
    Boolean(bool),
    List(Vec<Value>),
    Number(f64),
    GdValue(String),
}

impl Value {
    fn ty_name(&self) -> &'static str {
        match self {
            Self::Node => "Node",
            Self::Object(_) => "Object",
            Self::String(_) => "String",
            Self::Boolean(_) => "Boolean",
            Self::List(_) => "List",
            Self::Number(_) => "Number",
            Self::GdValue(_) => "GdValue",
        }
    }
}

#[derive(Debug)]
struct Function {
    name: Id,
    args: Vec<Id>,
    body: Body,
}

impl Function {
    fn new(name: Id, args: Vec<Id>, body: Body) -> Self {
        Self {
            name,
            args,
            body,
        }
    }

    fn call_with_args(&self, pair: &Pair<Rule>, args: &[Expression]) -> ParseResult<Value> {
        if self.args.len() != args.len() {
            return Err(custom_error(
                pair,
                &format!("expected {} arguments, got {}", self.args.len(), args.len()),
            ));
        }

        {
            let mut context = (*self.body.context).borrow_mut();
            let ftable = (*self.body.ftable).borrow();

            for (n, arg) in args.iter().enumerate() {
                let value = arg.eval(pair, &mut context, &ftable)?;
                context.assign_var(pair, self.args[n].clone(), value)?;
            }
        }

        self.body.eval(pair)
    }
}

#[derive(Debug)]
struct Body {
    expressions: Vec<Expression>,
    context: Rc<RefCell<Context<Value>>>,
    ftable: Rc<RefCell<Context<Function>>>,
}

impl Body {
    fn new(
        context: Rc<RefCell<Context<Value>>>,
        ftable: Rc<RefCell<Context<Function>>>,
        expressions: Vec<Expression>,
    ) -> Self {
        Self {
            context,
            ftable,
            expressions,
        }
    }

    fn eval(&self, pair: &Pair<Rule>) -> ParseResult<Value> {
        let ftable = (*self.ftable).borrow();
        let mut context = (*self.context).borrow_mut();
        let (last, rest) = self.expressions.split_last().unwrap();

        for expression in rest {
            expression.eval(pair, &mut context, &ftable)?;
        }

        last.eval(pair, &mut context, &ftable)
    }
}

/// Context is a scoped storage for variables and functions.
#[derive(Debug)]
struct Context<T> {
    table: HashMap<Id, T>,
    parent: Option<Rc<RefCell<Self>>>,
}

impl<T> Default for Context<T> {
    fn default() -> Self {
        Self {
            table: HashMap::new(),
            parent: None,
        }
    }
}

impl<T> Context<T> {
    fn with_parent(parent: Rc<RefCell<Self>>) -> Self {
        Self {
            parent: Some(parent),
            table: HashMap::new(),
        }
    }

    /// Get a value from the table without looking parent tables.
    fn get_non_recursive(&self, id: &Id) -> Option<&T> {
        self.table.get(id)
    }
}

impl<T: Clone> Context<T> {
    /// Get a value from the table, looking parent tables if necessary.
    fn get_recursive(&self, id: &Id) -> Option<T> {
        self.table
            .get(id)
            .cloned()
            .or_else(|| {
                self.parent
                    .as_ref()
                    .and_then(|parent: &Rc<RefCell<Self>>| (*parent).borrow().get_recursive(id))
            })
            .clone()
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

impl Context<Function> {
    fn add_func_def(&mut self, pair: &Pair<Rule>, func_def: Function) -> ParseResult<()> {
        match self.table.get_mut(&func_def.name) {
            None => {
                self.table.insert(func_def.name.clone(), func_def);
                Ok(())
            }
            Some(_) => Err(custom_error(
                &pair,
                &format!("Function {} already defined", func_def.name.0),
            )),
        }
    }
}

/// Represents a SparkML module.
pub struct Module {
    ext_resources: HashMap<ExtResource, usize>,
    ext_res_incr: Box<dyn FnMut() -> usize>,
    context: Rc<RefCell<Context<Value>>>,
    ftable: Rc<RefCell<Context<Function>>>,
    exports_func: HashSet<Id>,
    exports_var: HashSet<Id>,
}

impl Default for Module {
    fn default() -> Self {
        Self {
            ext_resources: HashMap::new(),
            ext_res_incr: new_incr(),
            context: Default::default(),
            ftable: Default::default(),
            exports_func: Default::default(),
            exports_var: Default::default(),
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

        let (func_defs, rest): (Vec<Pair<Rule>>, Vec<Pair<Rule>>) = pairs.partition(|pair| {
            matches!(pair.as_rule(), Rule::func_def) || matches!(pair.as_rule(), Rule::export_func)
        });

        // we need to define all functions first, to be able to call them from expressions
        module.process_func_defs(func_defs)?;

        for pair in rest {
            match pair.as_rule() {
                Rule::ext_resource => module.add_ext_resource(pair)?,
                Rule::assignment => {
                    SparkMLParser::parse_assignment(pair.clone())?.eval(
                        &pair,
                        &mut (*module.context).borrow_mut(),
                        &(*module.ftable).borrow(),
                    )?;
                    ()
                }
                Rule::export_var => todo!(),
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

    fn process_func_defs(&mut self, pairs: Vec<Pair<Rule>>) -> ParseResult<()> {
        for pair in pairs {
            let (exports, pair) = if matches!(pair.as_rule(), Rule::export_func) {
                (true, pair.into_inner().next().unwrap())
            } else {
                (false, pair)
            };

            let function = SparkMLParser::parse_func_def(
                pair.clone(),
                Rc::clone(&self.context),
                Rc::clone(&self.ftable),
            )?;

            let id = function.name.clone();

            (*self.ftable).borrow_mut().add_func_def(&pair, function)?;

            if exports {
                self.exports_func.insert(id);
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

    #[test]
    fn test_parse_func_def() {
        let context = Default::default();
        let ftable = Default::default();
        let pair = SparkMLParser::parse(
            Rule::func_def,
            r#"fn foo(a, b)
                n = 10
                20"#,
        )
        .unwrap()
        .next()
        .unwrap();
        let function = SparkMLParser::parse_func_def(pair, context, ftable).unwrap();

        assert_eq!(function.name, "foo".into());
        assert_eq!(function.args, vec!["a".into(), "b".into()]);
        assert_eq!(function.body.expressions.len(), 2);
    }

    #[test]
    fn test_parse_expression_assignment() {
        let mut context = Context::<Value>::default();
        let ftable = Context::<Function>::default();
        let pair = SparkMLParser::parse(Rule::assignment, "foo = true")
            .unwrap()
            .next()
            .unwrap();
        let assignment = SparkMLParser::parse_assignment(pair.clone()).unwrap();
        assert_eq!(
            assignment.eval(&pair, &mut context, &ftable).unwrap(),
            Value::Boolean(true)
        );

        assert_eq!(context.table[&"foo".into()], Value::Boolean(true));

        // using reserved keyword is not allowed
        let pair = SparkMLParser::parse(Rule::assignment, "true = false")
            .unwrap()
            .next()
            .unwrap();
        assert!(SparkMLParser::parse_assignment(pair).is_err());
    }

    #[test]
    fn test_parse_expression_value() {
        let mut context = Context::<Value>::default();
        let ftable = Context::<Function>::default();
        let pair = SparkMLParser::parse(Rule::expression, "1")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            SparkMLParser::parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, &mut context, &ftable)
                .unwrap(),
            Value::Number(1.0)
        );

        let pair = SparkMLParser::parse(Rule::expression, "1.0")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            SparkMLParser::parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, &mut context, &ftable)
                .unwrap(),
            Value::Number(1.0)
        );

        let pair = SparkMLParser::parse(Rule::expression, "1E-2")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            SparkMLParser::parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, &mut context, &ftable)
                .unwrap(),
            Value::Number(0.01)
        );

        let pair = SparkMLParser::parse(Rule::expression, r#""This is a string\nhello""#)
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            SparkMLParser::parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, &mut context, &ftable)
                .unwrap(),
            Value::String("This is a string\\nhello".to_string())
        );

        let pair = SparkMLParser::parse(Rule::expression, r#"`NodePath("Path:")`"#)
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            SparkMLParser::parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, &mut context, &ftable)
                .unwrap(),
            Value::GdValue("NodePath(\"Path:\")".to_string())
        );

        let pair = SparkMLParser::parse(Rule::expression, "true")
            .unwrap()
            .next()
            .unwrap();
        assert!(matches!(
            SparkMLParser::parse_expression(pair.clone()).unwrap().eval(
                &pair,
                &mut context,
                &ftable
            ),
            Ok(Value::Boolean(true))
        ));

        let pair = SparkMLParser::parse(Rule::expression, "false")
            .unwrap()
            .next()
            .unwrap();
        assert!(matches!(
            SparkMLParser::parse_expression(pair.clone()).unwrap().eval(
                &pair,
                &mut context,
                &ftable
            ),
            Ok(Value::Boolean(false))
        ));
    }
}
