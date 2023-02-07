use std::cell::RefCell;
use std::rc::Rc;

use im::Vector;
use pest::iterators::Pair;

use crate::parser::context::Context;
use crate::parser::expression::{self, Body, Expression};
use crate::parser::{custom_error, ParseResult, Rule, RESERVED_WORDS};

#[derive(Debug, PartialEq, Clone)]
#[non_exhaustive]
pub(crate) enum Value {
    Node,
    Object(Object<Value>),
    String(String),
    Boolean(bool),
    List(Vector<Value>),
    Number(f64),
    GdValue(String),
}

impl Value {
    pub(crate) fn ty_name(&self) -> &'static str {
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

#[derive(Debug, Clone)]
pub(crate) struct Object<T: PartialEq> {
    attributes: Box<Vec<Attribute<T>>>,
    ftable: Rc<RefCell<Context<Function>>>,
    context: Rc<RefCell<Context<Value>>>,
}

impl<T: PartialEq> PartialEq for Object<T> {
    fn eq(&self, other: &Self) -> bool {
        self.attributes == other.attributes
            && Rc::ptr_eq(&self.ftable, &other.ftable)
            && Rc::ptr_eq(&self.context, &other.context)
    }
}

impl<T: PartialEq> Object<T> {
    fn new(
        attributes: Vec<Attribute<T>>,
        parent_context: Rc<RefCell<Context<Value>>>,
        parent_ftable: Rc<RefCell<Context<Function>>>,
    ) -> Self {
        Self {
            attributes: attributes.into(),
            ftable: Rc::new(RefCell::new(Context::with_parent(parent_ftable))),
            context: Rc::new(RefCell::new(Context::with_parent(parent_context))),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Attribute<T> {
    Value(Rc<RefCell<T>>),
    Children(Box<Vec<Attribute<T>>>),
}

#[derive(Debug, Clone)]
pub(crate) struct Function {
    pub(crate) name: Id,
    args: Vec<Id>,
    body: Body,
}

impl Function {
    pub(crate) fn new(name: Id, args: Vec<Id>, body: Body) -> Self {
        Self { name, args, body }
    }

    pub(crate) fn call_with_args(
        &self,
        pair: &Pair<Rule>,
        args: &[Expression],
    ) -> ParseResult<Value> {
        if self.args.len() != args.len() {
            return Err(custom_error(
                pair,
                &format!("expected {} arguments, got {}", self.args.len(), args.len()),
            ));
        }

        {
            let context = self.body.get_context();
            let mut context = context.borrow_mut();
            let ftable = self.body.get_ftable();
            let ftable = ftable.borrow();

            for (n, arg) in args.iter().enumerate() {
                let value = arg.eval(pair, &mut context, &ftable)?;
                context.assign_var(pair, self.args[n].clone(), value)?;
            }
        }

        self.body.eval(pair)
    }
}

/// ID representation.
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub(crate) struct Id(String);

impl Id {
    pub(crate) fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

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

pub(crate) fn parse_func_def(
    pair: Pair<Rule>,
    context: Rc<RefCell<Context<Value>>>,
    ftable: Rc<RefCell<Context<Function>>>,
) -> ParseResult<Function> {
    let mut inner = pair.into_inner();
    let id_pair = inner.next().unwrap();
    if RESERVED_WORDS.contains(id_pair.as_str()) {
        return Err(custom_error(
            &id_pair,
            &format!("{} is a reserved keyword", id_pair.as_str()),
        ));
    }

    let id = id_pair.as_str().into();
    let args = parse_func_args(inner.next().unwrap())?;
    let body = expression::parse_expr_body(inner.next().unwrap(), context, ftable)?;

    Ok(Function::new(id, args, body))
}

fn parse_func_args(pair: Pair<Rule>) -> ParseResult<Vec<Id>> {
    pair.into_inner().map(|id| Ok(id.as_str().into())).collect()
}

#[cfg(test)]
mod test {
    use pest::Parser;

    use crate::parser::{Rule, SparkMLParser};

    use super::*;

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
        let function = parse_func_def(pair, context, ftable).unwrap();

        assert_eq!(function.name, "foo".into());
        assert_eq!(function.args, vec!["a".into(), "b".into()]);
    }
}
