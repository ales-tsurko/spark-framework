//! Value is a concrete data structure.

use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::Hash;
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
pub(crate) struct Object<T> {
    attributes: Rc<Attributes<T>>,
    body: Body,
}

impl<T: PartialEq> PartialEq for Object<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.attributes, &other.attributes)
            && Rc::ptr_eq(&self.body.context(), &other.body.context())
            && Rc::ptr_eq(&self.body.ftable(), &other.body.ftable())
    }
}

impl<T> Object<T> {
    pub(crate) fn new(attributes: Rc<Attributes<T>>, body: Body) -> Self {
        Self { attributes, body }
    }
    
    pub(crate) fn attributes(&self) -> &Attributes<T> {
        &self.attributes
    }
    
    pub(crate) fn body(&self) -> &Body {
        &self.body
    }
}

impl Object<Expression> {
    pub(crate) fn eval(&self, pair: &Pair<Rule>) -> ParseResult<Object<Value>> {
        let context = self.body.context();
        let ftable = self.body.ftable();
        let mut context = context.borrow_mut();
        let ftable = ftable.borrow();
        let _ = self.body.eval(pair)?;
        let attributes = Rc::new(self.attributes.eval(pair, &mut context, &ftable)?);
        Ok(Object::new(attributes, self.body.clone()))
    }
}

impl Object<Value> {
    /// Property access is just a non-recursive call in the context of the object.
    pub(crate) fn access_propery(&self, pair: &Pair<Rule>, call: Expression) -> ParseResult<Value> {
        call.eval(
            pair,
            &mut self.body.context().borrow_mut(),
            &self.body.ftable().borrow(),
        )
    }
}

#[derive(Debug)]
pub(crate) struct Attributes<T>(HashMap<Key, Attribute<T>>);

impl<T> Default for Attributes<T> {
    fn default() -> Self {
        Self(HashMap::new())
    }
}

impl<T> Attributes<T> {
    pub(crate) fn insert(&mut self, key: Key, value: Attribute<T>) {
        let _ = self.0.insert(key, value);
    }
    
    pub(crate) fn get(&self, key: &Key) -> Option<&Attribute<T>> {
        self.0.get(key)
    }
    
    pub(crate) fn table(&self) -> &HashMap<Key, Attribute<T>> {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Key {
    Key(Id),
    MetaKey(Id),
}

impl Attributes<Expression> {
    pub(crate) fn eval(
        &self,
        pair: &Pair<Rule>,
        context: &mut Context<Value>,
        ftable: &Context<Function>,
    ) -> ParseResult<Attributes<Value>> {
        let mut table = HashMap::new();

        for (key, attr) in &self.0 {
            table.insert(key.clone(), attr.eval(pair, context, ftable)?);
        }

        Ok(Attributes(table))
    }
}

#[derive(Debug, Clone)]
pub(crate) enum Attribute<T> {
    Value(Rc<T>),
    Attributes(Rc<Attributes<T>>),
}

impl Attribute<Expression> {
    pub(crate) fn eval(
        &self,
        pair: &Pair<Rule>,
        context: &mut Context<Value>,
        ftable: &Context<Function>,
    ) -> ParseResult<Attribute<Value>> {
        match self {
            Self::Value(expr) => Ok(Attribute::Value(Rc::new(expr.eval(pair, context, ftable)?))),

            Self::Attributes(children) => Ok(Attribute::Attributes(Rc::new(
                children.eval(pair, context, ftable)?,
            ))),
        }
    }
}

impl<T> PartialEq for Attribute<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Value(a), Self::Value(b)) => Rc::ptr_eq(a, b),
            (Self::Attributes(a), Self::Attributes(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
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
            let context = self.body.context();
            let mut context = context.borrow_mut();
            let ftable = self.body.ftable();
            let ftable = ftable.borrow();

            for (n, arg) in args.iter().enumerate() {
                let value = arg.eval(pair, &mut context, &ftable)?;
                context.assign_var(pair, self.args[n].clone(), value)?;
            }
        }

        self.body.eval(pair)
    }
    
    pub(crate) fn name(&self) -> &Id {
        &self.name
    }

    pub(crate) fn args(&self) -> &[Id] {
        &self.args
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
