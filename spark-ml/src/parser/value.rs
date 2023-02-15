//! Value is a concrete stateful data structure.

use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;

use pest::iterators::Pair;

use crate::parser::ast::{Ast, Body};
use crate::parser::context::Context;
use crate::parser::{custom_error, ParseResult, Rule};

#[derive(Debug, PartialEq, Clone)]
#[non_exhaustive]
pub(crate) enum Value {
    Node,
    Object(Object<Value>),
    String(String),
    Boolean(bool),
    List(Rc<RefCell<Vec<Value>>>),
    Number(f64),
    GdValue(String),
    Function(Function),
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
            Self::Function(_) => "Function",
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Object<T> {
    attributes: Rc<Attributes<T>>,
    context: Context,
    body: Body,
}

impl<T: PartialEq> PartialEq for Object<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.attributes, &other.attributes) && self.body == other.body
    }
}

impl<T> Object<T> {
    pub(crate) fn new(attributes: Rc<Attributes<T>>, body: Body, context: Context) -> Self {
        Self {
            attributes,
            body,
            context,
        }
    }

    pub(crate) fn attributes(&self) -> &Attributes<T> {
        &self.attributes
    }

    pub(crate) fn body(&self) -> &Body {
        &self.body
    }

    pub(crate) fn context(&self) -> &Context {
        &self.context
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
    pub(crate) fn new(table: HashMap<Key, Attribute<T>>) -> Self {
        Self(table)
    }

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

impl<T: PartialEq> PartialEq for Attributes<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Key {
    Key(Id),
    MetaKey(Id),
}

#[derive(Debug, Clone)]
pub(crate) enum Attribute<T> {
    Value(Rc<T>),
    Attributes(Rc<Attributes<T>>),
}

impl<T: PartialEq> PartialEq for Attribute<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Value(a), Self::Value(b)) => a == b,
            (Self::Attributes(a), Self::Attributes(b)) => a == b,
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Function {
    pub(crate) name: Id,
    args: Rc<Vec<Id>>,
    body: Body,
    context: Context,
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.args == other.args && self.body == other.body
    }
}

impl Function {
    pub(crate) fn new(name: Id, args: Vec<Id>, body: Body, caller_ctx: Context) -> Self {
        caller_ctx.vars().set_recursive(true);
        caller_ctx.funcs().set_recursive(true);

        let context = Context::with_parent(caller_ctx.clone());

        context.vars().set_recursive(false);
        context.funcs().set_recursive(true);

        Self {
            name,
            args: Rc::new(args),
            body,
            context,
        }
    }

    pub(crate) fn eval(
        &self,
        pair: &Pair<Rule>,
        args: &[Ast],
        caller_ctx: Context,
    ) -> ParseResult<Value> {
        if self.args.len() != args.len() {
            return Err(custom_error(
                pair,
                &format!("expected {} arguments, got {}", self.args.len(), args.len()),
            ));
        }

        for (n, arg) in args.iter().enumerate() {
            // args should be evaluated in the caller's context
            let value = arg.eval(pair, caller_ctx.clone())?;
            // and added to the function's context
            self.context.add_var(pair, self.args[n].clone(), value)?;
        }

        self.body.eval(pair, self.context.clone())
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
