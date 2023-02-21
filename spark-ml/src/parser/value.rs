//! Value is a concrete stateful data structure.

use std::cell::RefCell;
use std::hash::Hash;
use std::rc::Rc;

use indexmap::IndexMap;
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

impl ToString for Value {
    fn to_string(&self) -> String {
        match self {
            Self::Node => todo!(),
            Self::Object(obj) => obj.attributes().to_string(&mut vec![]),
            Self::String(s) => s.to_string(),
            Self::Boolean(b) => b.to_string(),
            Self::List(l) => l
                .borrow()
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            Self::Number(n) => n.to_string(),
            Self::GdValue(s) => s.to_string(),
            Self::Function(f) => f.name.as_str().to_string(),
        }
    }
}

macro_rules! impl_from {
    ($($val:ty,$var:ident),*) => {
        $(
            impl From<$val> for Value {
                fn from(v: $val) -> Self {
                    Self::$var(v)
                }
            }
        )*
    };
}

impl_from!(
    String,
    String,
    //
    bool,
    Boolean,
    //
    f64,
    Number,
    //
    Object<Value>,
    Object,
    //
    Function,
    Function
);

impl From<&str> for Value {
    fn from(s: &str) -> Self {
        Self::String(s.to_string())
    }
}

impl From<Vec<Value>> for Value {
    fn from(v: Vec<Value>) -> Self {
        Self::List(Rc::new(RefCell::new(v)))
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
pub(crate) struct Attributes<T>(IndexMap<Key, Attribute<T>>);

impl<T: ToString> Attributes<T> {
    fn to_string(&self, indent: &mut Vec<String>) -> String {
        let level = "  ";

        self.0
            .iter()
            .map(|(k, v)| match v {
                Attribute::Value(v) => {
                    format!("{}{}: {}", indent.join(""), k.to_string(), v.to_string())
                }
                Attribute::Attributes(attrs) => {
                    let indent_s = indent.join("");
                    indent.push(level.to_string());
                    let res = format!(
                        "{}{}:\n{}",
                        indent_s,
                        k.to_string(),
                        attrs.to_string(indent)
                    );
                    indent.pop();
                    res
                }
            })
            .collect::<Vec<String>>()
            .join("\n")
    }
}

impl<T> Default for Attributes<T> {
    fn default() -> Self {
        Self(IndexMap::new())
    }
}

impl<T> Attributes<T> {
    pub(crate) fn new(table: IndexMap<Key, Attribute<T>>) -> Self {
        Self(table)
    }

    pub(crate) fn insert(&mut self, key: Key, value: Attribute<T>) {
        let _ = self.0.insert(key, value);
    }

    #[allow(dead_code)]
    pub(crate) fn get(&self, key: &Key) -> Option<&Attribute<T>> {
        self.0.get(key)
    }

    pub(crate) fn table(&self) -> &IndexMap<Key, Attribute<T>> {
        &self.0
    }
}

impl<T: PartialEq> PartialEq for Attributes<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> From<IndexMap<Key, Attribute<T>>> for Attributes<T> {
    fn from(table: IndexMap<Key, Attribute<T>>) -> Self {
        Self(table)
    }
}

impl<T, const N: usize> From<[(Key, Attribute<T>); N]> for Attributes<T> {
    fn from(table: [(Key, Attribute<T>); N]) -> Self {
        Self(table.into())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Key {
    Key(Id),
    MetaKey(Id),
}

impl ToString for Key {
    fn to_string(&self) -> String {
        match self {
            Self::Key(id) | Self::MetaKey(id) => id.0.to_string(),
        }
    }
}

impl From<&str> for Key {
    fn from(s: &str) -> Self {
        if s.starts_with("@") {
            return Self::MetaKey(Id(s.to_string()));
        }
        Self::Key(Id(s.to_string()))
    }
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

impl From<Value> for Attribute<Value> {
    fn from(v: Value) -> Self {
        Self::Value(Rc::new(v))
    }
}

macro_rules! impl_from_value {
    ($($t:ty),*) => {
        $(
            impl From<$t> for Attribute<Value> {
                fn from(v: $t) -> Self {
                    Self::Value(Rc::new(v.into()))
                }
            }
        )*
    };
}

impl_from_value!(f64, bool, &str, String, Object<Value>, Vec<Value>, Function);

impl<T> From<Attributes<T>> for Attribute<T> {
    fn from(attrs: Attributes<T>) -> Self {
        Self::Attributes(Rc::new(attrs))
    }
}

impl<T> From<IndexMap<Key, Attribute<T>>> for Attribute<T> {
    fn from(table: IndexMap<Key, Attribute<T>>) -> Self {
        Self::Attributes(Rc::new(table.into()))
    }
}

impl<T, const N: usize> From<[(Key, Attribute<T>); N]> for Attribute<T> {
    fn from(table: [(Key, Attribute<T>); N]) -> Self {
        Self::Attributes(Rc::new(table.into()))
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_string() {
        let attrs: Attributes<Value> = [
            ("a".into(), 1.0.into()),
            (
                "b".into(),
                [("c".into(), 2.0.into()), ("d".into(), 3.0.into())].into(),
            ),
            (
                "e".into(),
                [("f".into(), [("g".into(), 4.0.into())].into())].into(),
            ),
            ("h".into(), 5.0.into()),
        ]
        .into();

        assert_eq!(
            "a: 1\nb:\n  c: 2\n  d: 3\ne:\n  f:\n    g: 4\nh: 5".to_string(),
            attrs.to_string(&mut vec![]),
        );
    }
}
