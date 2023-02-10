//! Value is a concrete stateful data structure.

use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;

use im::Vector;

use crate::parser::ast::Body;

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
        Rc::ptr_eq(&self.attributes, &other.attributes) && self.body == other.body
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

impl<T> PartialEq for Attribute<T> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Value(a), Self::Value(b)) => Rc::ptr_eq(a, b),
            (Self::Attributes(a), Self::Attributes(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
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
