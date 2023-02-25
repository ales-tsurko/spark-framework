use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::mem;
use std::rc::Rc;

use pest::iterators::Pair;

use crate::parser::value::{Function, Id, Node, Signal, Tween, Value};
use crate::parser::{custom_error, ParseResult, Rule};

/// Context is a scoped storage for variables and functions.
#[derive(Debug, Clone)]
pub(crate) struct Context {
    variables: Table<Value>,
    functions: Table<Function>,
    nodes: Rc<RefCell<HashMap<Id, Rc<RefCell<Node<Id, Value, Tween<Value>, Signal>>>>>>,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            variables: Default::default(),
            functions: Default::default(),
            nodes: Rc::new(RefCell::new(HashMap::new())),
        }
    }
}

impl Context {
    pub(crate) fn with_parent(parent: Self) -> Self {
        let variables = Table::with_parent(parent.variables);
        let functions = Table::with_parent(parent.functions);
        Self {
            variables,
            functions,
            nodes: parent.nodes.clone(),
        }
    }

    pub(crate) fn parent(&self) -> Option<Self> {
        let variables = self.variables.parent()?;
        let functions = self.functions.parent()?;
        Some(Self {
            variables,
            functions,
            nodes: self.nodes.clone(),
        })
    }

    pub(crate) fn var(&self, id: &Id) -> Option<Value> {
        self.variables.get(id)
    }

    pub(crate) fn func(&self, id: &Id) -> Option<Function> {
        self.functions.get(id)
    }

    pub(crate) fn vars(&self) -> &Table<Value> {
        &self.variables
    }

    pub(crate) fn funcs(&self) -> &Table<Function> {
        &self.functions
    }

    /// Add a variable to the context.
    pub(crate) fn add_var(&self, pair: &Pair<Rule>, id: Id, value: Value) -> ParseResult<()> {
        let mut table = self.variables.table.borrow_mut();
        match table.get_mut(&id) {
            None => {
                table.insert(id, value);
                Ok(())
            }
            Some(val) => {
                if mem::discriminant(val) != mem::discriminant(&value) {
                    return Err(custom_error(
                        &pair,
                        &format!(
                            "Type mismatch: expected '{}' found '{}'",
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

    /// Add a function definition.
    pub(crate) fn add_func(&self, pair: &Pair<Rule>, func_def: Function) -> ParseResult<()> {
        let mut table = self.functions.table.borrow_mut();
        match table.get_mut(&func_def.name) {
            None => {
                table.insert(func_def.name.clone(), func_def);
                Ok(())
            }
            Some(_) => Err(custom_error(
                &pair,
                &format!("Function '{}' already defined", func_def.name.as_str()),
            )),
        }
    }

    /// Find the ancestor context that contains the given var.
    pub(crate) fn find_var_ancestor(&self, id: &Id) -> Option<Self> {
        if self.variables.table.borrow().contains_key(id) {
            Some(self.clone())
        } else {
            self.parent()
                .as_ref()
                .and_then(|parent| parent.find_var_ancestor(id))
        }
    }

    pub(crate) fn has_node(&self, id: &Id) -> bool {
        self.nodes.borrow().contains_key(id)
    }

    pub(crate) fn add_node(&self, node: Rc<RefCell<Node<Id, Value, Tween<Value>, Signal>>>) {
        let id = node.borrow().name.clone();
        self.nodes.borrow_mut().insert(id, node);
    }

    #[allow(dead_code)]
    pub(crate) fn get_node(
        &self,
        id: &Id,
    ) -> Option<Rc<RefCell<Node<Id, Value, Tween<Value>, Signal>>>> {
        self.nodes.borrow().get(id).cloned()
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Table<T> {
    recursive: Cell<bool>,
    table: Rc<RefCell<HashMap<Id, T>>>,
    parent: Option<Box<Self>>,
}

impl<T> Table<T> {
    pub(crate) fn with_parent(parent: Self) -> Self {
        Self {
            recursive: parent.recursive.clone(),
            table: Default::default(),
            parent: Some(Box::new(parent)),
        }
    }

    pub(crate) fn set_recursive(&self, value: bool) {
        self.recursive.set(value);
    }

    pub(crate) fn set_all_recursive(&self, value: bool) {
        self.recursive.set(value);
        if let Some(parent) = self.parent.as_ref() {
            parent.set_all_recursive(value);
        }
    }
}

impl<T: Clone> Table<T> {
    /// Get a value.
    pub(crate) fn get(&self, id: &Id) -> Option<T> {
        let value = self.table.borrow().get(id).cloned();

        if self.recursive.get() {
            value.or_else(|| {
                self.parent
                    .as_ref()
                    .and_then(|parent: &Box<Self>| parent.get(id))
            })
        } else {
            value
        }
    }

    pub(crate) fn parent(&self) -> Option<Self> {
        self.parent.as_ref().map(|p| *p.clone())
    }
}

impl<T> Default for Table<T> {
    fn default() -> Self {
        Self {
            recursive: Cell::new(true),
            table: Default::default(),
            parent: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use pest::Parser;

    use super::*;
    use crate::parser::SparkMLParser;

    #[test]
    fn test_context() {
        let context = Context::default();
        // we need it just to pass something
        let pair = SparkMLParser::parse(Rule::module, "\n")
            .unwrap()
            .next()
            .unwrap();

        // assign a variable
        assert!(context.var(&"foo".into()).is_none());

        assert!(context
            .add_var(&pair, "foo".into(), Value::Boolean(true))
            .is_ok());

        assert!(matches!(
            context.var(&"foo".into()),
            Some(Value::Boolean(true))
        ));

        // re-assign a variable
        assert!(context
            .add_var(&pair, "foo".into(), Value::Boolean(false))
            .is_ok());

        assert!(matches!(
            context.var(&"foo".into()),
            Some(Value::Boolean(false))
        ));

        // type mismatch
        assert!(context
            .add_var(&pair, "foo".into(), Value::Number(1.0))
            .is_err());

        // recursive lookup
        let child = Context::with_parent(context.clone());

        assert_eq!(child.var(&"foo".into()), Some(Value::Boolean(false)));

        // make it non-recursive
        child.vars().set_recursive(false);
        assert!(child.var(&"foo".into()).is_none());
    }
}
