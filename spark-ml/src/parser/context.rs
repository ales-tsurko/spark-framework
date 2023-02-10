use std::cell::RefCell;
use std::collections::HashMap;
use std::mem;
use std::rc::Rc;

use pest::iterators::Pair;

use crate::parser::ast::FunctionDef;
use crate::parser::value::{Id, Value};
use crate::parser::{custom_error, ParseResult, Rule};

/// Context is a scoped storage for variables and functions.
#[derive(Debug, Default)]
pub(crate) struct Context {
    variables: Table<Value>,
    functions: Table<FunctionDef>,
    parent: Option<Rc<RefCell<Self>>>,
}

impl Context {
    pub(crate) fn with_parent(parent: Rc<RefCell<Self>>) -> Self {
        Self {
            parent: Some(parent),
            ..Default::default()
        }
    }

    /// Get a variable without looking parent tables.
    pub(crate) fn var_non_recursive(&self, id: &Id) -> Option<&Value> {
        self.variables.0.get(id)
    }

    /// Get a function definition without looking parent tables.
    pub(crate) fn func_non_recursive(&self, id: &Id) -> Option<&Value> {
        self.variables.0.get(id)
    }

    /// Get a variable looking parent tables if necessary.
    pub(crate) fn var_recursive(&self, id: &Id) -> Option<Value> {
        self.variables
            .get(id)
            .cloned()
            .or_else(|| {
                self.parent
                    .as_ref()
                    .and_then(|parent: &Rc<RefCell<Self>>| (*parent).borrow().var_recursive(id))
            })
            .clone()
    }
    /// Get a variable looking parent tables if necessary.
    pub(crate) fn func_recursive(&self, id: &Id) -> Option<FunctionDef> {
        self.functions
            .get(id)
            .cloned()
            .or_else(|| {
                self.parent
                    .as_ref()
                    .and_then(|parent: &Rc<RefCell<Self>>| (*parent).borrow().func_recursive(id))
            })
            .clone()
    }

    /// Add a variable to the context.
    pub(crate) fn add_var(&mut self, pair: &Pair<Rule>, id: Id, value: Value) -> ParseResult<()> {
        match self.variables.0.get_mut(&id) {
            None => {
                self.variables.0.insert(id, value);
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
    pub(crate) fn add_func(&mut self, pair: &Pair<Rule>, func_def: FunctionDef) -> ParseResult<()> {
        match self.functions.0.get_mut(&func_def.name) {
            None => {
                self.functions.0.insert(func_def.name.clone(), func_def);
                Ok(())
            }
            Some(_) => Err(custom_error(
                &pair,
                &format!("Function '{}' already defined", func_def.name.as_str()),
            )),
        }
    }

    pub(crate) fn variables(&self) -> &Table<Value> {
        &self.variables
    }

    pub(crate) fn functions(&self) -> &Table<FunctionDef> {
        &self.functions
    }

    pub(crate) fn set_variabels(&mut self, table: Table<Value>) {
        self.variables = table;
    }

    pub(crate) fn set_functions(&mut self, table: Table<FunctionDef>) {
        self.functions = table;
    }
}

#[derive(Debug)]
pub(crate) struct Table<T>(HashMap<Id, T>);

impl<T> Default for Table<T> {
    fn default() -> Self {
        Self(HashMap::new())
    }
}

impl<T> Table<T> {
    pub(crate) fn values(&self) -> impl Iterator<Item = &T> {
        self.0.values()
    }

    pub(crate) fn get(&self, id: &Id) -> Option<&T> {
        self.0.get(id)
    }
}

#[cfg(test)]
mod tests {
    use pest::Parser;

    use super::*;
    use crate::parser::SparkMLParser;

    #[test]
    fn test_context() {
        let context = Rc::new(RefCell::new(Context::default()));
        let mut context_ref = context.borrow_mut();
        // we need it just to pass something
        let pair = SparkMLParser::parse(Rule::module, "\n")
            .unwrap()
            .next()
            .unwrap();

        // assign a variable
        assert!(context_ref.var_non_recursive(&"foo".into()).is_none());

        assert!(context_ref
            .add_var(&pair, "foo".into(), Value::Boolean(true))
            .is_ok());

        assert!(matches!(
            context_ref.var_non_recursive(&"foo".into()),
            Some(Value::Boolean(true))
        ));

        // re-assign a variable
        assert!(context_ref
            .add_var(&pair, "foo".into(), Value::Boolean(false))
            .is_ok());

        assert!(matches!(
            context_ref.var_non_recursive(&"foo".into()),
            Some(Value::Boolean(false))
        ));

        // type mismatch
        assert!(context_ref
            .add_var(&pair, "foo".into(), Value::Number(1.0))
            .is_err());

        // recursive lookup
        drop(context_ref);
        let child = Rc::new(RefCell::new(Context::with_parent(context.clone())));
        let child_ref = child.borrow();

        assert_eq!(
            child_ref.var_recursive(&"foo".into()),
            Some(Value::Boolean(false))
        );
    }
}
