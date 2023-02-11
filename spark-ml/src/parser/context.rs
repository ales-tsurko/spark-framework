use std::cell::RefCell;
use std::collections::HashMap;
use std::mem;
use std::rc::Rc;

use pest::iterators::Pair;

use crate::parser::ast::FunctionDef;
use crate::parser::value::{Id, Value};
use crate::parser::{custom_error, ParseResult, Rule};

/// Context is a scoped storage for variables and functions.
#[derive(Debug, Default, Clone)]
pub(crate) struct Context {
    variables: Table<Value>,
    functions: Table<FunctionDef>,
}

impl Context {
    pub(crate) fn with_parent(parent: Self) -> Self {
        let variables = Table::with_parent(parent.variables);
        let functions = Table::with_parent(parent.functions);
        Self {
            variables,
            functions,
        }
    }

    /// Get a variable without looking parent tables.
    pub(crate) fn var_non_recursive(&self, id: &Id) -> Option<Value> {
        self.variables.table.borrow().get(id).cloned()
    }

    /// Get a function definition without looking parent tables.
    pub(crate) fn func_non_recursive(&self, id: &Id) -> Option<FunctionDef> {
        self.functions.table.borrow().get(id).cloned()
    }

    pub(crate) fn var_recursive(&self, id: &Id) -> Option<Value> {
        self.variables.get_recursive(id)
    }

    pub(crate) fn func_recursive(&self, id: &Id) -> Option<FunctionDef> {
        self.functions.get_recursive(id)
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
    pub(crate) fn add_func(&self, pair: &Pair<Rule>, func_def: FunctionDef) -> ParseResult<()> {
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
}

#[derive(Debug, Clone)]
pub(crate) struct Table<T> {
    table: Rc<RefCell<HashMap<Id, T>>>,
    parent: Option<Box<Self>>,
}

impl<T> Table<T> {
    pub(crate) fn with_parent(parent: Self) -> Self {
        Self {
            table: Default::default(),
            parent: Some(Box::new(parent)),
        }
    }
}

impl<T: Clone> Table<T> {
    /// Get a value looking parent tables if necessary.
    pub(crate) fn get_recursive(&self, id: &Id) -> Option<T> {
        self.table
            .borrow()
            .get(id)
            .cloned()
            .or_else(|| {
                self.parent
                    .as_ref()
                    .and_then(|parent: &Box<Self>| parent.get_recursive(id))
            })
            .clone()
    }
}

impl<T> Default for Table<T> {
    fn default() -> Self {
        Self {
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
        assert!(context.var_non_recursive(&"foo".into()).is_none());

        assert!(context
            .add_var(&pair, "foo".into(), Value::Boolean(true))
            .is_ok());

        assert!(matches!(
            context.var_non_recursive(&"foo".into()),
            Some(Value::Boolean(true))
        ));

        // re-assign a variable
        assert!(context
            .add_var(&pair, "foo".into(), Value::Boolean(false))
            .is_ok());

        assert!(matches!(
            context.var_non_recursive(&"foo".into()),
            Some(Value::Boolean(false))
        ));

        // type mismatch
        assert!(context
            .add_var(&pair, "foo".into(), Value::Number(1.0))
            .is_err());

        // recursive lookup
        let child = Context::with_parent(context.clone());

        assert_eq!(
            child.var_recursive(&"foo".into()),
            Some(Value::Boolean(false))
        );
    }
}
