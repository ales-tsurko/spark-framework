use std::cell::RefCell;
use std::collections::HashMap;
use std::mem;
use std::rc::Rc;

use pest::iterators::Pair;

use super::value::{Function, Id, Value};
use super::{custom_error, ParseResult, Rule};

/// Context is a scoped storage for variables and functions.
#[derive(Debug)]
pub(crate) struct Context<T> {
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
    pub(crate) fn with_parent(parent: Rc<RefCell<Self>>) -> Self {
        Self {
            parent: Some(parent),
            table: HashMap::new(),
        }
    }

    /// Get a value from the table without looking parent tables.
    pub(crate) fn get_non_recursive(&self, id: &Id) -> Option<&T> {
        self.table.get(id)
    }
}

impl<T: Clone> Context<T> {
    /// Get a value from the table, looking parent tables if necessary.
    pub(crate) fn get_recursive(&self, id: &Id) -> Option<T> {
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
    pub(crate) fn assign_var(
        &mut self,
        pair: &Pair<Rule>,
        id: Id,
        value: Value,
    ) -> ParseResult<()> {
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
    pub(crate) fn add_func_def(
        &mut self,
        pair: &Pair<Rule>,
        func_def: Function,
    ) -> ParseResult<()> {
        match self.table.get_mut(&func_def.name) {
            None => {
                self.table.insert(func_def.name.clone(), func_def);
                Ok(())
            }
            Some(_) => Err(custom_error(
                &pair,
                &format!("Function {} already defined", func_def.name.as_str()),
            )),
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
}
