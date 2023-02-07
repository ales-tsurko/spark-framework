use std::cell::RefCell;
use std::rc::Rc;

use im::Vector;
use pest::iterators::Pair;

use crate::parser::context::Context;
use crate::parser::value::{Function, Id, Object, Value};
use crate::parser::{custom_error, ParseResult, Rule, RESERVED_WORDS};

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum Expression {
    Assignment(Id, Box<Expression>),
    Value(Value),
    Object(Object<Expression>),
    Function(Id, Vec<Expression>),
    Variable(Id),
    If,
    Repeat,
    Algebraic,
    Boolean,
    List(Vector<Expression>),
    ListIndex(Box<Expression>, Box<Expression>),
    CallChain(Vec<Expression>),
}

impl Expression {
    pub(crate) fn eval(
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
                if let Some(function) = ftable.get_recursive(&id) {
                    function.call_with_args(pair, args)
                } else {
                    Err(custom_error(
                        pair,
                        &format!("Function '{}' not found", id.as_str()),
                    ))
                }
            }

            Expression::List(list) => Ok(Value::List(
                list.iter()
                    .map(|expr| expr.eval(pair, context, ftable))
                    .collect::<ParseResult<Vector<Value>>>()?,
            )),

            Expression::Variable(id) => context
                .get_recursive(id)
                .ok_or_else(|| custom_error(pair, &format!("'{}' not found", id.as_str()))),

            Expression::ListIndex(expression, index) => {
                if let Value::List(value) = expression.eval(pair, context, ftable)? {
                    if let Value::Number(index) = index.eval(pair, context, ftable)? {
                        let index = index as usize;
                        value.get(index).cloned().ok_or_else(|| {
                            custom_error(pair, &format!("Index '{}' is out of bounds", index))
                        })
                    } else {
                        Err(custom_error(pair, "Index should be a number"))
                    }
                } else {
                    Err(custom_error(pair, "Only lists can be indexed"))
                }
            }
            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Body {
    expressions: Box<Vec<Expression>>,
    context: Rc<RefCell<Context<Value>>>,
    ftable: Rc<RefCell<Context<Function>>>,
}

impl Body {
    pub(crate) fn new(
        context: Rc<RefCell<Context<Value>>>,
        ftable: Rc<RefCell<Context<Function>>>,
        expressions: Vec<Expression>,
    ) -> Self {
        Self {
            context,
            ftable,
            expressions: Box::new(expressions),
        }
    }

    pub(crate) fn eval(&self, pair: &Pair<Rule>) -> ParseResult<Value> {
        let ftable = (*self.ftable).borrow();
        let mut context = (*self.context).borrow_mut();
        let (last, rest) = self.expressions.split_last().unwrap();

        for expression in rest {
            expression.eval(pair, &mut context, &ftable)?;
        }

        last.eval(pair, &mut context, &ftable)
    }
    
    pub(crate) fn get_context(&self) -> Rc<RefCell<Context<Value>>> {
        self.context.clone()
    }

    pub(crate) fn get_ftable(&self) -> Rc<RefCell<Context<Function>>> {
        self.ftable.clone()
    }
}

pub(crate) fn parse_expression(pair: Pair<Rule>) -> ParseResult<Expression> {
    match pair.as_rule() {
        Rule::node => todo!(),
        Rule::object => parse_object(pair),
        Rule::assignment => parse_assignment(pair),
        Rule::if_expr => todo!(),
        Rule::repeat_expr => todo!(),
        Rule::algebraic_expr => todo!(),
        Rule::bool_expr => todo!(),
        Rule::BOOL => Ok(Expression::Value(Value::Boolean(
            pair.as_str().parse().unwrap(),
        ))),
        Rule::call => parse_call(pair.into_inner().next().unwrap()),
        Rule::list => Ok(Expression::List(
            pair.into_inner()
                .map(parse_expression)
                .collect::<ParseResult<Vector<Expression>>>()?,
        )),
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

pub(crate) fn parse_object(pair: Pair<Rule>) -> ParseResult<Expression> {
    dbg!(pair.as_rule());
    todo!()
}

pub(crate) fn parse_assignment(pair: Pair<Rule>) -> ParseResult<Expression> {
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
        Box::new(parse_expression(expression)?),
    ))
}

pub(crate) fn parse_call(pair: Pair<Rule>) -> ParseResult<Expression> {
    match pair.as_rule() {
        Rule::call_chain => todo!(),

        Rule::list_index => {
            let mut inner = pair.into_inner();
            // NOTE: it can be call only, but not wrapped into Rule::call
            let expression = parse_call(inner.next().unwrap())?;
            let indices = inner
                .map(parse_expression)
                .collect::<ParseResult<Vec<Expression>>>()?;

            Ok(indices.into_iter().fold(expression, |acc, index| {
                Expression::ListIndex(Box::new(acc), Box::new(index))
            }))
        }

        Rule::fn_call => {
            let mut inner = pair.into_inner();
            let id: Id = inner.next().unwrap().as_str().into();
            let args = inner
                .map(parse_expression)
                .collect::<ParseResult<Vec<Expression>>>()?;
            Ok(Expression::Function(id, args))
        }

        Rule::var_call => Ok(Expression::Variable(pair.into_inner().as_str().into())),

        _ => unreachable!(),
    }
}

pub(crate) fn parse_expr_body(
    pair: Pair<Rule>,
    parent_context: Rc<RefCell<Context<Value>>>,
    ftable: Rc<RefCell<Context<Function>>>,
) -> ParseResult<Body> {
    let context = Rc::new(RefCell::new(Context::<Value>::with_parent(parent_context)));
    let expressions: Vec<Expression> = pair
        .into_inner()
        .map(parse_expression)
        .collect::<ParseResult<Vec<Expression>>>()?;

    Ok(Body::new(context, ftable, expressions))
}

#[cfg(test)]
mod tests {
    use im::vector;
    use pest::Parser;

    use crate::parser::SparkMLParser;

    use super::*;

    #[test]
    fn test_parse_expression_assignment() {
        let mut context = Context::<Value>::default();
        let ftable = Context::<Function>::default();
        let pair = SparkMLParser::parse(Rule::assignment, "foo = true")
            .unwrap()
            .next()
            .unwrap();
        let assignment = parse_assignment(pair.clone()).unwrap();
        assert_eq!(
            assignment.eval(&pair, &mut context, &ftable).unwrap(),
            Value::Boolean(true)
        );

        assert_eq!(
            context.get_non_recursive(&"foo".into()).unwrap(),
            &Value::Boolean(true)
        );

        // using reserved keyword is not allowed
        let pair = SparkMLParser::parse(Rule::assignment, "true = false")
            .unwrap()
            .next()
            .unwrap();
        assert!(parse_assignment(pair).is_err());
    }

    #[test]
    fn test_expression_call() {
        let pair = SparkMLParser::parse(Rule::call, "foo")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair).unwrap(),
            Expression::Variable("foo".into())
        );

        let pair = SparkMLParser::parse(Rule::call, "foo(true, false)")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair).unwrap(),
            Expression::Function(
                "foo".into(),
                vec![
                    Expression::Value(Value::Boolean(true)),
                    Expression::Value(Value::Boolean(false))
                ]
            )
        );

        let mut context = Context::<Value>::default();
        let ftable = Context::<Function>::default();
        let pair = SparkMLParser::parse(Rule::assignment, "foo = [[4,3],[2,1]]")
            .unwrap()
            .next()
            .unwrap();

        assert!(parse_expression(pair.clone())
            .unwrap()
            .eval(&pair, &mut context, &ftable)
            .is_ok());

        let pair = SparkMLParser::parse(Rule::call, "foo[0][1]")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, &mut context, &ftable)
                .unwrap(),
            Value::Number(3.0)
        );

        let pair = SparkMLParser::parse(Rule::call, "foo[1][1]")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, &mut context, &ftable)
                .unwrap(),
            Value::Number(1.0)
        );
    }

    #[test]
    fn test_expression_list() {
        let mut context = Context::<Value>::default();
        let ftable = Context::<Function>::default();
        let pair = SparkMLParser::parse(Rule::expression, "[true,false,false]")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, &mut context, &ftable)
                .unwrap(),
            Value::List(vector![
                Value::Boolean(true),
                Value::Boolean(false),
                Value::Boolean(false)
            ])
        );
    }

    #[test]
    fn test_expression_object() {
        let pair = SparkMLParser::parse(
            Rule::expression,
            r#"object
                 n = 1

                 foo: test()
                 bar:
                    child: 0.1

                 fn test()
                    n"#,
        )
        .unwrap()
        .next()
        .unwrap();

        dbg!(pair);
    }

    #[test]
    fn test_expression_value() {
        let mut context = Context::<Value>::default();
        let ftable = Context::<Function>::default();
        let pair = SparkMLParser::parse(Rule::expression, "1")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair.clone())
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
            parse_expression(pair.clone())
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
            parse_expression(pair.clone())
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
            parse_expression(pair.clone())
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
            parse_expression(pair.clone())
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
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, &mut context, &ftable),
            Ok(Value::Boolean(true))
        ));

        let pair = SparkMLParser::parse(Rule::expression, "false")
            .unwrap()
            .next()
            .unwrap();
        assert!(matches!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, &mut context, &ftable),
            Ok(Value::Boolean(false))
        ));
    }
}
