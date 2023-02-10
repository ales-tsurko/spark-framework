//! Expression is something, that will happen later. Expression can be evaluated to a value.

use std::cell::RefCell;
use std::rc::Rc;

use im::Vector;
use pest::iterators::Pair;

use crate::parser::context::Context;
use crate::parser::value::{
    parse_func_def, Attribute, Attributes, Function, Id, Key, Object, Value,
};
use crate::parser::{custom_error, ParseResult, Rule, RESERVED_WORDS};

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum Expression {
    // Assignment is actually a statement, but we need to treat it as an expression in case of
    // assignments inside a function, they can be dependent on the function arguments in that case.
    // So we reevaluate them each time, we call the function.
    Assignment(Id, Box<Expression>),
    Object(Object<Expression>),
    Value(Value),
    FunctionCall(Id, Vec<Expression>),
    Variable(Id),
    If,
    Repeat,
    Algebraic,
    Boolean,
    List(Vector<Expression>),
    ListIndex(Box<Expression>, Box<Expression>),
    PropertyCall(Vec<Expression>),
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

            Expression::FunctionCall(id, args) => {
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

    pub(crate) fn expressions(&self) -> &Vec<Expression> {
        &self.expressions
    }

    pub(crate) fn context(&self) -> Rc<RefCell<Context<Value>>> {
        self.context.clone()
    }

    pub(crate) fn ftable(&self) -> Rc<RefCell<Context<Function>>> {
        self.ftable.clone()
    }
}

pub(crate) fn parse_expression(
    pair: Pair<Rule>,
    parent_context: Rc<RefCell<Context<Value>>>,
    parent_ftable: Rc<RefCell<Context<Function>>>,
) -> ParseResult<Expression> {
    match pair.as_rule() {
        Rule::node => todo!(),
        Rule::object => parse_object(pair, parent_context, parent_ftable),
        Rule::assignment => parse_assignment(pair, parent_context, parent_ftable),
        Rule::if_expr => todo!(),
        Rule::repeat_expr => todo!(),
        Rule::algebraic_expr => todo!(),
        Rule::bool_expr => todo!(),
        Rule::BOOL => Ok(Expression::Value(Value::Boolean(
            pair.as_str().parse().unwrap(),
        ))),
        Rule::call => parse_call(
            pair.into_inner().next().unwrap(),
            parent_context,
            parent_ftable,
        ),
        Rule::list => Ok(Expression::List(
            pair.into_inner()
                .map(|item| parse_expression(item, parent_context.clone(), parent_ftable.clone()))
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

pub(crate) fn parse_object(
    pair: Pair<Rule>,
    parent_context: Rc<RefCell<Context<Value>>>,
    parent_ftable: Rc<RefCell<Context<Function>>>,
) -> ParseResult<Expression> {
    assert!(matches!(pair.as_rule(), Rule::object));

    let pairs = pair.into_inner();
    let context = Rc::new(RefCell::new(Context::with_parent(parent_context)));
    let ftable = Rc::new(RefCell::new(Context::with_parent(parent_ftable)));

    let (attributes, properties) = pairs.fold(
        (Ok(Attributes::default()), Ok(Vec::new())),
        |(mut attributes, mut properties), pair| {
            match pair.as_rule() {
                Rule::attributes => {
                    attributes = parse_attributes(pair, Rc::clone(&context), Rc::clone(&ftable));
                }

                Rule::properties => {
                    properties = parse_properties(pair, Rc::clone(&context), Rc::clone(&ftable));
                }

                _ => unreachable!(),
            }

            (attributes, properties)
        },
    );

    let body = Body::new(context, ftable, properties?);

    Ok(Expression::Object(Object::new(Rc::new(attributes?), body)))
}

fn parse_attributes(
    pair: Pair<Rule>,
    context: Rc<RefCell<Context<Value>>>,
    ftable: Rc<RefCell<Context<Function>>>,
) -> ParseResult<Attributes<Expression>> {
    assert!(matches!(pair.as_rule(), Rule::attributes));

    let mut attributes = Attributes::default();

    for pair in pair.into_inner() {
        let mut pairs = pair.into_inner();
        let key_pair = pairs.next().unwrap();
        let value_pair = pairs.next().unwrap();
        let key = match key_pair.as_rule() {
            Rule::KEY => Key::Key(key_pair.as_str().into()),
            Rule::METAKEY => Key::MetaKey(key_pair.as_str().into()),
            _ => unreachable!(),
        };

        match value_pair.as_rule() {
            Rule::attributes => attributes.insert(
                key,
                Attribute::Attributes(Rc::new(parse_attributes(
                    value_pair,
                    context.clone(),
                    ftable.clone(),
                )?)),
            ),

            _ => attributes.insert(
                key,
                Attribute::Value(Rc::new(parse_expression(
                    value_pair,
                    context.clone(),
                    ftable.clone(),
                )?)),
            ),
        }
    }

    Ok(attributes)
}

fn parse_properties(
    pair: Pair<Rule>,
    context: Rc<RefCell<Context<Value>>>,
    ftable: Rc<RefCell<Context<Function>>>,
) -> ParseResult<Vec<Expression>> {
    assert!(matches!(pair.as_rule(), Rule::properties));

    let properties = pair.into_inner();
    let mut ftable_ref = ftable.borrow_mut();
    let mut expressions = Vec::new();

    for property in properties {
        match property.as_rule() {
            Rule::func_def => {
                let func_def =
                    parse_func_def(property.clone(), Rc::clone(&context), Rc::clone(&ftable))?;
                ftable_ref.add_func_def(&property, func_def)?;
            }

            Rule::assignment => {
                expressions.push(parse_assignment(
                    property,
                    Rc::clone(&context),
                    Rc::clone(&ftable),
                )?);
            }

            _ => unreachable!(),
        }
    }

    Ok(expressions)
}

pub(crate) fn parse_assignment(
    pair: Pair<Rule>,
    context: Rc<RefCell<Context<Value>>>,
    ftable: Rc<RefCell<Context<Function>>>,
) -> ParseResult<Expression> {
    assert!(matches!(pair.as_rule(), Rule::assignment));

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
        Box::new(parse_expression(expression, context, ftable)?),
    ))
}

pub(crate) fn parse_call(
    pair: Pair<Rule>,
    context: Rc<RefCell<Context<Value>>>,
    ftable: Rc<RefCell<Context<Function>>>,
) -> ParseResult<Expression> {
    match pair.as_rule() {
        Rule::property_call => todo!(),

        Rule::list_index => {
            let mut inner = pair.into_inner();
            // NOTE: it can be call only, but not wrapped into Rule::call
            let expression = parse_call(inner.next().unwrap(), context.clone(), ftable.clone())?;
            let indices = inner
                .map(|pair| parse_expression(pair, context.clone(), ftable.clone()))
                .collect::<ParseResult<Vec<Expression>>>()?;

            Ok(indices.into_iter().fold(expression, |acc, index| {
                Expression::ListIndex(Box::new(acc), Box::new(index))
            }))
        }

        Rule::fn_call => {
            let mut inner = pair.into_inner();
            let id: Id = inner.next().unwrap().as_str().into();
            let args = inner
                .map(|pair| parse_expression(pair, context.clone(), ftable.clone()))
                .collect::<ParseResult<Vec<Expression>>>()?;
            Ok(Expression::FunctionCall(id, args))
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
        .map(|pair| parse_expression(pair, context.clone(), ftable.clone()))
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
    fn test_parse_object() {
        let context = Rc::new(RefCell::new(Context::<Value>::default()));
        let ftable = Rc::new(RefCell::new(Context::<Function>::default()));
        let pair = SparkMLParser::parse(
            Rule::expression,
            r#"{ 
                 foo: test()
                 bar:
                    @child: 0.1
                 baz: 1

                 n = 1
                 fn test()
                     n }"#,
        )
        .unwrap()
        .next()
        .unwrap();
        let expr = parse_object(pair, context, ftable).unwrap();

        if let Expression::Object(object) = expr {
            assert_eq!(object.attributes().table().len(), 3);

            match object.attributes().get(&Key::Key("foo".into())) {
                Some(Attribute::Value(value)) => {
                    assert!(matches!(value.as_ref(), &Expression::FunctionCall(_, _)));
                }
                _ => panic!("Expected value"),
            }

            match object.attributes().get(&Key::Key("bar".into())) {
                Some(Attribute::Attributes(attrs)) => {
                    match attrs.get(&Key::MetaKey("@child".into())) {
                        Some(Attribute::Value(value)) => {
                            assert!(matches!(
                                value.as_ref(),
                                &Expression::Value(Value::Number(_))
                            ));
                        }
                        _ => panic!("Expected value"),
                    }
                }
                _ => panic!("Expected value"),
            }

            match object.body().expressions().as_slice() {
                [Expression::Assignment(id, expr)] => {
                    assert_eq!(id, &"n".into());
                    assert!(matches!(
                        expr.as_ref(),
                        &Expression::Value(Value::Number(_))
                    ));
                }
                _ => panic!("Expected assignment"),
            }

            match object
                .body()
                .ftable()
                .borrow()
                .get_non_recursive(&"test".into())
            {
                Some(func_def) => {
                    assert_eq!(func_def.name(), &"test".into());
                    assert_eq!(func_def.args(), vec![]);
                }
                _ => panic!("Expected function"),
            }
        } else {
            panic!("Expected object");
        }
    }

    #[test]
    fn test_parse_expression_assignment() {
        let context = Rc::new(RefCell::new(Context::<Value>::default()));
        let ftable = Rc::new(RefCell::new(Context::<Function>::default()));
        let mut context_ref = context.borrow_mut();
        let ftable_ref = ftable.borrow();
        let pair = SparkMLParser::parse(Rule::assignment, "foo = true")
            .unwrap()
            .next()
            .unwrap();
        let assignment = parse_assignment(pair.clone(), context.clone(), ftable.clone()).unwrap();
        assert_eq!(
            assignment
                .eval(&pair, &mut context_ref, &ftable_ref)
                .unwrap(),
            Value::Boolean(true)
        );

        assert_eq!(
            context_ref.get_non_recursive(&"foo".into()).unwrap(),
            &Value::Boolean(true)
        );

        // using reserved keyword is not allowed
        let pair = SparkMLParser::parse(Rule::assignment, "true = false")
            .unwrap()
            .next()
            .unwrap();
        assert!(parse_assignment(pair, context.clone(), ftable.clone()).is_err());
    }

    #[test]
    fn test_expression_call() {
        let context = Rc::new(RefCell::new(Context::<Value>::default()));
        let ftable = Rc::new(RefCell::new(Context::<Function>::default()));
        let pair = SparkMLParser::parse(Rule::call, "foo")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair, context.clone(), ftable.clone()).unwrap(),
            Expression::Variable("foo".into())
        );

        let pair = SparkMLParser::parse(Rule::call, "foo(true, false)")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair, context.clone(), ftable.clone()).unwrap(),
            Expression::FunctionCall(
                "foo".into(),
                vec![
                    Expression::Value(Value::Boolean(true)),
                    Expression::Value(Value::Boolean(false))
                ]
            )
        );

        let mut context_ref = context.borrow_mut();
        let ftable_ref = ftable.borrow();
        let pair = SparkMLParser::parse(Rule::assignment, "foo = [[4,3],[2,1]]")
            .unwrap()
            .next()
            .unwrap();

        assert!(
            parse_expression(pair.clone(), context.clone(), ftable.clone())
                .unwrap()
                .eval(&pair, &mut context_ref, &ftable_ref)
                .is_ok()
        );

        let pair = SparkMLParser::parse(Rule::call, "foo[0][1]")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone(), context.clone(), ftable.clone())
                .unwrap()
                .eval(&pair, &mut context_ref, &ftable_ref)
                .unwrap(),
            Value::Number(3.0)
        );

        let pair = SparkMLParser::parse(Rule::call, "foo[1][1]")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone(), context.clone(), ftable.clone())
                .unwrap()
                .eval(&pair, &mut context_ref, &ftable_ref)
                .unwrap(),
            Value::Number(1.0)
        );
    }

    #[test]
    fn test_expression_list() {
        let context = Rc::new(RefCell::new(Context::<Value>::default()));
        let ftable = Rc::new(RefCell::new(Context::<Function>::default()));
        let mut context_ref = context.borrow_mut();
        let ftable_ref = ftable.borrow();
        let pair = SparkMLParser::parse(Rule::expression, "[true,false,false]")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair.clone(), context.clone(), ftable.clone())
                .unwrap()
                .eval(&pair, &mut context_ref, &ftable_ref)
                .unwrap(),
            Value::List(vector![
                Value::Boolean(true),
                Value::Boolean(false),
                Value::Boolean(false)
            ])
        );
    }

    #[test]
    fn test_expression_value() {
        let context = Rc::new(RefCell::new(Context::<Value>::default()));
        let ftable = Rc::new(RefCell::new(Context::<Function>::default()));
        let mut context_ref = context.borrow_mut();
        let ftable_ref = ftable.borrow();
        let pair = SparkMLParser::parse(Rule::expression, "1")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair.clone(), context.clone(), ftable.clone())
                .unwrap()
                .eval(&pair, &mut context_ref, &ftable_ref)
                .unwrap(),
            Value::Number(1.0)
        );

        let pair = SparkMLParser::parse(Rule::expression, "1.0")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair.clone(), context.clone(), ftable.clone())
                .unwrap()
                .eval(&pair, &mut context_ref, &ftable_ref)
                .unwrap(),
            Value::Number(1.0)
        );

        let pair = SparkMLParser::parse(Rule::expression, "1E-2")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair.clone(), context.clone(), ftable.clone())
                .unwrap()
                .eval(&pair, &mut context_ref, &ftable_ref)
                .unwrap(),
            Value::Number(0.01)
        );

        let pair = SparkMLParser::parse(Rule::expression, r#""This is a string\nhello""#)
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair.clone(), context.clone(), ftable.clone())
                .unwrap()
                .eval(&pair, &mut context_ref, &ftable_ref)
                .unwrap(),
            Value::String("This is a string\\nhello".to_string())
        );

        let pair = SparkMLParser::parse(Rule::expression, r#"`NodePath("Path:")`"#)
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair.clone(), context.clone(), ftable.clone())
                .unwrap()
                .eval(&pair, &mut context_ref, &ftable_ref)
                .unwrap(),
            Value::GdValue("NodePath(\"Path:\")".to_string())
        );

        let pair = SparkMLParser::parse(Rule::expression, "true")
            .unwrap()
            .next()
            .unwrap();
        assert!(matches!(
            parse_expression(pair.clone(), context.clone(), ftable.clone())
                .unwrap()
                .eval(&pair, &mut context_ref, &ftable_ref),
            Ok(Value::Boolean(true))
        ));

        let pair = SparkMLParser::parse(Rule::expression, "false")
            .unwrap()
            .next()
            .unwrap();
        assert!(matches!(
            parse_expression(pair.clone(), context.clone(), ftable.clone())
                .unwrap()
                .eval(&pair, &mut context_ref, &ftable_ref),
            Ok(Value::Boolean(false))
        ));
    }
}
