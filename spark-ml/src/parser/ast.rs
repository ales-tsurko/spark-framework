//! Abstract syntax tree.
use std::collections::HashMap;
use std::rc::Rc;

use im::Vector;
use pest::iterators::Pair;

use crate::parser::context::Context;
use crate::parser::value::{Attribute, Attributes, Id, Key, Object, Value};
use crate::parser::{custom_error, ParseResult, Rule, RESERVED_WORDS};

pub(crate) fn parse_expression(pair: Pair<Rule>) -> ParseResult<Ast> {
    match pair.as_rule() {
        Rule::node => todo!(),
        Rule::object => parse_object(pair),
        Rule::assignment => parse_assignment(pair),
        Rule::if_expr => todo!(),
        Rule::repeat_expr => todo!(),
        Rule::algebraic_expr => todo!(),
        Rule::bool_expr => todo!(),
        Rule::BOOL => Ok(Ast::Value(Value::Boolean(pair.as_str().parse().unwrap()))),
        Rule::call => parse_call(pair.into_inner().next().unwrap()),
        Rule::list => Ok(Ast::List(
            pair.into_inner()
                .map(|item| parse_expression(item))
                .collect::<ParseResult<Vector<Ast>>>()?,
        )),
        Rule::NUMBER => Ok(Ast::Value(Value::Number(pair.as_str().parse().unwrap()))),
        Rule::STRING => Ok(Ast::Value(Value::String(
            pair.into_inner().next().unwrap().as_str().into(),
        ))),
        Rule::GD_VALUE => Ok(Ast::Value(Value::GdValue(
            pair.into_inner().next().unwrap().as_str().into(),
        ))),
        _ => unreachable!(),
    }
}

pub(crate) fn parse_object(pair: Pair<Rule>) -> ParseResult<Ast> {
    assert!(matches!(pair.as_rule(), Rule::object));

    let pairs = pair.into_inner();

    let (attributes, properties) = pairs.fold(
        (Ok(Attributes::default()), Ok(Vec::new())),
        |(mut attributes, mut properties), pair| {
            match pair.as_rule() {
                Rule::attributes => {
                    attributes = parse_attributes(pair);
                }

                Rule::properties => {
                    properties = parse_properties(pair);
                }

                _ => unreachable!(),
            }

            (attributes, properties)
        },
    );

    let body = Body::new(properties?);

    Ok(Ast::Object(Object::new(Rc::new(attributes?), body)))
}

fn parse_attributes(pair: Pair<Rule>) -> ParseResult<Attributes<Ast>> {
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
                Attribute::Attributes(Rc::new(parse_attributes(value_pair)?)),
            ),

            _ => attributes.insert(
                key,
                Attribute::Value(Rc::new(parse_expression(value_pair)?)),
            ),
        }
    }

    Ok(attributes)
}

fn parse_properties(pair: Pair<Rule>) -> ParseResult<Vec<Ast>> {
    assert!(matches!(pair.as_rule(), Rule::properties));

    pair.into_inner()
        .map(|property| match property.as_rule() {
            Rule::func_def => parse_func_def(property),
            Rule::assignment => parse_assignment(property),
            _ => unreachable!(),
        })
        .collect()
}

pub(crate) fn parse_assignment(pair: Pair<Rule>) -> ParseResult<Ast> {
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

    Ok(Ast::Assignment(
        id.as_str().into(),
        Box::new(parse_expression(expression)?),
    ))
}

pub(crate) fn parse_call(pair: Pair<Rule>) -> ParseResult<Ast> {
    match pair.as_rule() {
        Rule::property_call => {
            let calls = pair
                .into_inner()
                .map(parse_call)
                .collect::<ParseResult<Vec<_>>>()?;
            Ok(Ast::PropertyCall(calls))
        }

        Rule::list_index => {
            let mut inner = pair.into_inner();
            // NOTE: it can be call only, but not wrapped into Rule::call
            let expression = parse_call(inner.next().unwrap())?;
            let indices = inner
                .map(parse_expression)
                .collect::<ParseResult<Vec<Ast>>>()?;

            Ok(indices.into_iter().fold(expression, |acc, index| {
                Ast::ListIndex(Box::new(acc), Box::new(index))
            }))
        }

        Rule::fn_call => {
            let mut inner = pair.into_inner();
            let id: Id = inner.next().unwrap().as_str().into();
            let args = inner
                .map(parse_expression)
                .collect::<ParseResult<Vec<Ast>>>()?;
            Ok(Ast::FunctionCall(id, args))
        }

        Rule::var_call => Ok(Ast::Variable(pair.into_inner().as_str().into())),

        _ => unreachable!(),
    }
}

pub(crate) fn parse_expr_body(pair: Pair<Rule>) -> ParseResult<Body> {
    let expressions: Vec<Ast> = pair
        .into_inner()
        .map(parse_expression)
        .collect::<ParseResult<Vec<Ast>>>()?;

    Ok(Body::new(expressions))
}

pub(crate) fn parse_func_def(pair: Pair<Rule>) -> ParseResult<Ast> {
    let mut inner = pair.into_inner();
    let id_pair = inner.next().unwrap();
    if RESERVED_WORDS.contains(id_pair.as_str()) {
        return Err(custom_error(
            &id_pair,
            &format!("'{}' is a reserved keyword", id_pair.as_str()),
        ));
    }

    let id = id_pair.as_str().into();
    let args = parse_func_args(inner.next().unwrap())?;
    let body = parse_expr_body(inner.next().unwrap())?;

    Ok(Ast::FunctionDef(FunctionDef::new(id, args, body)))
}

fn parse_func_args(pair: Pair<Rule>) -> ParseResult<Vec<Id>> {
    pair.into_inner().map(|id| Ok(id.as_str().into())).collect()
}

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum Ast {
    Assignment(Id, Box<Ast>),
    Object(Object<Ast>),
    Value(Value),
    FunctionCall(Id, Vec<Ast>),
    FunctionDef(FunctionDef),
    Variable(Id),
    If,
    Repeat,
    Algebraic,
    Boolean,
    List(Vector<Ast>),
    ListIndex(Box<Ast>, Box<Ast>),
    PropertyCall(Vec<Ast>),
}

impl Ast {
    pub(crate) fn eval(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Value> {
        match self {
            Ast::Value(val) => Ok(val.clone()),

            Ast::Assignment(id, expression) => {
                let value = expression.eval(pair, context.clone())?;
                context.add_var(pair, id.clone(), value.clone())?;
                Ok(value)
            }

            Ast::FunctionDef(func) => {
                context.add_func(pair, func.clone())?;
                Ok(Value::Boolean(true))
            }

            Ast::Object(object) => Ok(Value::Object(object.eval(pair, context.clone())?)),

            Ast::FunctionCall(id, args) => {
                if let Some(func) = context.func_recursive(&id) {
                    func.eval(pair, args, context.clone())
                } else {
                    Err(custom_error(
                        pair,
                        &format!("Function '{}' not found", id.as_str()),
                    ))
                }
            }

            Ast::List(list) => Ok(Value::List(
                list.iter()
                    .map(|expr| expr.eval(pair, context.clone()))
                    .collect::<ParseResult<Vector<Value>>>()?,
            )),

            Ast::Variable(id) => context
                .var_recursive(id)
                .ok_or_else(|| custom_error(pair, &format!("'{}' not found", id.as_str()))),

            Ast::ListIndex(expression, index) => {
                if let Value::List(value) = expression.eval(pair, context.clone())? {
                    if let Value::Number(index) = index.eval(pair, context)? {
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

impl Object<Ast> {
    pub(crate) fn eval(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Object<Value>> {
        let context = Context::with_parent(context.clone());
        let _ = self.body().eval(pair, context.clone())?;
        let attributes = Rc::new(self.attributes().eval(pair, context)?);
        Ok(Object::new(attributes, self.body().clone()))
    }
}

impl Attributes<Ast> {
    pub(crate) fn eval(
        &self,
        pair: &Pair<Rule>,
        context: Context,
    ) -> ParseResult<Attributes<Value>> {
        let mut table = HashMap::new();

        for (key, attr) in self.table() {
            table.insert(key.clone(), attr.eval(pair, context.clone())?);
        }

        Ok(Attributes::new(table))
    }
}

impl Attribute<Ast> {
    pub(crate) fn eval(
        &self,
        pair: &Pair<Rule>,
        context: Context,
    ) -> ParseResult<Attribute<Value>> {
        match self {
            Self::Value(expr) => Ok(Attribute::Value(Rc::new(expr.eval(pair, context)?))),

            Self::Attributes(children) => Ok(Attribute::Attributes(Rc::new(
                children.eval(pair, context)?,
            ))),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct FunctionDef {
    pub(crate) name: Id,
    args: Vec<Id>,
    body: Body,
}

impl FunctionDef {
    pub(crate) fn new(name: Id, args: Vec<Id>, body: Body) -> Self {
        Self { name, args, body }
    }

    pub(crate) fn eval(
        &self,
        pair: &Pair<Rule>,
        args: &[Ast],
        context: Context,
    ) -> ParseResult<Value> {
        if self.args.len() != args.len() {
            return Err(custom_error(
                pair,
                &format!("expected {} arguments, got {}", self.args.len(), args.len()),
            ));
        }

        let context = Context::with_parent(context.clone());

        for (n, arg) in args.iter().enumerate() {
            let value = arg.eval(pair, context.clone())?;
            context.add_var(pair, self.args[n].clone(), value)?;
        }

        self.body.eval(pair, context.clone())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Body {
    expressions: Box<Vec<Ast>>,
}

impl Body {
    pub(crate) fn new(expressions: Vec<Ast>) -> Self {
        Self {
            expressions: Box::new(expressions),
        }
    }

    pub(crate) fn eval(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Value> {
        let (last, rest) = self.expressions.split_last().unwrap();

        for expression in rest {
            expression.eval(pair, context.clone())?;
        }

        last.eval(pair, context)
    }
}

#[cfg(test)]
mod tests {
    use im::vector;
    use pest::Parser;

    use crate::parser::SparkMLParser;

    use super::*;

    #[test]
    fn test_parse_func_def() {
        let pair = SparkMLParser::parse(
            Rule::func_def,
            r#"fn foo(a, b)
                n = 10
                20"#,
        )
        .unwrap()
        .next()
        .unwrap();
        if let Ast::FunctionDef(function) = parse_func_def(pair).unwrap() {
            assert_eq!(function.name, "foo".into());
            assert_eq!(function.args, vec!["a".into(), "b".into()]);
            assert_eq!(function.body.expressions.len(), 2);
        } else {
            panic!("Expected function definition");
        }
    }

    #[test]
    fn test_object() {
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
        let expr = parse_object(pair.clone()).unwrap();

        if let Ast::Object(object) = expr.clone() {
            assert_eq!(object.attributes().table().len(), 3);

            match object.attributes().get(&Key::Key("foo".into())) {
                Some(Attribute::Value(value)) => {
                    assert!(matches!(value.as_ref(), &Ast::FunctionCall(_, _)));
                }
                _ => panic!("Expected value"),
            }

            match object.attributes().get(&Key::Key("bar".into())) {
                Some(Attribute::Attributes(attrs)) => {
                    match attrs.get(&Key::MetaKey("@child".into())) {
                        Some(Attribute::Value(value)) => {
                            assert!(matches!(value.as_ref(), &Ast::Value(Value::Number(_))));
                        }
                        _ => panic!("Expected value"),
                    }
                }
                _ => panic!("Expected value"),
            }

            match object.body().expressions.as_slice() {
                [Ast::Assignment(id, expr), Ast::FunctionDef(func)] => {
                    assert_eq!(id, &"n".into());
                    assert!(matches!(expr.as_ref(), &Ast::Value(Value::Number(_))));
                    assert_eq!(func.name, "test".into());
                    assert_eq!(func.args, vec![]);
                }
                _ => panic!("Expected assignment"),
            }
        } else {
            panic!("Expected object");
        }

        // test evaluation
        let context = Context::default();
        let object = expr.eval(&pair, context.clone()).unwrap();

        // object should have its own context (i.e. it shouldn't touch the parent context)
        assert_eq!(context.var_non_recursive(&"n".into()), None);

        if let Value::Object(ref object) = object {
            assert_eq!(object.attributes().table().len(), 3);
            assert_eq!(
                object.attributes().get(&Key::Key("foo".into())),
                Some(&Attribute::Value(Value::Number(1.0).into()))
            );
        } else {
            panic!("Expected object");
        }
    }

    #[test]
    fn test_assignment() {
        let context = Context::default();
        let pair = SparkMLParser::parse(Rule::assignment, "foo = true")
            .unwrap()
            .next()
            .unwrap();
        let assignment = parse_assignment(pair.clone()).unwrap();
        assert_eq!(
            assignment.eval(&pair, context.clone()).unwrap(),
            Value::Boolean(true)
        );

        assert_eq!(
            context.var_non_recursive(&"foo".into()).unwrap(),
            Value::Boolean(true)
        );

        // using reserved keyword is not allowed
        let pair = SparkMLParser::parse(Rule::assignment, "true = false")
            .unwrap()
            .next()
            .unwrap();
        assert!(parse_assignment(pair).is_err());
    }

    #[test]
    fn test_call() {
        let context = Context::default();
        let pair = SparkMLParser::parse(Rule::call, "foo")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(parse_expression(pair).unwrap(), Ast::Variable("foo".into()));

        let pair = SparkMLParser::parse(Rule::call, "foo(true, false)")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair).unwrap(),
            Ast::FunctionCall(
                "foo".into(),
                vec![
                    Ast::Value(Value::Boolean(true)),
                    Ast::Value(Value::Boolean(false))
                ]
            )
        );

        let pair = SparkMLParser::parse(Rule::assignment, "foo = [[4,3],[2,1]]")
            .unwrap()
            .next()
            .unwrap();

        assert!(parse_expression(pair.clone())
            .unwrap()
            .eval(&pair, context.clone())
            .is_ok());

        let pair = SparkMLParser::parse(Rule::call, "foo[0][1]")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, context.clone())
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
                .eval(&pair, context.clone())
                .unwrap(),
            Value::Number(1.0)
        );

        let pair = SparkMLParser::parse(Rule::call, "foo.bar[0].baz()")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone()).unwrap(),
            Ast::PropertyCall(vec![
                Ast::Variable("foo".into()),
                Ast::ListIndex(
                    Box::new(Ast::Variable("bar".into())),
                    Box::new(Ast::Value(Value::Number(0.0)))
                ),
                Ast::FunctionCall("baz".into(), vec![])
            ])
        );
    }

    #[test]
    fn test_list() {
        let context = Context::default();
        let pair = SparkMLParser::parse(Rule::expression, "[true,false,false]")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, context)
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
        let context = Context::default();
        let pair = SparkMLParser::parse(Rule::expression, "1")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, context.clone())
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
                .eval(&pair, context.clone())
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
                .eval(&pair, context.clone())
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
                .eval(&pair, context.clone())
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
                .eval(&pair, context.clone())
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
                .eval(&pair, context.clone()),
            Ok(Value::Boolean(true))
        ));

        let pair = SparkMLParser::parse(Rule::expression, "false")
            .unwrap()
            .next()
            .unwrap();
        assert!(matches!(
            parse_expression(pair.clone()).unwrap().eval(&pair, context),
            Ok(Value::Boolean(false))
        ));
    }
}
