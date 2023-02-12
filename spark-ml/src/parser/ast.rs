//! Abstract syntax tree.
use std::collections::HashMap;
use std::rc::Rc;

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
                .collect::<ParseResult<Vec<Ast>>>()?,
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

    Ok(Ast::Object(Object::new(
        Rc::new(attributes?),
        body,
        Context::default(),
    )))
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
            let mut inner = pair.into_inner();
            let target = inner.next().unwrap();
            let property = inner.next().unwrap();

            Ok(Ast::PropertyCall(
                Box::new(parse_call(target)?),
                Box::new(parse_call(property)?),
            ))
        }

        Rule::list_index => {
            let mut inner = pair.into_inner();
            // NOTE: it can be call only, but not wrapped into Rule::call
            let expression = parse_call(inner.next().unwrap())?;
            let indices = inner
                .map(parse_expression)
                .collect::<ParseResult<Vec<Ast>>>()?;

            Ok(indices.into_iter().fold(expression, |acc, index| {
                Ast::ListIndex(ListIndex::new(acc, index))
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
    List(Vec<Ast>),
    ListIndex(ListIndex),
    PropertyCall(Box<Ast>, Box<Ast>),
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
                let mut func = func.clone();
                func.capture_parent_context(&context);
                context.add_func(pair, func)?;
                Ok(Value::Boolean(true))
            }

            Ast::Object(object) => Ok(Value::Object(object.eval(pair, context)?)),

            Ast::PropertyCall(target, property) => {
                if let Value::Object(obj) = target.eval(pair, context.clone())? {
                    obj.call_poperty(pair, property, context)
                } else {
                    Err(custom_error(
                        pair,
                        "Property call can be applied only to objects",
                    ))
                }
            }

            Ast::FunctionCall(id, args) => {
                if let Some(func) = context.func(&id) {
                    func.call(pair, args, context.clone())
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
                    .collect::<ParseResult<Vec<Value>>>()?,
            )),

            Ast::Variable(id) => context
                .var(id)
                .ok_or_else(|| custom_error(pair, &format!("'{}' not found", id.as_str()))),

            Ast::ListIndex(list_index) => {
                let list = list_index.eval_target(pair, context.clone())?;
                list_index.eval_index(list, pair, context)
            }
            _ => todo!(),
        }
    }
}

impl Object<Ast> {
    pub(crate) fn eval(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Object<Value>> {
        let context = Context::from_parent(
            Context::default()
                .with_vars(context.vars().capture())
                .with_funcs(context.funcs().clone()),
        );
        let _ = self.body().eval(pair, context.clone())?;
        let attributes = Rc::new(self.attributes().eval(pair, context.clone())?);
        Ok(Object::new(attributes, self.body().clone(), context))
    }
}

impl Object<Value> {
    pub(crate) fn call_poperty(
        &self,
        pair: &Pair<Rule>,
        property: &Ast,
        caller_ctx: Context,
    ) -> ParseResult<Value> {
        match property {
            Ast::FunctionCall(id, args) => {
                if let Some(func) = self.context().shallow_clone().func(&id) {
                    func.call(pair, args, self.context().clone())
                } else {
                    Err(custom_error(
                        pair,
                        &format!("Object has no '{}' function", id.as_str()),
                    ))
                }
            }

            Ast::ListIndex(list_index) => {
                let list = list_index.eval_target(pair, self.context().clone())?;
                list_index.eval_index(list, pair, caller_ctx)
            }

            Ast::PropertyCall(target, prop) => {
                match target.eval(pair, self.context().shallow_clone())? {
                    Value::Object(obj) => obj.call_poperty(pair, prop, caller_ctx),
                    _ => Err(custom_error(
                        pair,
                        "Property call can be applied only to objects",
                    )),
                }
            }

            Ast::Variable(_) => property.eval(pair, self.context().shallow_clone()),

            _ => unreachable!(),
        }
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

#[derive(Debug, Clone)]
pub(crate) struct FunctionDef {
    pub(crate) name: Id,
    args: Rc<Vec<Id>>,
    body: Body,
    context: Option<Context>,
}

impl PartialEq for FunctionDef {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.args == other.args && self.body == other.body
    }
}

impl FunctionDef {
    pub(crate) fn new(name: Id, args: Vec<Id>, body: Body) -> Self {
        Self {
            name,
            args: Rc::new(args),
            body,
            context: None,
        }
    }

    pub(crate) fn capture_parent_context(&mut self, context: &Context) {
        self.context = Some(Context::from_parent(
            Context::default()
                .with_vars(context.vars().capture())
                .with_funcs(context.funcs().clone()),
        ));
    }

    pub(crate) fn call(
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

        let caller_ctx = context.clone();

        let context = self.context.clone().ok_or(custom_error(
            pair,
            &format!(
                "Internal: context of function '{}' not found",
                self.name.as_str()
            ),
        ))?;

        for (n, arg) in args.iter().enumerate() {
            // args should be evaluated in the caller's context
            let value = arg.eval(pair, caller_ctx.clone())?;
            // and added to the function's context
            context.add_var(pair, self.args[n].clone(), value)?;
        }

        self.body.eval(pair, context)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Body {
    expressions: Rc<Vec<Ast>>,
}

impl Body {
    pub(crate) fn new(expressions: Vec<Ast>) -> Self {
        Self {
            expressions: Rc::new(expressions),
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

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ListIndex {
    pub(crate) target: Box<Ast>,
    pub(crate) index: Box<Ast>,
}

impl ListIndex {
    pub(crate) fn new(target: Ast, index: Ast) -> Self {
        Self {
            target: target.into(),
            index: index.into(),
        }
    }

    pub(crate) fn eval_target(
        &self,
        pair: &Pair<Rule>,
        context: Context,
    ) -> ParseResult<Vec<Value>> {
        match self.target.eval(pair, context.clone())? {
            Value::List(list) => Ok(list),
            _ => Err(custom_error(pair, "Only lists can be indexed")),
        }
    }

    pub(crate) fn eval_index(
        &self,
        mut value: Vec<Value>,
        pair: &Pair<Rule>,
        context: Context,
    ) -> ParseResult<Value> {
        if let Value::Number(index) = self.index.eval(pair, context)? {
            let index = index as usize;

            if index >= value.len() {
                return Err(custom_error(
                    pair,
                    &format!("Index '{}' is out of bounds", index),
                ));
            }

            Ok(value.swap_remove(index))
        } else {
            Err(custom_error(pair, "Index should be a number"))
        }
    }
}

#[cfg(test)]
mod tests {
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
            assert_eq!(function.args.as_ref(), &["a".into(), "b".into()]);
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
                    assert!(func.args.is_empty());
                }
                _ => panic!("Expected assignment"),
            }
        } else {
            panic!("Expected object");
        }

        // test evaluation
        let context = Context::default();
        let object = expr.eval(&pair, context.clone()).unwrap();

        if let Value::Object(ref object) = object {
            assert_eq!(object.context().var(&"n".into()), Some(Value::Number(1.0)));
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

        assert_eq!(context.var(&"foo".into()).unwrap(), Value::Boolean(true));

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
            Ast::PropertyCall(
                Box::new(Ast::Variable("foo".into())),
                Box::new(Ast::PropertyCall(
                    Box::new(Ast::ListIndex(ListIndex::new(
                        Ast::Variable("bar".into()),
                        Ast::Value(Value::Number(0.0))
                    ))),
                    Box::new(Ast::FunctionCall("baz".into(), vec![]))
                ))
            )
        );

        // property call evaluation
        let context = Context::default();

        // first, we prepare an object
        let pair = SparkMLParser::parse(
            Rule::assignment,
            r#"test = {
                   n = {
                       n = 1
                       foo = 2
                       list = [[1,2],[n,4]]

                       fn bar()
                           foo()
                   }
                   foo = 3
                   bar = 4 # shouldn't be accessible from child object (n)

                   fn foo()
                       5

                   fn baz(n)
                       .n.n = n
                        n
               }"#,
        )
        .unwrap()
        .next()
        .unwrap();

        // evaluate the object
        parse_expression(pair.clone())
            .unwrap()
            .eval(&pair, context.clone())
            .unwrap();

        // the property call shouldn't be recursive (i.e the value should be undefined in this case)
        let pair = SparkMLParser::parse(Rule::call, "test.n.bar")
            .unwrap()
            .next()
            .unwrap();

        assert!(parse_expression(pair.clone())
            .unwrap()
            .eval(&pair, context.clone())
            .is_err());

        let pair = SparkMLParser::parse(Rule::call, "test.n.foo()")
            .unwrap()
            .next()
            .unwrap();

        assert!(parse_expression(pair.clone())
            .unwrap()
            .eval(&pair, context.clone())
            .is_err());

        // the property call should read its own context
        let pair = SparkMLParser::parse(Rule::call, "test.n.foo")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, context.clone())
                .unwrap(),
            Value::Number(2.0)
        );

        let pair = SparkMLParser::parse(Rule::call, "test.foo")
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

        let pair = SparkMLParser::parse(Rule::call, "test.foo()")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, context.clone())
                .unwrap(),
            Value::Number(5.0)
        );

        // functions can read parent context
        let pair = SparkMLParser::parse(Rule::call, "test.n.bar()")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, context.clone())
                .unwrap(),
            Value::Number(5.0)
        );

        // indexing should be evaluated in the context of the caller (`n` should be undefined here)
        let pair = SparkMLParser::parse(Rule::call, "test.n.list[n]")
            .unwrap()
            .next()
            .unwrap();

        assert!(parse_expression(pair.clone())
            .unwrap()
            .eval(&pair, context.clone())
            .is_err());

        // functions can read and modify properties
        let pair = SparkMLParser::parse(Rule::call, "test.baz(6)")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, context.clone())
                .unwrap(),
            Value::Number(6.0)
        );

        let pair = SparkMLParser::parse(Rule::call, "test.n.n")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, context.clone())
                .unwrap(),
            Value::Number(6.0)
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
            Value::List(vec![
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
