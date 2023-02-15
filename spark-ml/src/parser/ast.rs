//! Abstract syntax tree.
use std::collections::HashMap;
use std::rc::Rc;

use pest::iterators::Pair;

use crate::parser::context::Context;
use crate::parser::value::{self, Attribute, Attributes, Id, Key, Object, Value};
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
        Rule::call => parse_call(pair.into_inner().next().unwrap()),
        Rule::list => {
            let list = Rc::new(
                pair.into_inner()
                    .map(|item| parse_expression(item))
                    .collect::<ParseResult<Vec<Ast>>>()?,
            );
            Ok(Ast::List(list))
        }
        Rule::NUMBER => Ok(Ast::Value(Value::Number(pair.as_str().parse().unwrap()))),
        Rule::BOOL => Ok(Ast::Value(Value::Boolean(pair.as_str().parse().unwrap()))),
        Rule::STRING => Ok(Ast::Value(Value::String(
            pair.into_inner().next().unwrap().as_str().into(),
        ))),
        Rule::GD_VALUE => Ok(Ast::Value(Value::GdValue(
            pair.into_inner().next().unwrap().as_str().into(),
        ))),
        _ => unreachable!(),
    }
}

fn parse_object(pair: Pair<Rule>) -> ParseResult<Ast> {
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

    let mut pairs = pair.clone().into_inner();
    let target = pairs.next().unwrap();
    let expression = pairs.next().unwrap();
    let expression = parse_expression(expression)?;
    let target = parse_assignment_target(target)?;

    Ok(Ast::Assignment(Assignment::new(target, expression)))
}

fn parse_assignment_target(pair: Pair<Rule>) -> ParseResult<AssignmentTarget> {
    match pair.as_rule() {
        Rule::ID => {
            // in contrast to other assignment targets, IDs can be undefined (we reference others
            // instead)
            let id: Id = pair.as_str().into();
            if RESERVED_WORDS.contains(id.as_str()) {
                return Err(custom_error(
                    &pair,
                    &format!("'{}' is a reserved keyword", id.as_str()),
                ));
            }
            Ok(AssignmentTarget::Id(id))
        }

        Rule::assign_property => {
            let mut inner = pair.into_inner();
            let target = inner.next().unwrap();
            let property = inner.next().unwrap();
            let target = parse_assignment_target(target)?;
            let property = parse_assignment_target(property)?;
            Ok(AssignmentTarget::Property(AssignProperty::new(
                target, property,
            )))
        }

        Rule::assign_list_index => {
            let inner = pair.clone().into_inner();
            let id: Id = pair.as_str().into();
            let indices = inner
                .map(parse_expression)
                .collect::<ParseResult<Vec<Ast>>>()?;
            Ok(AssignmentTarget::ListIndex(AssignListIndex::new(
                id, indices,
            )))
        }

        Rule::assign_ancestor => {
            let assign_ancestor =
                AssignAncestor::new(parse_assignment_target(pair.into_inner().next().unwrap())?);
            Ok(AssignmentTarget::Ancestor(assign_ancestor))
        }

        _ => unreachable!(),
    }
}

fn parse_call(pair: Pair<Rule>) -> ParseResult<Ast> {
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

        Rule::ancestor_ref => Ok(Ast::AncestorRef(AncestorRef(Box::new(parse_call(
            pair.into_inner().next().unwrap(),
        )?)))),

        _ => unreachable!(),
    }
}

fn parse_expr_body(pair: Pair<Rule>) -> ParseResult<Body> {
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

    Ok(Ast::FunctionDef(Function::new(id, args, body)))
}

fn parse_func_args(pair: Pair<Rule>) -> ParseResult<Vec<Id>> {
    pair.into_inner().map(|id| Ok(id.as_str().into())).collect()
}

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum Ast {
    Assignment(Assignment),
    Object(Object<Self>),
    Value(Value),
    FunctionCall(Id, Vec<Self>),
    FunctionDef(Function),
    Variable(Id),
    AncestorRef(AncestorRef),
    If,
    Repeat,
    Algebraic,
    Boolean,
    List(Rc<Vec<Self>>),
    ListIndex(ListIndex),
    PropertyCall(Box<Self>, Box<Self>),
}

impl Ast {
    pub(crate) fn eval(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Value> {
        match self {
            Ast::Value(val) => Ok(val.clone()),

            Ast::Assignment(assignment) => assignment.eval(pair, context),

            Ast::FunctionDef(func) => {
                let func = func.eval(context.clone());
                context.add_func(pair, func.clone())?;
                Ok(Value::Function(func))
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
                    func.eval(pair, args, context.clone())
                } else {
                    Err(custom_error(
                        pair,
                        &format!("Function '{}' not found", id.as_str()),
                    ))
                }
            }

            Ast::List(list) => {
                let list = Rc::new(
                    list.iter()
                        .map(|expr| expr.eval(pair, context.clone()))
                        .collect::<ParseResult<Vec<Value>>>()?,
                );
                Ok(Value::List(list))
            }

            Ast::Variable(id) => context
                .var(id)
                .ok_or_else(|| custom_error(pair, &format!("'{}' not found", id.as_str()))),

            Ast::AncestorRef(call) => call.eval(pair, context),

            Ast::ListIndex(list_index) => list_index.eval(pair, context.clone(), context),

            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Assignment {
    target: AssignmentTarget,
    expression: Box<Ast>,
}

impl Assignment {
    pub(crate) fn new(target: AssignmentTarget, expression: Ast) -> Self {
        Self {
            target,
            expression: Box::new(expression),
        }
    }

    pub(crate) fn eval(&self, pair: &Pair<Rule>, caller_ctx: Context) -> ParseResult<Value> {
        let value = self.expression.eval(pair, caller_ctx.clone())?;
        self.target
            .assign(value, pair, caller_ctx.clone(), caller_ctx)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum AssignmentTarget {
    Id(Id),
    Ancestor(AssignAncestor),
    Property(AssignProperty),
    ListIndex(AssignListIndex),
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct AssignAncestor {
    target: Box<AssignmentTarget>,
}

impl AssignmentTarget {
    pub(crate) fn assign(
        &self,
        value: Value,
        pair: &Pair<Rule>,
        lookup_ctx: Context,
        caller_ctx: Context,
    ) -> ParseResult<Value> {
        match &self {
            Self::Id(id) => {
                caller_ctx.add_var(pair, id.clone(), value.clone())?;
                Ok(value)
            }

            Self::Ancestor(ancestor) => ancestor.assign(value, pair, lookup_ctx, caller_ctx),

            Self::Property(prop_assignment) => {
                prop_assignment.assign(value, pair, lookup_ctx, caller_ctx)
            }

            Self::ListIndex(list_index) => list_index.assign(pair, value, lookup_ctx, caller_ctx),
        }
    }
}

impl AssignAncestor {
    fn new(target: AssignmentTarget) -> Self {
        Self {
            target: Box::new(target),
        }
    }

    fn assign(
        &self,
        value: Value,
        pair: &Pair<Rule>,
        lookup_ctx: Context,
        caller_ctx: Context,
    ) -> ParseResult<Value> {
        match &*self.target {
            AssignmentTarget::Id(id) => lookup_ctx
                .find_var_ancestor(id)
                .ok_or_else(|| custom_error(pair, &format!("'{}' not found", id.as_str())))
                .map(|ctx| {
                    ctx.add_var(pair, id.clone(), value.clone())?;
                    Ok(value)
                })?,

            AssignmentTarget::ListIndex(list_index) => lookup_ctx
                .find_var_ancestor(&list_index.target)
                .ok_or_else(|| {
                    custom_error(pair, &format!("'{}' not found", list_index.target.as_str()))
                })
                .map(|ctx| list_index.assign(pair, value, ctx, caller_ctx))?,

            _ => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct AssignProperty {
    target: Box<AssignmentTarget>,
    property: Box<AssignmentTarget>,
}

impl AssignProperty {
    pub(crate) fn new(target: AssignmentTarget, property: AssignmentTarget) -> Self {
        Self {
            target: Box::new(target),
            property: Box::new(property),
        }
    }

    pub(crate) fn assign(
        &self,
        value: Value,
        pair: &Pair<Rule>,
        lookup_ctx: Context,
        caller_ctx: Context,
    ) -> ParseResult<Value> {
        if let Value::Object(obj) = match &*self.target {
            AssignmentTarget::Ancestor(ancestor) => {
                AncestorRef::from(ancestor).eval(pair, lookup_ctx)?
            }

            AssignmentTarget::ListIndex(list_index) => {
                ListIndex::from(list_index).eval(pair, lookup_ctx, caller_ctx.clone())?
            }
            AssignmentTarget::Id(id) => Ast::Variable(id.clone()).eval(pair, lookup_ctx)?,
            _ => unreachable!(),
        } {
            self.property
                .assign(value, pair, obj.context().clone(), caller_ctx)
        } else {
            Err(custom_error(
                pair,
                "Property assignment can be applied only to objects",
            ))
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct AssignListIndex {
    target: Id,
    indices: Vec<Ast>,
}

impl AssignListIndex {
    pub(crate) fn new(target: Id, indices: Vec<Ast>) -> Self {
        Self { target, indices }
    }

    pub(crate) fn assign(
        &self,
        pair: &Pair<Rule>,
        value: Value,
        lookup_ctx: Context,
        caller_ctx: Context,
    ) -> ParseResult<Value> {
        let list = lookup_ctx.var(&self.target).ok_or_else(|| {
            custom_error(pair, &format!("Value '{}' not found", self.target.as_str()))
        })?;

        let mut list = match list {
            Value::List(list) => (*list).clone(),
            _ => {
                return Err(custom_error(
                    pair,
                    &format!("'{}' is not a list", self.target.as_str()),
                ))
            }
        };

        let indices = self.eval_indices(pair, caller_ctx)?;
        let (last, rest) = indices.split_last().unwrap();
        let mut target_ref = &mut list;

        for index in rest {
            if index >= &target_ref.len() {
                return Err(custom_error(
                    pair,
                    &format!("Index '{}' out of range", index),
                ));
            }

            match target_ref.get_mut(*index) {
                Some(Value::List(val)) => {
                    target_ref = Rc::get_mut(val).unwrap();
                }
                Some(_) => return Err(custom_error(pair, "Only lists can be indexed")),
                _ => {
                    return Err(custom_error(
                        pair,
                        &format!("Index '{}' is out of range", index),
                    ))
                }
            }
        }

        target_ref[*last] = value.clone();

        let result = Value::List(Rc::new(list));

        lookup_ctx.add_var(pair, self.target.clone(), result)?;

        Ok(value)
    }

    fn eval_indices(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Vec<usize>> {
        self.indices
            .iter()
            .map(|index| match index.eval(pair, context.clone())? {
                Value::Number(index) => Ok(index as usize),
                _ => Err(custom_error(pair, "Index is not a number")),
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct AncestorRef(Box<Ast>);

impl AncestorRef {
    fn eval(&self, pair: &Pair<Rule>, caller_ctx: Context) -> ParseResult<Value> {
        let parent_ctx = caller_ctx
            .clone()
            .parent()
            .clone()
            .ok_or_else(|| custom_error(pair, "The caller has no parent context"))?;

        parent_ctx.vars().set_all_recursive(true);

        match &*self.0 {
            Ast::Variable(_) => self.eval(pair, parent_ctx),

            Ast::ListIndex(list_index) => list_index.eval(pair, parent_ctx, caller_ctx),

            _ => unreachable!(),
        }
    }
}

impl From<&AssignAncestor> for AncestorRef {
    fn from(ancestor: &AssignAncestor) -> Self {
        match &*ancestor.target {
            AssignmentTarget::Id(id) => Self(Box::new(Ast::Variable(id.clone()))),

            AssignmentTarget::ListIndex(list_index) => {
                Self(Box::new(Ast::ListIndex(list_index.into())))
            }

            _ => unreachable!(),
        }
    }
}

impl Object<Ast> {
    pub(crate) fn eval(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Object<Value>> {
        let context = Context::with_parent(context);

        context.vars().set_recursive(false);
        context.funcs().set_recursive(false);

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
                self.context().funcs().set_recursive(false);

                if let Some(func) = self.context().func(&id) {
                    func.eval(pair, args, self.context().clone())
                } else {
                    Err(custom_error(
                        pair,
                        &format!("Object has no '{}' function", id.as_str()),
                    ))
                }
            }

            Ast::ListIndex(list_index) => {
                self.context().vars().set_recursive(false);
                list_index.eval(pair, self.context().clone(), caller_ctx)
            }

            Ast::PropertyCall(target, prop) => {
                self.context().vars().set_recursive(false);
                self.context().funcs().set_recursive(false);

                match target.eval(pair, self.context().clone())? {
                    Value::Object(obj) => obj.call_poperty(pair, prop, caller_ctx),
                    _ => Err(custom_error(
                        pair,
                        "Property call can be applied only to objects",
                    )),
                }
            }

            Ast::Variable(_) => {
                self.context().vars().set_recursive(false);
                property.eval(pair, self.context().clone())
            }

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
pub(crate) struct Function {
    pub(crate) name: Id,
    args: Vec<Id>,
    body: Body,
}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.args == other.args && self.body == other.body
    }
}

impl Function {
    pub(crate) fn new(name: Id, args: Vec<Id>, body: Body) -> Self {
        Self { name, args, body }
    }

    pub(crate) fn eval(&self, context: Context) -> value::Function {
        value::Function::new(
            self.name.clone(),
            self.args.clone(),
            self.body.clone(),
            context,
        )
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

    pub(crate) fn eval(
        &self,
        pair: &Pair<Rule>,
        lookup_ctx: Context,
        caller_ctx: Context,
    ) -> ParseResult<Value> {
        let mut list = match self.target.eval(pair, lookup_ctx.clone())? {
            Value::List(list) => (*list).clone(),
            _ => return Err(custom_error(pair, "Only lists can be indexed")),
        };

        if let Value::Number(index) = self.index.eval(pair, caller_ctx)? {
            let index = index as usize;

            if index >= list.len() {
                return Err(custom_error(
                    pair,
                    &format!("Index '{}' is out of range", index),
                ));
            }

            Ok(list.swap_remove(index))
        } else {
            Err(custom_error(pair, "Index should be a number"))
        }
    }
}

impl From<&AssignListIndex> for ListIndex {
    fn from(assign: &AssignListIndex) -> Self {
        let target = Ast::Variable(assign.target.clone().into());
        match assign.indices.iter().fold(target, |acc, index| {
            Ast::ListIndex(ListIndex::new(acc, index.clone()))
        }) {
            Ast::ListIndex(index) => index,
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use pest::Parser;

    use crate::parser::SparkMLParser;

    use super::*;

    #[test]
    fn test_function() {
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
                     ^n }"#,
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
                [Ast::Assignment(assignment), Ast::FunctionDef(func)] => {
                    assert_eq!(assignment.target, AssignmentTarget::Id("n".into()));
                    assert!(matches!(
                        assignment.expression.as_ref(),
                        &Ast::Value(Value::Number(_))
                    ));
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
    fn test_variable_call() {
        let pair = SparkMLParser::parse(Rule::call, "foo")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(parse_expression(pair).unwrap(), Ast::Variable("foo".into()));
    }

    #[test]
    fn test_list_index() {
        let context = Context::default();
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
    }

    #[test]
    fn test_property_call() {
        // property call parsing
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
                   ^n.n = n
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
    fn test_ancestor_ref() {
        let context = Context::default();
        let pair = SparkMLParser::parse(Rule::call, "^foo")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair).unwrap(),
            Ast::AncestorRef(AncestorRef(Box::new(Ast::Variable("foo".into()))))
        );

        let pair = SparkMLParser::parse(Rule::assignment, "foo = [2, 1]")
            .unwrap()
            .next()
            .unwrap();
        assert!(parse_expression(pair.clone())
            .unwrap()
            .eval(&pair, context.clone())
            .is_ok());

        let pair = SparkMLParser::parse(
            Rule::func_def,
            r#"fn test_ancestor_ref(n)
                    ^foo[n]"#,
        )
        .unwrap()
        .next()
        .unwrap();
        assert!(parse_func_def(pair.clone())
            .unwrap()
            .eval(&pair, context.clone())
            .is_ok());

        let pair = SparkMLParser::parse(Rule::call, "test_ancestor_ref(1)")
            .unwrap()
            .next()
            .unwrap();
        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, context)
                .unwrap(),
            Value::Number(1.0)
        );

        let context = Context::default();

        let pair = SparkMLParser::parse(Rule::assignment, "baz = 1")
            .unwrap()
            .next()
            .unwrap();
        assert!(parse_expression(pair.clone())
            .unwrap()
            .eval(&pair, context.clone())
            .is_ok());

        let pair = SparkMLParser::parse(
            Rule::assignment,
            r#"test = {
                bar = 2

                obj = {
                    foo = 3

                    fn one()
                        ^foo

                    fn two()
                        ^bar

                    fn three()
                        ^baz

                    fn four(foo)
                        foo

                    fn five()
                        ^obj.foo

                    fn six()
                        foo # should be undefined
                }
            }"#,
        )
        .unwrap()
        .next()
        .unwrap();

        assert!(parse_expression(pair.clone())
            .unwrap()
            .eval(&pair, context.clone())
            .is_ok());

        let pair = SparkMLParser::parse(Rule::call, "test.obj.one()")
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

        let pair = SparkMLParser::parse(Rule::call, "test.obj.two()")
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

        let pair = SparkMLParser::parse(Rule::call, "test.obj.three()")
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

        let pair = SparkMLParser::parse(Rule::call, "test.obj.four(4)")
            .unwrap()
            .next()
            .unwrap();

        assert_eq!(
            parse_expression(pair.clone())
                .unwrap()
                .eval(&pair, context.clone())
                .unwrap(),
            Value::Number(4.0)
        );

        let pair = SparkMLParser::parse(Rule::call, "test.obj.five()")
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

        let pair = SparkMLParser::parse(Rule::call, "test.obj.six()")
            .unwrap()
            .next()
            .unwrap();

        assert!(parse_expression(pair.clone())
            .unwrap()
            .eval(&pair, context)
            .is_err());
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
            Value::List(Rc::new(vec![
                Value::Boolean(true),
                Value::Boolean(false),
                Value::Boolean(false)
            ]))
        );
    }

    #[test]
    fn test_value() {
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
