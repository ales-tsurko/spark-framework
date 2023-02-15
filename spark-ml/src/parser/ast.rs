//! Abstract syntax tree.
use std::borrow::BorrowMut;
use std::cell::RefCell;
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
            let mut inner = pair.clone().into_inner();
            let id: Id = inner.next().unwrap().as_str().into();
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
                    obj.call_property(pair, property, context)
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
                let list = Rc::new(RefCell::new(
                    list.iter()
                        .map(|expr| expr.eval(pair, context.clone()))
                        .collect::<ParseResult<Vec<Value>>>()?,
                ));
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
                lookup_ctx.add_var(pair, id.clone(), value.clone())?;
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
        let list = match lookup_ctx.var(&self.target).ok_or_else(|| {
            custom_error(pair, &format!("Value '{}' not found", self.target.as_str()))
        })? {
            Value::List(list) => list,
            _ => {
                return Err(custom_error(
                    pair,
                    &format!("'{}' is not a list", self.target.as_str()),
                ))
            }
        };

        let indices = self.eval_indices(pair, caller_ctx)?;
        let (last, rest) = indices.split_last().unwrap();
        let mut target = list.clone();

        for index in rest {
            if index >= &target.borrow().len() {
                return Err(custom_error(
                    pair,
                    &format!("Index '{}' out of range", index),
                ));
            }

            let new_target = match target.borrow().get(*index) {
                Some(Value::List(val)) => val.clone(),
                Some(_) => return Err(custom_error(pair, "Only lists can be indexed")),
                _ => {
                    return Err(custom_error(
                        pair,
                        &format!("Index '{}' is out of range", index),
                    ))
                }
            };

            target = new_target;
        }

        (*target).borrow_mut()[*last] = value.clone();

        lookup_ctx.add_var(pair, self.target.clone(), Value::List(list))?;

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
            Ast::Variable(_) => self.0.eval(pair, parent_ctx),

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
    pub(crate) fn call_property(
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
                    Value::Object(obj) => obj.call_property(pair, prop, caller_ctx),
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
        let list = match self.target.eval(pair, lookup_ctx.clone())? {
            Value::List(list) => list.clone(),
            _ => return Err(custom_error(pair, "Only lists can be indexed")),
        };

        if let Value::Number(index) = self.index.eval(pair, caller_ctx)? {
            let index = index as usize;

            if index >= list.borrow().len() {
                return Err(custom_error(
                    pair,
                    &format!("Index '{}' is out of range", index),
                ));
            }

            Ok((*list).borrow()[index].clone())
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

    macro_rules! parse {
        ($code:literal, $rule:ident) => {{
            let pair = SparkMLParser::parse(Rule::$rule, $code)
                .unwrap()
                .next()
                .unwrap();

            pair
        }};
    }

    macro_rules! parse_err {
        ($code:literal, $rule:ident, $parse_func:ident) => {{
            let pair = parse!($code, $rule);
            assert!($parse_func(pair.clone()).is_err());
        }};
    }

    macro_rules! parse_eq {
        ($code:literal, $rule:ident, $parse_func:ident, $expected:expr) => {{
            let pair = parse!($code, $rule);
            assert_eq!($parse_func(pair.clone()).unwrap(), $expected);
        }};
    }

    macro_rules! eval_ok {
        ($code:literal, $rule:ident, $parse_func:ident, $context:expr) => {{
            let pair = parse!($code, $rule);
            assert!($parse_func(pair.clone())
                .unwrap()
                .eval(&pair, $context)
                .is_ok());
        }};
    }

    macro_rules! eval_err {
        ($code:literal, $rule:ident, $parse_func:ident, $context:expr) => {{
            let pair = parse!($code, $rule);
            assert!($parse_func(pair.clone())
                .unwrap()
                .eval(&pair, $context)
                .is_err());
        }};
    }

    macro_rules! eval_eq {
        ($code:literal, $rule:ident, $parse_func:ident, $context:expr, $expected:expr) => {{
            let pair = parse!($code, $rule);
            assert_eq!(
                $parse_func(pair.clone())
                    .unwrap()
                    .eval(&pair, $context)
                    .unwrap(),
                $expected
            );
        }};
    }

    #[test]
    fn test_function() {
        let pair = parse!(
            r#"fn foo(a, b)
                    n = 10
                    20"#,
            func_def
        );

        if let Ast::FunctionDef(function) = parse_func_def(pair).unwrap() {
            assert_eq!(function.name, "foo".into());
            assert_eq!(function.args, vec!["a".into(), "b".into()]);
            assert_eq!(function.body.expressions.len(), 2);
        } else {
            panic!("Expected function definition");
        }

        parse_eq!(
            "foo(true, false)",
            call,
            parse_expression,
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
        let pair = parse!(
            r#"{ 
                 foo: test()
                 bar:
                    @child: 0.1
                 baz: 1

                 n = 1
                 fn test()
                     ^n }"#,
            expression
        );

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

        eval_eq!(
            "foo = true",
            assignment,
            parse_assignment,
            context.clone(),
            Value::Boolean(true)
        );

        // using another type for already assigned variable is not allowed
        eval_err!("foo = 1", assignment, parse_assignment, context.clone());

        // using reserved keyword is not allowed
        parse_err!("true = false", assignment, parse_assignment);

        eval_ok!(
            r#"test = {
                foo = 1
                bar = {
                    baz = 1
                    list = [{
                        foo = [[1, 2], [3, 4]]
                    }]
                }

                fn set_foo(n)
                    ^foo = n
                    n

                fn set_baz(n)
                    ^bar.baz = n
                    n
                }
            "#,
            assignment,
            parse_assignment,
            context.clone()
        );

        eval_eq!(
            "test.foo",
            call,
            parse_expression,
            context.clone(),
            Value::Number(1.0)
        );

        eval_ok!(
            "test.foo = 2",
            assignment,
            parse_assignment,
            context.clone()
        );

        eval_eq!(
            "test.foo",
            call,
            parse_expression,
            context.clone(),
            Value::Number(2.0)
        );

        eval_ok!("test.set_foo(3)", call, parse_expression, context.clone());

        eval_eq!(
            "test.foo",
            call,
            parse_expression,
            context.clone(),
            Value::Number(3.0)
        );

        eval_eq!(
            "test.bar.baz",
            call,
            parse_expression,
            context.clone(),
            Value::Number(1.0)
        );

        eval_ok!("test.set_baz(4)", call, parse_expression, context.clone());

        eval_eq!(
            "test.bar.baz",
            call,
            parse_expression,
            context.clone(),
            Value::Number(4.0)
        );

        eval_eq!(
            "test.bar.list[0].foo[0][1]",
            call,
            parse_expression,
            context.clone(),
            Value::Number(2.0)
        );

        eval_ok!(
            "test.bar.list[0].foo[0][1] = 5",
            assignment,
            parse_assignment,
            context.clone()
        );

        eval_eq!(
            "test.bar.list[0].foo[0][1]",
            call,
            parse_expression,
            context.clone(),
            Value::Number(5.0)
        );
    }

    #[test]
    fn test_variable_call() {
        parse_eq!("foo", call, parse_expression, Ast::Variable("foo".into()));
    }

    #[test]
    fn test_list_index() {
        let context = Context::default();

        eval_ok!(
            "foo = [[4,3],[2,1]]",
            assignment,
            parse_expression,
            context.clone()
        );

        eval_eq!(
            "foo[0][1]",
            call,
            parse_expression,
            context.clone(),
            Value::Number(3.0)
        );

        eval_eq!(
            "foo[1][1]",
            call,
            parse_expression,
            context.clone(),
            Value::Number(1.0)
        );
    }

    #[test]
    fn test_property_call() {
        // property call parsing
        parse_eq!(
            "foo.bar[0].baz()",
            call,
            parse_expression,
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
        eval_ok!(
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
            assignment,
            parse_expression,
            context.clone()
        );

        // the property call shouldn't be recursive (i.e the value should be undefined in this case)
        eval_err!("test.n.bar", call, parse_expression, context.clone());
        eval_err!("test.n.foo()", call, parse_expression, context.clone());

        // the property call should read its own context
        eval_eq!(
            "test.n.foo",
            call,
            parse_expression,
            context.clone(),
            Value::Number(2.0)
        );

        eval_eq!(
            "test.foo",
            call,
            parse_expression,
            context.clone(),
            Value::Number(3.0)
        );

        eval_eq!(
            "test.foo()",
            call,
            parse_expression,
            context.clone(),
            Value::Number(5.0)
        );

        // functions can read parent context
        eval_eq!(
            "test.n.bar()",
            call,
            parse_expression,
            context.clone(),
            Value::Number(5.0)
        );

        // indexing should be evaluated in the context of the caller (`n` should be undefined here)
        eval_err!("test.n.list[n]", call, parse_expression, context.clone());

        // functions can read and modify properties
        eval_eq!(
            "test.baz(6)",
            call,
            parse_expression,
            context.clone(),
            Value::Number(6.0)
        );

        eval_eq!(
            "test.n.n",
            call,
            parse_expression,
            context.clone(),
            Value::Number(6.0)
        );
    }

    #[test]
    fn test_ancestor_ref() {
        parse_eq!(
            "^foo",
            call,
            parse_expression,
            Ast::AncestorRef(AncestorRef(Box::new(Ast::Variable("foo".into()))))
        );

        let context = Context::default();

        eval_ok!(
            "foo = [2, 1]",
            assignment,
            parse_expression,
            context.clone()
        );

        eval_ok!(
            r#"fn test_ancestor_ref(n)
                    ^foo[n]"#,
            func_def,
            parse_func_def,
            context.clone()
        );

        eval_eq!(
            "test_ancestor_ref(1)",
            call,
            parse_expression,
            context.clone(),
            Value::Number(1.0)
        );

        let context = Context::default();

        eval_ok!("baz = 1", assignment, parse_expression, context.clone());

        eval_ok!(
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
            assignment,
            parse_expression,
            context.clone()
        );

        eval_eq!(
            "test.obj.one()",
            call,
            parse_expression,
            context.clone(),
            Value::Number(3.0)
        );

        eval_eq!(
            "test.obj.two()",
            call,
            parse_expression,
            context.clone(),
            Value::Number(2.0)
        );

        eval_eq!(
            "test.obj.three()",
            call,
            parse_expression,
            context.clone(),
            Value::Number(1.0)
        );

        eval_eq!(
            "test.obj.four(4)",
            call,
            parse_expression,
            context.clone(),
            Value::Number(4.0)
        );

        eval_eq!(
            "test.obj.five()",
            call,
            parse_expression,
            context.clone(),
            Value::Number(3.0)
        );

        eval_err!("test.obj.six()", call, parse_expression, context.clone());
    }

    #[test]
    fn test_list() {
        eval_eq!(
            "[true,false,false]",
            expression,
            parse_expression,
            Context::default(),
            Value::List(Rc::new(RefCell::new(vec![
                Value::Boolean(true),
                Value::Boolean(false),
                Value::Boolean(false)
            ])))
        );
    }

    #[test]
    fn test_value() {
        let context = Context::default();

        eval_eq!(
            "1",
            expression,
            parse_expression,
            context.clone(),
            Value::Number(1.0)
        );

        eval_eq!(
            "1.0",
            expression,
            parse_expression,
            context.clone(),
            Value::Number(1.0)
        );

        eval_eq!(
            "1E-2",
            expression,
            parse_expression,
            context.clone(),
            Value::Number(0.01)
        );

        eval_eq!(
            r#""This is a string\nhello""#,
            expression,
            parse_expression,
            context.clone(),
            Value::String("This is a string\\nhello".to_string())
        );

        eval_eq!(
            r#"`NodePath("Path:")`"#,
            expression,
            parse_expression,
            context.clone(),
            Value::GdValue("NodePath(\"Path:\")".to_string())
        );

        eval_eq!(
            "true",
            expression,
            parse_expression,
            context.clone(),
            Value::Boolean(true)
        );

        eval_eq!(
            "false",
            expression,
            parse_expression,
            context.clone(),
            Value::Boolean(false)
        );
    }
}
