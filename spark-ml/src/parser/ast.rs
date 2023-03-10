//! Abstract syntax tree.
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

use indexmap::IndexMap;
use once_cell::sync::OnceCell;
use pest::iterators::Pair;
use regex::Regex;

use crate::parser::context::Context;
use crate::parser::value::{
    self, Attribute, Attributes, Easing, Id, Key, Node, Object, Signal, Transition, Tween, Value,
};
use crate::parser::SparkMLParser;
use crate::parser::{custom_error, ParseResult, Rule, RESERVED_WORDS};

pub(crate) fn parse_expression(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Ast> {
    match pair.as_rule() {
        Rule::node => parse_node(pair, parser),
        Rule::object => parse_object(pair, parser),
        Rule::assignment => parse_assignment(pair, parser),
        Rule::if_expr => Ok(Ast::If(parse_if_expr(pair, parser)?)),
        Rule::repeat_expr => parse_repeat_expr(pair, parser),
        Rule::algebraic_expr => parse_algebraic_expr(pair, parser),
        Rule::bool_expr => parse_boolean_expr(pair, parser),
        Rule::call => parse_call(pair.into_inner().next().unwrap(), parser),
        Rule::list => {
            let list = Rc::new(
                pair.into_inner()
                    .map(|item| parse_expression(item, parser))
                    .collect::<ParseResult<Vec<Ast>>>()?,
            );
            Ok(Ast::List(list))
        }
        Rule::NUMBER => Ok(Ast::Value(Value::Number(pair.as_str().parse().unwrap()))),
        Rule::BOOL => Ok(Ast::Value(Value::Boolean(pair.as_str().parse().unwrap()))),
        Rule::STRING => parse_string_expr(pair, parser),
        Rule::GD_VALUE => Ok(Ast::Value(Value::GdValue(
            pair.into_inner().next().unwrap().as_str().into(),
        ))),
        _ => unreachable!(),
    }
}

fn parse_node(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Ast> {
    let mut inner = pair.into_inner();

    let name = parse_node_id(inner.next().unwrap(), parser)?;
    let class = parse_node_id(inner.next().unwrap(), parser)?;
    let attributes = match inner.next() {
        Some(pair) => parse_attributes(pair, parser)?,
        None => Attributes::default(),
    };

    Ok(Ast::Node(Rc::new(Node::new_default(
        name, class, attributes,
    ))))
}

fn parse_node_id(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<NodeIdExpr> {
    match pair.as_rule() {
        Rule::ID => parse_id(pair).map(NodeIdExpr::Id),
        Rule::STRING => {
            parse_string_expr(pair, parser).map(|expr| NodeIdExpr::String(Box::new(expr)))
        }
        _ => unreachable!(),
    }
}

fn parse_id(pair: Pair<Rule>) -> ParseResult<Id> {
    let id: Id = pair.as_str().into();
    if RESERVED_WORDS.contains(id.as_str()) {
        return Err(custom_error(
            &pair,
            &format!("'{}' is a reserved keyword", id.as_str()),
        ));
    }
    Ok(id)
}

fn parse_object(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Ast> {
    assert!(matches!(pair.as_rule(), Rule::object));

    let pairs = pair.into_inner();

    let (attributes, properties) = pairs.fold(
        (Ok(Attributes::default()), Ok(Vec::new())),
        |(mut attributes, mut properties), pair| {
            match pair.as_rule() {
                Rule::attributes => {
                    attributes = parse_attributes(pair, parser);
                }

                Rule::properties => {
                    properties = parse_properties(pair, parser);
                }

                _ => unreachable!(),
            }

            (attributes, properties)
        },
    );

    let body = Body::new(properties?);

    Ok(Ast::Object(Rc::new(Object::new(
        attributes?,
        body,
        Context::default(),
    ))))
}

fn parse_attributes(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Attributes<Ast>> {
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
                Attribute::Attributes(Rc::new(parse_attributes(value_pair, parser)?)),
            ),

            _ => attributes.insert(
                key,
                Attribute::Value(Rc::new(parse_expression(value_pair, parser)?)),
            ),
        }
    }

    Ok(attributes)
}

fn parse_properties(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Vec<Ast>> {
    assert!(matches!(pair.as_rule(), Rule::properties));

    pair.into_inner()
        .map(|property| match property.as_rule() {
            Rule::func_def => parse_func_def(property, parser),
            Rule::assignment => parse_assignment(property, parser),
            _ => unreachable!(),
        })
        .collect()
}

pub(crate) fn parse_assignment(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Ast> {
    assert!(matches!(pair.as_rule(), Rule::assignment));

    let mut pairs = pair.clone().into_inner();
    let target = pairs.next().unwrap();
    let expression = pairs.next().unwrap();
    let expression = parse_expression(expression, parser)?;
    let target = parse_assignment_target(target, parser)?;

    Ok(Ast::Assignment(Assignment::new(target, expression)))
}

fn parse_assignment_target(
    pair: Pair<Rule>,
    parser: &SparkMLParser,
) -> ParseResult<AssignmentTarget> {
    match pair.as_rule() {
        Rule::ID => Ok(AssignmentTarget::Id(parse_id(pair)?)),

        Rule::assign_property => {
            let mut inner = pair.into_inner();
            let target = inner.next().unwrap();
            let property = inner.next().unwrap();
            let target = parse_assignment_target(target, parser)?;
            let property = parse_assignment_target(property, parser)?;
            Ok(AssignmentTarget::Property(AssignProperty::new(
                target, property,
            )))
        }

        Rule::assign_list_index => {
            let mut inner = pair.clone().into_inner();
            let id: Id = inner.next().unwrap().as_str().into();
            let indices = inner
                .map(|expr| parse_expression(expr, parser))
                .collect::<ParseResult<Vec<Ast>>>()?;
            Ok(AssignmentTarget::ListIndex(AssignListIndex::new(
                id, indices,
            )))
        }

        Rule::assign_ancestor => {
            let assign_ancestor = AssignAncestor::new(parse_assignment_target(
                pair.into_inner().next().unwrap(),
                parser,
            )?);
            Ok(AssignmentTarget::Ancestor(assign_ancestor))
        }

        _ => unreachable!(),
    }
}

fn parse_if_expr(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<If> {
    assert!(matches!(pair.as_rule(), Rule::if_expr) || matches!(pair.as_rule(), Rule::elseif));

    let mut pairs = pair.clone().into_inner();
    let condition = parse_expression(pairs.next().unwrap(), parser)?;
    let body = parse_expr_body(pairs.next().unwrap(), parser)?;

    let else_exprs = pairs
        .map(|else_expr| {
            Ok(match else_expr.as_rule() {
                Rule::elseif => Else::ElseIf(parse_if_expr(else_expr, parser)?),
                Rule::ifelse => Else::IfElse(parse_expr_body(
                    else_expr.into_inner().next().unwrap(),
                    parser,
                )?),
                _ => unreachable!(),
            })
        })
        .collect::<ParseResult<Vec<_>>>()?;

    Ok(If::new(condition, body, else_exprs))
}

fn parse_repeat_expr(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Ast> {
    assert!(matches!(pair.as_rule(), Rule::repeat_expr));

    let mut pairs = pair.clone().into_inner();
    let times = parse_expression(pairs.next().unwrap(), parser)?;
    let body = parse_expr_body(pairs.next().unwrap(), parser)?;

    Ok(Ast::Repeat(Repeat::new(times, body)))
}

fn parse_algebraic_expr(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Ast> {
    parser
        .algebraic
        .map_primary(|primary| match primary.as_rule() {
            Rule::call | Rule::NUMBER => parse_expression(primary, parser),
            Rule::algebraic_expr => parse_algebraic_expr(primary, parser),
            _ => Err(custom_error(
                &primary,
                "Unexpected value in algebraic expression",
            )),
        })
        .map_prefix(|_, rhs| Ok(Ast::Algebraic(Algebraic::new_neg(rhs?))))
        .map_infix(|lhs, op, rhs| {
            let op = match op.as_rule() {
                Rule::ADD => MathOperator::Add,
                Rule::SUB => MathOperator::Sub,
                Rule::MUL => MathOperator::Mul,
                Rule::DIV => MathOperator::Div,
                Rule::MOD => MathOperator::Mod,
                _ => unreachable!(),
            };

            Ok(Ast::Algebraic(Algebraic::new_in(lhs?, op, rhs?)))
        })
        .parse(pair.into_inner())
}

fn parse_boolean_expr(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Ast> {
    parser
        .boolean
        .map_primary(|primary| match primary.as_rule() {
            Rule::call | Rule::BOOL => parse_expression(primary, parser),
            Rule::bool_expr => parse_boolean_expr(primary, parser),
            Rule::comparison => parse_comparison(primary, parser),
            _ => Err(custom_error(
                &primary,
                "Unexpected value in boolean expression",
            )),
        })
        .map_prefix(|_, rhs| Ok(Ast::Boolean(BooleanExpr::new_not(rhs?))))
        .map_infix(|lhs, op, rhs| {
            let op = match op.as_rule() {
                Rule::AND => BoolOperator::And,
                Rule::OR => BoolOperator::Or,
                _ => unreachable!(),
            };

            Ok(Ast::Boolean(BooleanExpr::new_in(lhs?, op, rhs?)))
        })
        .parse(pair.into_inner())
}

fn parse_comparison(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Ast> {
    parser
        .boolean
        .map_primary(|primary| match primary.as_rule() {
            Rule::call | Rule::STRING | Rule::NUMBER | Rule::BOOL => {
                parse_expression(primary, parser)
            }
            _ => Err(custom_error(
                &primary,
                "Unexpected value in comparison expression",
            )),
        })
        .map_infix(|lhs, op, rhs| {
            let op = match op.as_rule() {
                Rule::EQ => CompOperator::Eq,
                Rule::NEQ => CompOperator::Neq,
                Rule::LT => CompOperator::Lt,
                Rule::GT => CompOperator::Gt,
                Rule::LT_EQ => CompOperator::LtEq,
                Rule::GT_EQ => CompOperator::GtEq,
                _ => unreachable!(),
            };

            Ok(Ast::Boolean(BooleanExpr::new_comp(lhs?, op, rhs?)))
        })
        .parse(pair.into_inner())
}

fn parse_call(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Ast> {
    match pair.as_rule() {
        Rule::property_call => {
            let mut inner = pair.into_inner();
            let target = inner.next().unwrap();
            let property = inner.next().unwrap();

            Ok(Ast::PropertyCall(
                Box::new(parse_call(target, parser)?),
                Box::new(parse_call(property, parser)?),
            ))
        }

        Rule::list_index => {
            let mut inner = pair.into_inner();
            // NOTE: it can be call only, but not wrapped into Rule::call
            let expression = parse_call(inner.next().unwrap(), parser)?;
            let indices = inner
                .map(|expr| parse_expression(expr, parser))
                .collect::<ParseResult<Vec<Ast>>>()?;

            Ok(indices.into_iter().fold(expression, |acc, index| {
                Ast::ListIndex(ListIndex::new(acc, index))
            }))
        }

        Rule::fn_call => {
            let mut inner = pair.into_inner();
            let id: Id = inner.next().unwrap().as_str().into();
            let args = inner
                .map(|expr| parse_expression(expr, parser))
                .collect::<ParseResult<Vec<Ast>>>()?;
            Ok(Ast::FunctionCall(id, args))
        }

        Rule::var_call => Ok(Ast::Variable(pair.into_inner().as_str().into())),

        Rule::ancestor_ref => Ok(Ast::AncestorRef(AncestorRef(Box::new(parse_call(
            pair.into_inner().next().unwrap(),
            parser,
        )?)))),

        _ => unreachable!(),
    }
}

fn parse_expr_body(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Body> {
    let expressions: Vec<Ast> = pair
        .into_inner()
        .map(|expr| parse_expression(expr, parser))
        .collect::<ParseResult<Vec<Ast>>>()?;

    Ok(Body::new(expressions))
}

pub(crate) fn parse_func_def(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Ast> {
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
    let body = parse_expr_body(inner.next().unwrap(), parser)?;

    Ok(Ast::FunctionDef(Function::new(id, args, body)))
}

fn parse_func_args(pair: Pair<Rule>) -> ParseResult<Vec<Id>> {
    pair.into_inner().map(|id| Ok(id.as_str().into())).collect()
}

fn parse_string_expr(pair: Pair<Rule>, parser: &SparkMLParser) -> ParseResult<Ast> {
    Ok(Ast::StringExpr(Rc::new(
        pair.into_inner()
            .map(|pair| match pair.as_rule() {
                Rule::STRING_INTERP => parse_expression(pair.into_inner().next().unwrap(), parser),
                Rule::STRING_INNER => Ok(Ast::Value(Value::String(pair.as_str().into()))),
                _ => unreachable!(),
            })
            .collect::<ParseResult<_>>()?,
    )))
}

#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub(crate) enum Ast {
    Node(Rc<Node<NodeIdExpr, Self, PhantomData<Self>, PhantomData<Self>>>),
    Object(Rc<Object<Self>>),
    Assignment(Assignment),
    Value(Value),
    StringExpr(Rc<Vec<Self>>),
    FunctionCall(Id, Vec<Self>),
    FunctionDef(Function),
    Variable(Id),
    AncestorRef(AncestorRef),
    If(If),
    Repeat(Repeat),
    Algebraic(Algebraic),
    Boolean(BooleanExpr),
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

            Ast::Node(node) => node.eval(pair, context).map(Value::Node),

            Ast::Object(object) => object.eval(pair, context).map(Rc::new).map(Value::Object),

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

            Ast::Algebraic(expr) => expr.eval(pair, context),

            Ast::Boolean(expr) => expr.eval(pair, context),

            Ast::StringExpr(exprs) => Self::eval_string_expr(exprs, pair, context),

            Ast::If(if_expr) => if_expr.eval(pair, context),

            Ast::Repeat(repeat_expr) => repeat_expr.eval(pair, context),

            _ => todo!(),
        }
    }

    fn eval_string_expr(exprs: &[Self], pair: &Pair<Rule>, context: Context) -> ParseResult<Value> {
        exprs
            .iter()
            .map(|expr| match expr {
                Self::Value(Value::String(s)) => Ok(s.clone()),
                expr => {
                    let value = expr.eval(pair, context.clone())?;
                    Ok(value.to_string())
                }
            })
            .fold(Ok(String::new()), |acc, expr: ParseResult<String>| {
                let mut acc = acc?;
                let expr = expr?;
                acc.push_str(&expr);
                Ok(acc)
            })
            .map(Value::String)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum NodeIdExpr {
    Id(Id),
    String(Box<Ast>),
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

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct If {
    condition: Box<Ast>,
    body: Body,
    else_exprs: Rc<Vec<Else>>,
}

impl If {
    fn new(condition: Ast, body: Body, else_exprs: Vec<Else>) -> Self {
        Self {
            condition: Box::new(condition),
            body,
            else_exprs: Rc::new(else_exprs),
        }
    }

    fn eval(&self, pair: &Pair<Rule>, caller_ctx: Context) -> ParseResult<Value> {
        let context = Context::with_parent(caller_ctx.clone());
        caller_ctx.vars().set_recursive(true);
        caller_ctx.funcs().set_recursive(true);

        match self.condition.eval(pair, caller_ctx.clone())? {
            Value::Boolean(val) => {
                if val {
                    self.body.eval(pair, context)
                } else {
                    self.parse_else(pair, context, caller_ctx)
                }
            }

            _ => {
                return Err(custom_error(
                    pair,
                    "Condition of 'if' statement must be a boolean",
                ))
            }
        }
    }

    fn parse_else(
        &self,
        pair: &Pair<Rule>,
        context: Context,
        caller_ctx: Context,
    ) -> ParseResult<Value> {
        for expr in self.else_exprs.iter() {
            match expr {
                Else::ElseIf(expr) => {
                    let condition = expr.condition.eval(pair, caller_ctx.clone())?;
                    if matches!(condition, Value::Boolean(true)) {
                        return expr.body.eval(pair, context);
                    } else if matches!(condition, Value::Boolean(false)) {
                        continue;
                    } else {
                        return Err(custom_error(
                            pair,
                            "Condition of 'if else' statement must be a boolean",
                        ));
                    }
                }
                Else::IfElse(body) => return body.eval(pair, context),
            }
        }

        Ok(Value::Boolean(false))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Else {
    ElseIf(If),
    IfElse(Body),
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Repeat {
    times: Box<Ast>,
    body: Body,
}

impl Repeat {
    fn new(times: Ast, body: Body) -> Self {
        Self {
            times: Box::new(times),
            body,
        }
    }

    fn eval(&self, pair: &Pair<Rule>, caller_ctx: Context) -> ParseResult<Value> {
        let times = match self.times.eval(pair, caller_ctx.clone())? {
            Value::Number(num) => num as usize,
            _ => {
                return Err(custom_error(
                    pair,
                    "The number of times to repeat must be a number",
                ))
            }
        };

        let context = Context::with_parent(caller_ctx.clone());
        let mut result = Value::Boolean(false);

        for _ in 0..times {
            result = self.body.eval(pair, context.clone())?;
        }

        Ok(result)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Algebraic {
    Neg(Box<Ast>),
    In(AlgebraicIn),
}

impl Algebraic {
    pub(crate) fn new_neg(expr: Ast) -> Self {
        Self::Neg(Box::new(expr))
    }

    pub(crate) fn new_in(left: Ast, operator: MathOperator, right: Ast) -> Self {
        Self::In(AlgebraicIn {
            left: Box::new(left),
            right: Box::new(right),
            operator,
        })
    }

    pub(crate) fn eval(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Value> {
        match self {
            Self::Neg(expr) => Ok(Value::Number(self.eval_num(expr, pair, context)? * -1.0)),
            Self::In(algebraic) => {
                let lhs = self.eval_num(&algebraic.left, pair, context.clone())?;
                let rhs = self.eval_num(&algebraic.right, pair, context)?;

                Ok(Value::Number(match algebraic.operator {
                    MathOperator::Add => lhs + rhs,
                    MathOperator::Sub => lhs - rhs,
                    MathOperator::Mul => lhs * rhs,
                    MathOperator::Div => lhs / rhs,
                    MathOperator::Mod => lhs % rhs,
                }))
            }
        }
    }

    fn eval_num(&self, expr: &Ast, pair: &Pair<Rule>, context: Context) -> ParseResult<f64> {
        match expr.eval(pair, context)? {
            Value::Number(num) => Ok(num),
            _ => Err(custom_error(pair, "Expected a number")),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct AlgebraicIn {
    left: Box<Ast>,
    right: Box<Ast>,
    operator: MathOperator,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum MathOperator {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BooleanExpr {
    Not(Box<Ast>),
    In(BooleanIn),
    Comp(Comparison),
}

impl BooleanExpr {
    pub(crate) fn new_not(expr: Ast) -> Self {
        Self::Not(Box::new(expr))
    }

    pub(crate) fn new_in(left: Ast, operator: BoolOperator, right: Ast) -> Self {
        Self::In(BooleanIn {
            left: Box::new(left),
            right: Box::new(right),
            operator,
        })
    }

    pub(crate) fn new_comp(left: Ast, operator: CompOperator, right: Ast) -> Self {
        Self::Comp(Comparison {
            left: Box::new(left),
            operator,
            right: Box::new(right),
        })
    }

    pub(crate) fn eval(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Value> {
        match self {
            Self::Not(expr) => Ok(Value::Boolean(!self.eval_bool(expr, pair, context)?)),
            Self::In(boolean) => {
                let lhs = self.eval_bool(&boolean.left, pair, context.clone())?;
                let rhs = self.eval_bool(&boolean.right, pair, context)?;

                Ok(Value::Boolean(match boolean.operator {
                    BoolOperator::And => lhs && rhs,
                    BoolOperator::Or => lhs || rhs,
                }))
            }
            Self::Comp(comp) => comp.eval(pair, context.clone()),
        }
    }

    fn eval_bool(&self, expr: &Ast, pair: &Pair<Rule>, context: Context) -> ParseResult<bool> {
        match expr.eval(pair, context)? {
            Value::Boolean(bool) => Ok(bool),
            _ => Err(custom_error(pair, "Expected a boolean")),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct BooleanIn {
    left: Box<Ast>,
    operator: BoolOperator,
    right: Box<Ast>,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum BoolOperator {
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Comparison {
    left: Box<Ast>,
    operator: CompOperator,
    right: Box<Ast>,
}

impl Comparison {
    fn eval(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Value> {
        macro_rules! compare {
            ($lhs:ident, $rhs:ident) => {
                Ok(Value::Boolean(match self.operator {
                    CompOperator::Lt => $lhs < $rhs,
                    CompOperator::Gt => $lhs > $rhs,
                    CompOperator::Eq => $lhs == $rhs,
                    CompOperator::Neq => $lhs != $rhs,
                    CompOperator::LtEq => $lhs <= $rhs,
                    CompOperator::GtEq => $lhs >= $rhs,
                }))
            };
        }

        let lhs = self.left.eval(pair, context.clone())?;
        let rhs = self.right.eval(pair, context)?;

        match (lhs, rhs) {
            (Value::Number(lhs), Value::Number(rhs)) => compare!(lhs, rhs),
            (Value::String(lhs), Value::String(rhs)) => compare!(lhs, rhs),
            (Value::Boolean(lhs), Value::Boolean(rhs)) => compare!(lhs, rhs),
            (lhs, rhs) => Err(custom_error(
                pair,
                &format!(
                    "Cannot compare '{}' with '{}'",
                    lhs.ty_name(),
                    rhs.ty_name()
                ),
            )),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum CompOperator {
    Lt,
    Gt,
    Eq,
    Neq,
    LtEq,
    GtEq,
}

impl<T, S> Node<NodeIdExpr, Ast, PhantomData<T>, PhantomData<S>> {
    pub(crate) fn eval(
        &self,
        pair: &Pair<Rule>,
        caller_ctx: Context,
    ) -> ParseResult<Rc<RefCell<Node<Id, Value, Tween<Value>, Signal>>>> {
        let name = self.name().eval(pair, caller_ctx.clone())?;

        if caller_ctx.has_node(&name) {
            return Err(custom_error(
                pair,
                &format!("Node '{}' already defined in module", name.as_str()),
            ));
        }

        let class = self.class().eval(pair, caller_ctx.clone())?;

        let mut attributes = self.attributes().eval(pair, caller_ctx.clone())?;

        let tweens = attributes
            .take("@tweens")
            .map(|tweens| self.eval_list(tweens, pair))
            .unwrap_or_else(|| Ok(vec![]))?
            .iter()
            .map(|val| self.eval_tween(val, pair))
            .collect::<ParseResult<Vec<_>>>()?;

        let signals = attributes
            .take("@signals")
            .map(|signals| self.eval_list(signals, pair))
            .unwrap_or_else(|| Ok(vec![]))?
            .iter()
            .map(|val| self.eval_signal(val, pair))
            .collect::<ParseResult<Vec<_>>>()?;

        if let Some(meta_attrs) = attributes.take("@attributes") {
            self.eval_meta_attrs(&mut attributes, &meta_attrs, pair)?;
        }

        let children = attributes.take("@children");

        let node = Rc::new(RefCell::new(Node {
            name,
            class,
            attributes,
            tweens,
            signals,
            parent: None,
        }));

        caller_ctx.add_node(node.clone());

        children
            .map(|children| self.eval_list(children, pair))
            .unwrap_or_else(|| Ok(vec![]))?
            .into_iter()
            .try_for_each(|val| match val {
                Value::Node(child) => {
                    child.borrow_mut().set_parent(node.clone());
                    caller_ctx.add_node(child);
                    Ok(())
                }
                _ => Err(custom_error(pair, "Expected a node")),
            })?;

        Ok(node)
    }

    fn eval_list(&self, attr: Attribute<Value>, pair: &Pair<Rule>) -> ParseResult<Vec<Value>> {
        match attr {
            Attribute::Value(val) if matches!(val.as_ref(), Value::List(_)) => match val.as_ref() {
                Value::List(list) => Ok(list.take()),
                _ => unreachable!(),
            },
            _ => Err(custom_error(pair, "Expected a list")),
        }
    }

    fn eval_tween(&self, value: &Value, pair: &Pair<Rule>) -> ParseResult<Tween<Value>> {
        match value {
            Value::Object(obj) => Tween::eval(obj, pair),
            _ => Err(custom_error(pair, "Expected an object")),
        }
    }

    fn eval_signal(&self, value: &Value, pair: &Pair<Rule>) -> ParseResult<Signal> {
        match value {
            Value::Object(obj) => Signal::eval(obj, pair),
            _ => Err(custom_error(pair, "Expected an object")),
        }
    }

    fn eval_meta_attrs(
        &self,
        attributes: &mut Attributes<Value>,
        meta_attrs: &Attribute<Value>,
        pair: &Pair<Rule>,
    ) -> ParseResult<()> {
        let meta_attrs = match meta_attrs {
            Attribute::Value(val) if matches!(val.as_ref(), Value::Object(_)) => match val.as_ref()
            {
                Value::Object(obj) => obj,
                _ => unreachable!(),
            },
            _ => return Err(custom_error(pair, "Expected an object")),
        };

        attributes.extend(meta_attrs.attributes().clone());

        Ok(())
    }
}

impl NodeIdExpr {
    pub(crate) fn eval(&self, pair: &Pair<Rule>, caller_ctx: Context) -> ParseResult<Id> {
        match self {
            Self::Id(id) => Ok(id.clone()),
            Self::String(expr) => self.eval_string_id(expr, pair, caller_ctx),
        }
    }

    fn eval_string_id(
        &self,
        expr: &Ast,
        pair: &Pair<Rule>,
        caller_ctx: Context,
    ) -> ParseResult<Id> {
        match expr.eval(pair, caller_ctx)? {
            Value::String(id) => {
                static RE: OnceCell<Regex> = OnceCell::new();
                let re = RE.get_or_init(|| Regex::new(r"^[^\d]\w+$").unwrap());

                if !re.is_match(id.as_str()) {
                    return Err(custom_error(pair, "Invalid ID"));
                }

                Ok(Id::from(id.clone()))
            }
            _ => Err(custom_error(pair, "Expected a string")),
        }
    }
}

impl Tween<Value> {
    pub(crate) fn eval(obj: &Object<Value>, pair: &Pair<Rule>) -> ParseResult<Self> {
        let mut attrs = obj.attributes().clone();

        if attrs.table().is_empty() {
            return Err(custom_error(
                pair,
                "Tween should has at least one attribute",
            ));
        }

        let method = attrs.take_required("@method", pair)?.get_as_string(pair)?;

        let duration = attrs
            .take_required("@duration", pair)?
            .get_as_number(pair)?;

        macro_rules! get_optional {
            ($key:literal, $type:ty) => {
                attrs
                    .take_optional($key, pair)?
                    .map(|val| match val.as_ref() {
                        Value::String(string) => <$type>::from_str(string.as_str(), pair),
                        _ => {
                            return Err(custom_error(
                                pair,
                                &format!("Expected a string for '{}'", $key),
                            ))
                        }
                    })
                    .unwrap_or_else(|| Ok(Default::default()))?
            };
        }

        macro_rules! get_optional_primitive {
            ($key:literal, $expected:ident) => {
                attrs
                    .take_optional($key, pair)?
                    .map(|val| match val.as_ref() {
                        Value::$expected(val) => Ok(*val),
                        _ => {
                            return Err(custom_error(
                                pair,
                                &format!("Expected a string for '{}'", $key),
                            ))
                        }
                    })
                    .unwrap_or_else(|| Ok(Default::default()))?
            };
        }

        let transition = get_optional!("@transition", Transition);
        let easing = get_optional!("@easing", Easing);
        let delay = get_optional_primitive!("@delay", Number);
        let repeat = get_optional_primitive!("@repeat", Boolean);

        Ok(Self {
            attributes: Rc::new(attrs.table().clone().into()),
            method,
            duration,
            transition,
            easing,
            delay,
            repeat,
        })
    }
}

impl Signal {
    pub(crate) fn eval(obj: &Object<Value>, pair: &Pair<Rule>) -> ParseResult<Self> {
        let mut attrs = obj.attributes().clone();

        let source = attrs.take_required("@source", pair)?.get_as_string(pair)?;

        let destination = attrs
            .take_required("@destination", pair)?
            .get_as_string(pair)?;

        Ok(Signal {
            source,
            destination,
        })
    }
}

impl Object<Ast> {
    pub(crate) fn eval(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Object<Value>> {
        let context = Context::with_parent(context);

        context.vars().set_recursive(false);
        context.funcs().set_recursive(false);

        if !self.body().is_empty() {
            let _ = self.body().eval(pair, context.clone())?;
        }

        let attributes = self.attributes().eval(pair, context.clone())?;
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
        let mut table = IndexMap::new();

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

    pub(crate) fn is_empty(&self) -> bool {
        self.expressions.is_empty()
    }

    pub(crate) fn eval(&self, pair: &Pair<Rule>, context: Context) -> ParseResult<Value> {
        if self.is_empty() {
            return Err(custom_error(pair, "Body should return an expression"));
        }

        if self.expressions.len() == 1 {
            return self.expressions[0].eval(pair, context);
        }

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
            let parser = SparkMLParser::default();
            let pair = parse!($code, $rule);
            assert!($parse_func(pair.clone(), &parser).is_err());
        }};
    }

    macro_rules! parse_eq {
        ($code:literal, $rule:ident, $parse_func:ident, $expected:expr) => {{
            let parser = SparkMLParser::default();
            let pair = parse!($code, $rule);
            assert_eq!($parse_func(pair.clone(), &parser).unwrap(), $expected);
        }};
    }

    macro_rules! eval_ok {
        ($code:literal, $rule:ident, $parse_func:ident, $context:expr) => {{
            let parser = SparkMLParser::default();
            let pair = parse!($code, $rule);
            $parse_func(pair.clone(), &parser)
                .unwrap()
                .eval(&pair, $context)
                .unwrap();
        }};
    }

    macro_rules! eval_err {
        ($code:literal, $rule:ident, $parse_func:ident, $context:expr) => {{
            let parser = SparkMLParser::default();
            let pair = parse!($code, $rule);
            assert!($parse_func(pair.clone(), &parser)
                .unwrap()
                .eval(&pair, $context)
                .is_err());
        }};
    }

    macro_rules! eval_eq {
        ($code:literal, $rule:ident, $parse_func:ident, $context:expr, $expected:expr) => {{
            let parser = SparkMLParser::default();
            let pair = parse!($code, $rule);
            assert_eq!(
                $parse_func(pair.clone(), &parser)
                    .unwrap()
                    .eval(&pair, $context)
                    .unwrap(),
                $expected
            );
        }};
    }

    #[test]
    fn test_function() {
        let parser = SparkMLParser::default();
        let pair = parse!(
            r#"fn foo(a, b)
                    n = 10
                    20"#,
            func_def
        );

        if let Ast::FunctionDef(function) = parse_func_def(pair, &parser).unwrap() {
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
        let parser = SparkMLParser::default();
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

        let expr = parse_object(pair.clone(), &parser).unwrap();

        if let Ast::Object(object) = expr.clone() {
            assert_eq!(object.attributes().table().len(), 3);

            match object.attributes().get("foo") {
                Some(Attribute::Value(value)) => {
                    assert!(matches!(value.as_ref(), &Ast::FunctionCall(_, _)));
                }
                _ => panic!("Expected value"),
            }

            match object.attributes().get("bar") {
                Some(Attribute::Attributes(attrs)) => match attrs.get("@child") {
                    Some(Attribute::Value(value)) => {
                        assert!(matches!(value.as_ref(), &Ast::Value(Value::Number(_))));
                    }
                    _ => panic!("Expected value"),
                },
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
                object.attributes().get("foo"),
                Some(&Attribute::Value(Value::Number(1.0).into()))
            );
        } else {
            panic!("Expected object");
        }
    }

    #[test]
    fn test_node() {
        parse_eq!(
            r#"Node from Node"#,
            expression,
            parse_expression,
            Ast::Node(Rc::new(Node::new_default(
                NodeIdExpr::Id("Node".into()),
                NodeIdExpr::Id("Node".into()),
                Attributes::default()
            )))
        );

        parse_eq!(
            r#""N{ call }de" from Node"#,
            expression,
            parse_expression,
            Ast::Node(Rc::new(Node::new_default(
                NodeIdExpr::String(Box::new(Ast::StringExpr(Rc::new(vec![
                    Ast::Value(Value::String("N".into())),
                    Ast::Variable("call".into()),
                    Ast::Value(Value::String("de".into()))
                ])))),
                NodeIdExpr::Id("Node".into()),
                Attributes::default()
            )))
        );

        parse_eq!(
            r#"Node from Node
                foo: 0"#,
            expression,
            parse_expression,
            Ast::Node(Rc::new(Node::new_default(
                NodeIdExpr::Id("Node".into()),
                NodeIdExpr::Id("Node".into()),
                [(
                    Key::Key("foo".into()),
                    Attribute::Value(Rc::new(Ast::Value(Value::Number(0.0).into()))),
                )]
                .into()
            )))
        );

        let context = Context::default();

        eval_eq!(
            r#"Node from Node
                foo: 0"#,
            expression,
            parse_expression,
            context.clone(),
            Node {
                name: "Node".into(),
                class: "Node".into(),
                attributes: [("foo".into(), Attribute::Value(Rc::new(0.0.into())))].into(),
                parent: None,
                tweens: vec![],
                signals: vec![],
            }
            .into()
        );

        let expected: Rc<RefCell<Node<_, Value, _, _>>> = Rc::new(RefCell::new(Node {
            name: "Foo".into(),
            class: "Foo".into(),
            attributes: Default::default(),
            parent: None,
            tweens: vec![],
            signals: vec![],
        }));

        eval_eq!(
            r#"Foo from Foo
                @children: [
                    Bar from Bar,
                    Baz from Baz
                ]"#,
            expression,
            parse_expression,
            context.clone(),
            Value::Node(expected.clone())
        );

        // the context should be updated with children
        assert_eq!(
            context.get_node(&"Bar".into()),
            Some(Rc::new(RefCell::new(Node {
                name: "Bar".into(),
                class: "Bar".into(),
                attributes: Default::default(),
                parent: Some(expected.clone()),
                tweens: vec![],
                signals: vec![],
            })))
        );

        assert_eq!(
            context.get_node(&"Baz".into()),
            Some(Rc::new(RefCell::new(Node {
                name: "Baz".into(),
                class: "Baz".into(),
                attributes: Default::default(),
                parent: Some(expected.clone()),
                tweens: vec![],
                signals: vec![],
            })))
        );

        // redefining a node is not allowed
        eval_err!(
            r#"Foo from Foo"#,
            expression,
            parse_expression,
            context.clone()
        );

        eval_ok!(
            r#""Test{ "????????????" }" from A"#,
            expression,
            parse_expression,
            context.clone()
        );

        eval_ok!(
            r#""Test{ 1 }" from A"#,
            expression,
            parse_expression,
            context.clone()
        );

        let expected = Node {
            name: "A".into(),
            class: "A".into(),
            attributes: [("foo".into(), 0.0.into())].into(),
            parent: None,
            tweens: vec![Tween {
                attributes: Rc::new([("foo".into(), 1.0.into())].into()),
                method: "tween_foo".to_string(),
                duration: 1.0,
                transition: Transition::Bounce,
                easing: Easing::In,
                delay: 0.0,
                repeat: false,
            }],
            signals: vec![Signal {
                source: String::from("A.click"),
                destination: String::from("tween_foo"),
            }],
        };

        eval_eq!(
            r#"A from A
                @tweens: [
                    {
                        foo: 1
                        @method: "tween_foo"
                        @duration: 1
                        @transition: "bounce"
                        @easing: "in"
                    }
                    ]
                @signals: [
                    {
                        @source: "A.click"
                        @destination: "tween_foo"
                    }
                    ]
                @attributes: {
                    foo: 0
                }"#,
            expression,
            parse_expression,
            context.clone(),
            expected.into()
        );

        eval_err!(
            r#"B from B
                @children: [
                    C from C,
                    true
                ]"#,
            expression,
            parse_expression,
            context.clone()
        );

        eval_err!(
            r#""Test{ "@" }" from A"#,
            expression,
            parse_expression,
            context.clone()
        );

        eval_err!(
            r#""1Test" from A"#,
            expression,
            parse_expression,
            context.clone()
        );

        eval_err!(
            r#""1" from A"#,
            expression,
            parse_expression,
            context.clone()
        );
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

    #[test]
    fn test_algebraic_expr() {
        parse_eq!(
            "1 + 2",
            expression,
            parse_expression,
            Ast::Algebraic(Algebraic::new_in(
                Ast::Value(Value::Number(1.0)),
                MathOperator::Add,
                Ast::Value(Value::Number(2.0))
            ))
        );

        parse_eq!(
            "-(1 + 2) * 3",
            expression,
            parse_expression,
            Ast::Algebraic(Algebraic::new_in(
                Ast::Algebraic(Algebraic::new_neg(Ast::Algebraic(Algebraic::new_in(
                    Ast::Value(Value::Number(1.0)),
                    MathOperator::Add,
                    Ast::Value(Value::Number(2.0))
                )))),
                MathOperator::Mul,
                Ast::Value(Value::Number(3.0))
            ))
        );

        parse_eq!(
            "1 + n * 2 / (10 % call(1,2))",
            expression,
            parse_expression,
            Ast::Algebraic(Algebraic::new_in(
                Ast::Value(Value::Number(1.0)),
                MathOperator::Add,
                Ast::Algebraic(Algebraic::new_in(
                    Ast::Algebraic(
                        // n * 2
                        Algebraic::new_in(
                            Ast::Variable("n".into()),
                            MathOperator::Mul,
                            Ast::Value(Value::Number(2.0))
                        )
                    ),
                    MathOperator::Div,
                    Ast::Algebraic(Algebraic::new_in(
                        // (10 % call(1,2))
                        Ast::Value(Value::Number(10.0)),
                        MathOperator::Mod,
                        Ast::FunctionCall(
                            "call".into(),
                            vec![
                                Ast::Value(Value::Number(1.0)),
                                Ast::Value(Value::Number(2.0))
                            ]
                        )
                    ))
                ))
            ))
        );

        let context = Context::default();

        eval_ok!("n = 2 * 3", assignment, parse_expression, context.clone());

        eval_ok!(
            "fn call(a, b)
                a + b",
            func_def,
            parse_func_def,
            context.clone()
        );

        eval_eq!(
            "1 + n * 2 / (10 % call(1,2))",
            expression,
            parse_expression,
            context.clone(),
            Value::Number(1.0 + 2.0 * 3.0 * 2.0 / (10.0 % (1.0 + 2.0)))
        );

        eval_ok!("bar = true", assignment, parse_expression, context.clone());

        eval_err!("bar * 2", expression, parse_expression, context.clone());
    }

    #[test]
    fn test_boolean_expr() {
        parse_eq!(
            "true && false",
            expression,
            parse_expression,
            Ast::Boolean(BooleanExpr::new_in(
                Ast::Value(Value::Boolean(true)),
                BoolOperator::And,
                Ast::Value(Value::Boolean(false))
            ))
        );

        parse_eq!(
            "10 < 1",
            expression,
            parse_expression,
            Ast::Boolean(BooleanExpr::new_comp(
                Ast::Value(Value::Number(10.0)),
                CompOperator::Lt,
                Ast::Value(Value::Number(1.0))
            ))
        );

        let context = Context::default();

        eval_eq!(
            "true && false",
            expression,
            parse_expression,
            context.clone(),
            Value::Boolean(false)
        );

        eval_eq!(
            "10 < 1",
            expression,
            parse_expression,
            context.clone(),
            Value::Boolean(false)
        );

        eval_ok!("n = 1", assignment, parse_expression, context.clone());
        eval_ok!("z = 2", assignment, parse_expression, context.clone());
        eval_ok!("a = true", assignment, parse_expression, context.clone());
        eval_ok!("b = false", assignment, parse_expression, context.clone());

        let n = 1.0;
        let z = 2.0;
        let a = true;
        let b = false;

        eval_eq!(
            "!(n < z && a) || !a || (n >= z || n != z && !b)",
            expression,
            parse_expression,
            context,
            Value::Boolean(!(n < z && a) || !a || (n >= z || n != z && !b))
        );
    }

    #[test]
    fn test_string() {
        parse_eq!(
            r#""This is a string\nhello""#,
            expression,
            parse_expression,
            Ast::StringExpr(Rc::new(vec![Ast::Value(Value::String(
                "This is a string\\nhello".to_string()
            ))]))
        );

        parse_eq!(
            r#""{foo}\{{bar}} \{te} test { call(0,1) } ""#,
            expression,
            parse_expression,
            Ast::StringExpr(Rc::new(vec![
                Ast::Variable("foo".into()),
                Ast::Value(Value::String("\\{".to_string())),
                Ast::Variable("bar".into()),
                Ast::Value(Value::String("} \\{te} test ".to_string())),
                Ast::FunctionCall(
                    "call".into(),
                    vec![
                        Ast::Value(Value::Number(0.0)),
                        Ast::Value(Value::Number(1.0))
                    ]
                ),
                Ast::Value(Value::String(" ".to_string()))
            ]))
        );

        let context = Context::default();

        eval_ok!("foo = 1", assignment, parse_expression, context.clone());
        eval_ok!("bar = 2", assignment, parse_expression, context.clone());
        eval_ok!(
            r#"fn call(a, b)
                a + b"#,
            func_def,
            parse_func_def,
            context.clone()
        );

        eval_eq!(
            r#""{foo}\{{bar}} \{te} test { call(3,4) } ""#,
            expression,
            parse_expression,
            context.clone(),
            Value::String("1\\{2} \\{te} test 7 ".to_string())
        );
    }

    #[test]
    fn test_if_expr() {
        parse_eq!(
            r#"if true
                1
            else if true
                2
            else if false
                3           
            else
                4"#,
            expression,
            parse_expression,
            Ast::If(If::new(
                Ast::Value(Value::Boolean(true)),
                Body::new(vec![Ast::Value(Value::Number(1.0))]),
                vec![
                    Else::ElseIf(If::new(
                        Ast::Value(Value::Boolean(true)),
                        Body::new(vec![Ast::Value(Value::Number(2.0))]),
                        vec![],
                    )),
                    Else::ElseIf(If::new(
                        Ast::Value(Value::Boolean(false)),
                        Body::new(vec![Ast::Value(Value::Number(3.0))]),
                        vec![],
                    )),
                    Else::IfElse(Body::new(vec![Ast::Value(Value::Number(4.0))])),
                ]
            ))
        );

        let context = Context::default();

        eval_eq!(
            r#"if true
                1
            else if true
                2
            else if false
                3           
            else
                4"#,
            expression,
            parse_expression,
            context.clone(),
            Value::Number(1.0)
        );

        eval_eq!(
            r#"if false
                1
            else if true
                2
            else if false
                3           
            else
                4"#,
            expression,
            parse_expression,
            context.clone(),
            Value::Number(2.0)
        );

        eval_eq!(
            r#"if false
                1
            else if false
                2
            else if true
                3           
            else
                4"#,
            expression,
            parse_expression,
            context.clone(),
            Value::Number(3.0)
        );

        eval_eq!(
            r#"if false
                1
            else if false
                2
            else if false
                3           
            else
                4"#,
            expression,
            parse_expression,
            context.clone(),
            Value::Number(4.0)
        );

        eval_eq!(
            r#"if false
                1"#,
            expression,
            parse_expression,
            context.clone(),
            Value::Boolean(false)
        );
    }

    #[test]
    fn test_repeat_expr() {
        parse_eq!(
            r#"repeat 10
                1"#,
            expression,
            parse_expression,
            Ast::Repeat(Repeat::new(
                Ast::Value(Value::Number(10.0)),
                Body::new(vec![Ast::Value(Value::Number(1.0))])
            ))
        );

        let context = Context::default();

        eval_err!(
            r#"repeat true
                1"#,
            expression,
            parse_expression,
            context.clone()
        );

        eval_ok!("n = 0", assignment, parse_assignment, context.clone());

        eval_eq!(
            r#"repeat 10
                n = n + 1
                n"#,
            expression,
            parse_expression,
            context.clone(),
            Value::Number(10.0)
        );
    }
}
