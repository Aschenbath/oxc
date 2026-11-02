use oxc_ast::{
    AstKind,
    ast::{Argument, Expression, FunctionBody, MemberExpression, Statement, UnaryOperator},
};
use oxc_diagnostics::OxcDiagnostic;
use oxc_macros::declare_oxc_lint;
use oxc_span::Span;

use crate::{AstNode, ast_util::get_declaration_of_variable, context::LintContext, rule::Rule};

fn no_negated_array_predicate_diagnostic(
    span: Span,
    method: &str,
    replacement: &str,
) -> OxcDiagnostic {
    OxcDiagnostic::warn(format!(
        "Prefer `Array#{replacement}()` with a negated predicate over negating `Array#{method}()`."
    ))
    .with_help(format!("Replace `!array.{method}(x => …)` with `array.{replacement}(x => !…)`."))
    .with_label(span)
}

#[derive(Debug, Default, Clone)]
pub struct NoNegatedArrayPredicate;

declare_oxc_lint!(
    /// ### What it does
    ///
    /// Disallow negating `Array#every()` or `Array#some()` called with a predicate that can be
    /// negated instead.
    ///
    /// ### Why is this bad?
    ///
    /// `!array.every(x => x.ok)` is a double negative in disguise: "not every item is ok"
    /// reads more directly as "some item is not ok", `array.some(x => !x.ok)`.
    ///
    /// ### Examples
    ///
    /// Examples of **incorrect** code for this rule:
    /// ```javascript
    /// const hasInvalid = !items.every(item => item.valid);
    /// const isEmpty = !items.some(item => item.selected);
    /// ```
    ///
    /// Examples of **correct** code for this rule:
    /// ```javascript
    /// const hasInvalid = items.some(item => !item.valid);
    /// const isEmpty = items.every(item => !item.selected);
    /// ```
    NoNegatedArrayPredicate,
    unicorn,
    style,
    pending,
    version = "next",
    short_description = "Disallow negated array predicate calls.",
);

impl Rule for NoNegatedArrayPredicate {
    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {
        let AstKind::UnaryExpression(unary) = node.kind() else {
            return;
        };
        if unary.operator != UnaryOperator::LogicalNot {
            return;
        }
        let Expression::CallExpression(call) = unary.argument.get_inner_expression() else {
            return;
        };
        if call.optional
            || call.type_arguments.is_some()
            || !(1..=2).contains(&call.arguments.len())
        {
            return;
        }
        let Some(MemberExpression::StaticMemberExpression(member)) =
            call.callee.get_inner_expression().as_member_expression()
        else {
            return;
        };
        if member.optional {
            return;
        }
        let method = member.property.name.as_str();
        let replacement = match method {
            "every" => "some",
            "some" => "every",
            _ => return,
        };
        let has_returned_expression = match &call.arguments[0] {
            Argument::ArrowFunctionExpression(arrow) => {
                !arrow.r#async
                    && arrow.return_type.is_none()
                    && arrow.type_parameters.is_none()
                    && (arrow.is_expression()
                        || arrow
                            .body
                            .as_function_body()
                            .is_some_and(|body| has_single_return(body)))
            }
            Argument::FunctionExpression(function) => {
                !function.r#async
                    && !function.generator
                    && function.return_type.is_none()
                    && function.type_parameters.is_none()
                    && function.body.as_ref().is_some_and(|body| has_single_return(body))
            }
            _ => false,
        };
        if !has_returned_expression || is_known_non_indexed_collection(&member.object, ctx) {
            return;
        }
        ctx.diagnostic(no_negated_array_predicate_diagnostic(
            member.property.span,
            method,
            replacement,
        ));
    }
}

/// `{ return value; }`
fn has_single_return(body: &FunctionBody) -> bool {
    matches!(
        body.statements.as_slice(),
        [Statement::ReturnStatement(statement)] if statement.argument.is_some()
    )
}

/// Receivers that are clearly not arrays, so `every`/`some` may mean anything.
fn is_known_non_indexed_collection<'a>(object: &Expression<'a>, ctx: &LintContext<'a>) -> bool {
    match object.get_inner_expression() {
        Expression::Identifier(ident) => {
            let Some(declaration) = get_declaration_of_variable(ident, ctx.semantic()) else {
                return false;
            };
            let AstKind::VariableDeclarator(declarator) = declaration.kind() else {
                return false;
            };
            matches!(
                ctx.nodes().parent_kind(declaration.id()),
                AstKind::VariableDeclaration(declaration) if declaration.kind.is_const()
            ) && declarator
                .init
                .as_ref()
                .is_some_and(|init| is_non_indexed_collection_literal(init.get_inner_expression()))
        }
        expression => is_non_indexed_collection_literal(expression),
    }
}

fn is_non_indexed_collection_literal(expression: &Expression) -> bool {
    match expression {
        Expression::ObjectExpression(_)
        | Expression::StringLiteral(_)
        | Expression::TemplateLiteral(_)
        | Expression::NumericLiteral(_)
        | Expression::BooleanLiteral(_)
        | Expression::NullLiteral(_)
        | Expression::BigIntLiteral(_)
        | Expression::RegExpLiteral(_)
        | Expression::ArrowFunctionExpression(_)
        | Expression::FunctionExpression(_)
        | Expression::ClassExpression(_) => true,
        Expression::NewExpression(new_expr) => matches!(
            new_expr.callee.get_inner_expression(),
            Expression::Identifier(ident) if matches!(ident.name.as_str(), "Set" | "Map" | "WeakSet" | "WeakMap" | "Object")
        ),
        _ => false,
    }
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        "array.every(x => x)",
        "array.some(x => !x)",
        "!array.filter(x => x)",
        "!array.every(fn)",
        "!array.every()",
        "!array.every(x => x, thisArg, extra)",
        "!array?.every(x => x)",
        "!array.every?.(x => x)",
        "!array[every](x => x)",
        "!array.every(async x => x)",
        "!array.every(function* (x) { yield x })",
        "!array.every(x => { foo(); return x; })",
        "!array.every(x => { x; })",
        "!array.every(function (x) { return; })",
        "!array.every((x): boolean => x)",
        "!array.every<T>(x => x)",
        "-array.every(x => x)",
        "!new Set(foo).every(x => x)",
        "!({}).some(x => x)",
        "const foo = new Map(); !foo.some(x => x)",
        "const foo = {every() {}}; !foo.every(x => x)",
    ];

    let fail = vec![
        "!array.every(x => x.ok)",
        "!array.some(x => x.ok)",
        "!array.every(function (x) { return x.ok; })",
        "!array.every(x => { return x.ok; })",
        "!array.some(x => x, thisArg)",
        "!(array.some(x => x))",
        "!array.some(x => x)!",
        "!foo.bar.every(x => !x)",
        "if (!array.every(x => x > 0)) {}",
        "let foo = {}; !foo.every(x => x)",
        "!new Array(3).some(x => x)",
    ];

    Tester::new(NoNegatedArrayPredicate::NAME, NoNegatedArrayPredicate::PLUGIN, pass, fail)
        .test_and_snapshot();
}
