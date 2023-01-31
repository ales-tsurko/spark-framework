//! This crate contains pest tools to simplify development of pest written parsers.
use pest::{iterators::Pair, iterators::Pairs, RuleType};

/// Returns the parser tree as a readable string (as on the pest' site).
pub fn parser_tree_as_string<Rule: RuleType>(pairs: Pairs<Rule>) -> String {
    pairs
        .map(|pair| format_pair::<Rule>(pair, 0, true))
        .collect::<Vec<_>>()
        .join("\n")
}

// stolen and adapted from https://github.com/pest-parser/site/blob/master/src/lib.rs
fn format_pair<Rule: RuleType>(pair: Pair<Rule>, indent_level: usize, is_newline: bool) -> String {
    let indent = if is_newline {
        "  ".repeat(indent_level)
    } else {
        "".to_string()
    };

    let children: Vec<_> = pair.clone().into_inner().collect();
    let len = children.len();
    let children: Vec<_> = children
        .into_iter()
        .map(|pair| {
            format_pair(
                pair,
                if len > 1 {
                    indent_level + 1
                } else {
                    indent_level
                },
                len > 1,
            )
        })
        .collect();

    let dash = if is_newline { "- " } else { "" };

    match len {
        0 => format!(
            "{}{}{:?}: {:?}",
            indent,
            dash,
            pair.as_rule(),
            pair.as_str()
        ),
        1 => format!("{}{}{:?} > {}", indent, dash, pair.as_rule(), children[0]),
        _ => format!(
            "{}{}{:?}\n{}",
            indent,
            dash,
            pair.as_rule(),
            children.join("\n")
        ),
    }
}
