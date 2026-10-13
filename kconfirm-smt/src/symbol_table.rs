//! The encoder's normalized, single-target symbol table.
//!
//! Linting retains raw partial definitions in kconfirm-lib. The encoder consumes
//! desugared entries, with one definition per symbol and no architecture state.

use std::collections::BTreeMap;

use nom_kconfig::{
    Attribute, Entry, Symbol,
    attribute::{
        AndExpression, Atom, DefaultAttribute, Expression, OrExpression, Range, Term, r#type::Type,
    },
    symbol::ConstantSymbol,
    tristate::Tristate,
};
use z3::ast::{Int, String as Z3String};
use z3_ternary::Ternary;

#[derive(Clone, Debug)]
pub enum Z3Types {
    String(Z3String),
    Integer(Int),
    Ternary(Ternary),
}

macro_rules! conversion {
    ($ty:ty, $variant:ident) => {
        impl TryFrom<Z3Types> for $ty {
            type Error = &'static str;

            fn try_from(value: Z3Types) -> Result<Self, Self::Error> {
                match value {
                    Z3Types::$variant(value) => Ok(value),
                    _ => Err("unexpected SMT expression type"),
                }
            }
        }
    };
}

conversion!(Int, Integer);
conversion!(Z3String, String);
conversion!(Ternary, Ternary);

#[derive(Clone, Debug, Default)]
pub struct TypeInfo {
    pub kconfig_type: Option<Type>,
    pub z3_type: Option<Z3Types>,
    // Ordered reverse dependencies keep the generated SMT terms reproducible.
    pub selected_by: BTreeMap<String, Vec<Option<Expression>>>,
    pub implied_by: BTreeMap<String, Vec<Option<Expression>>>,
    pub definition: Option<AttributeDef>,
}

#[derive(Clone, Debug, Default)]
pub struct AttributeDef {
    pub kconfig_dependencies: Option<Expression>,
    pub kconfig_ranges: Vec<Range>,
    pub kconfig_defaults: Vec<DefaultAttribute>,
    pub visibility: Option<Expression>,
}

pub(crate) struct ChoiceData {
    pub dependencies: Vec<Expression>,
    pub defaults: Vec<DefaultAttribute>,
    pub config_options: Vec<String>,
}

#[derive(Default)]
pub(crate) struct SymbolTable {
    // Symbol iteration determines variable creation and assertion order.
    pub raw: BTreeMap<String, TypeInfo>,
    pub choices: Vec<ChoiceData>,
    pub modules_option: Option<String>,
}

fn unconditional() -> Expression {
    OrExpression::Term(AndExpression::Term(Term::Atom(Atom::Symbol(
        Symbol::Constant(ConstantSymbol::Tristate(Tristate::Yes)),
    ))))
}

impl SymbolTable {
    /// Entries must have passed through kconfirm-desugar first.
    pub fn from_entries(entries: Vec<Entry>) -> Self {
        let mut table = Self::default();
        table.collect(entries);
        table
    }

    fn collect(&mut self, entries: Vec<Entry>) {
        for entry in entries {
            match entry {
                Entry::Config(config) | Entry::MenuConfig(config) => {
                    let mut definition = AttributeDef::default();
                    let mut kconfig_type = None;
                    for attribute in config.attributes {
                        match attribute {
                            Attribute::Type(ty) => kconfig_type = Some(ty.r#type),
                            Attribute::Default(default) => {
                                definition.kconfig_defaults.push(default)
                            }
                            Attribute::Range(range) => definition.kconfig_ranges.push(range),
                            Attribute::DependsOn(dep) => {
                                assert!(
                                    definition.kconfig_dependencies.is_none(),
                                    "dependencies must be combined before encoding"
                                );
                                definition.kconfig_dependencies = Some(dep.expression);
                            }
                            Attribute::Prompt(prompt) => {
                                definition.visibility =
                                    Some(prompt.r#if.unwrap_or_else(unconditional));
                            }
                            Attribute::Select(select) => {
                                self.raw
                                    .entry(select.symbol)
                                    .or_default()
                                    .selected_by
                                    .entry(config.symbol.clone())
                                    .or_default()
                                    .push(select.r#if);
                            }
                            Attribute::Imply(imply) => {
                                self.raw
                                    .entry(imply.symbol.to_string())
                                    .or_default()
                                    .implied_by
                                    .entry(config.symbol.clone())
                                    .or_default()
                                    .push(imply.r#if);
                            }
                            Attribute::Modules => self.modules_option = Some(config.symbol.clone()),
                            _ => {}
                        }
                    }
                    let info = self.raw.entry(config.symbol).or_default();
                    assert!(
                        info.definition.is_none(),
                        "partial definitions must be merged before encoding"
                    );
                    info.kconfig_type = kconfig_type;
                    info.definition = Some(definition);
                }
                Entry::Menu(menu) => self.collect(menu.entries),
                Entry::Choice(choice) => {
                    let mut data = ChoiceData {
                        dependencies: Vec::new(),
                        defaults: Vec::new(),
                        config_options: Vec::new(),
                    };
                    for attribute in choice.options {
                        match attribute {
                            Attribute::DependsOn(dep) => data.dependencies.push(dep.expression),
                            Attribute::Default(default) => data.defaults.push(default),
                            _ => {}
                        }
                    }
                    for entry in &choice.entries {
                        if let Entry::Config(config) | Entry::MenuConfig(config) = entry {
                            data.config_options.push(config.symbol.clone());
                        }
                    }
                    self.collect(choice.entries);
                    self.choices.push(data);
                }
                Entry::If(_)
                | Entry::Source(_)
                | Entry::OSource(_)
                | Entry::RSource(_)
                | Entry::OrSource(_) => {
                    unreachable!("containers must be expanded before encoding")
                }
                _ => {}
            }
        }
    }
}
