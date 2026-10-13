// SPDX-License-Identifier: GPL-2.0-only
//! --confirm mode checks query over the same value constraints used
//! `kconfirm-smt`. Track the source properties separately because modeling
//! merges definitions and removes redundant defaults, which are what some of
//! these checks inspect.

use std::collections::{BTreeMap, HashMap};

use kconfirm_desugar::desugar_for_analysis;
use kconfirm_lib::{AnalysisArgs, Check, Finding, Severity};
use nom_kconfig::{
    Attribute, Entry,
    attribute::Expression,
    entry::{Config, Source},
};
use z3::{
    SatResult,
    ast::{Ast, Bool, Int},
};
use z3_ternary::{Ternary, and, bool_and, bool_or, eq, le, lt, or};

use super::failure;
use kconfirm_smt::{
    SmtModel, Z3Types, definition_dependencies, model_condition, model_int_bound,
    model_int_value_expr, model_kconfig_or_expr, model_string_value_expr,
};
use nom_kconfig::attribute::r#type::Type;

const SEMANTIC_CHECKS: &[Check] = &[
    Check::SelectVisible,
    Check::DuplicateDependency,
    Check::DuplicateRange,
    Check::DeadRange,
    Check::DuplicateSelect,
    Check::DeadSelect,
    Check::DuplicateDefault,
    Check::DeadDefault,
    Check::OutOfRangeDefault,
    Check::DuplicateDefaultValue,
    Check::ConstantCondition,
    Check::DuplicateImply,
    Check::DeadImply,
];

pub(crate) fn needs_solver(args: &AnalysisArgs) -> bool {
    args.is_enabled(Check::UnmetDependency)
        || args.is_enabled(Check::DeadSubrange)
        || SEMANTIC_CHECKS.iter().any(|&check| args.is_enabled(check))
}

pub(crate) fn structural_checks(source: &Source, args: &AnalysisArgs) -> Vec<Finding> {
    let mut structural = AnalysisArgs::new();
    for check in [Check::UngroupedAttribute, Check::DeadLink] {
        if args.is_enabled(check) {
            structural.enable_check(check);
        }
    }
    if !structural.is_enabled(Check::UngroupedAttribute) && !structural.is_enabled(Check::DeadLink)
    {
        return Vec::new();
    }
    kconfirm_lib::analyze(
        &structural,
        &mut kconfirm_lib::SymbolTable::new(),
        source
            .kconfigs
            .iter()
            .flat_map(|ast| ast.entries.clone())
            .collect(),
    )
}

#[derive(Default)]
pub(crate) struct Analysis {
    definitions: BTreeMap<String, Vec<Config>>,
}

impl Analysis {
    pub fn new(entries: Vec<Entry>) -> Self {
        let mut analysis = Self::default();
        analysis.collect(entries);
        analysis
    }

    fn collect(&mut self, entries: Vec<Entry>) {
        for entry in entries {
            match entry {
                Entry::Config(config) | Entry::MenuConfig(config) => {
                    self.definitions
                        .entry(config.symbol.clone())
                        .or_default()
                        .push(config);
                }
                Entry::Menu(menu) => self.collect(menu.entries),
                Entry::Choice(choice) => self.collect(choice.entries),
                _ => {}
            }
        }
    }
}

struct DefaultProperty {
    text: String,
    value: Z3Types,
    condition: Ternary,
    conditional: bool,
}

struct RangeProperty {
    text: String,
    lower: Int,
    upper: Int,
    guard: Bool,
}

struct Edge {
    target: String,
    text: String,
    pull: Ternary,
}

struct Checker<'a> {
    model: &'a SmtModel,
    analysis: &'a Analysis,
    args: &'a AnalysisArgs,
    findings: Vec<Finding>,
    answers: HashMap<Bool, bool>,
}

pub(crate) fn check(model: &SmtModel, args: &AnalysisArgs) -> Vec<Finding> {
    if !SEMANTIC_CHECKS.iter().any(|&check| args.is_enabled(check)) {
        return Vec::new();
    }
    let analysis = Analysis::new(desugar_for_analysis(model.source().clone()));
    let mut checker = Checker {
        model,
        analysis: &analysis,
        args,
        findings: Vec::new(),
        answers: HashMap::new(),
    };
    for (symbol, definitions) in &analysis.definitions {
        // An inconclusive query reports failed_model and stops this symbol's
        // checks. It must never be mistaken for a proof of unreachability.
        let _ = checker.symbol(symbol, definitions);
    }
    checker.findings
}

impl Checker<'_> {
    fn enabled(&self, checks: &[Check]) -> bool {
        checks.iter().any(|&check| self.args.is_enabled(check))
    }

    fn report(&mut self, symbol: &str, check: Check, message: impl Into<String>) {
        if self.args.is_enabled(check) {
            self.findings.push(Finding {
                severity: if check == Check::DuplicateDefaultValue {
                    Severity::Style
                } else {
                    Severity::Warning
                },
                check,
                symbol: Some(symbol.to_owned()),
                arch: None,
                message: message.into(),
            });
        }
    }

    fn possible(&mut self, symbol: &str, check: Check, predicate: Bool) -> Result<bool, ()> {
        // The base model has already been checked SAT. Queries never change
        // its assertions, so repeated conditions can share their answers.
        let predicate = predicate.simplify();
        if let Some(value) = predicate
            .as_bool()
            .or_else(|| self.answers.get(&predicate).copied())
        {
            return Ok(value);
        }
        match self
            .model
            .solver()
            .check_assumptions(std::slice::from_ref(&predicate))
        {
            result @ (SatResult::Sat | SatResult::Unsat) => {
                let value = result == SatResult::Sat;
                self.answers.insert(predicate, value);
                Ok(value)
            }
            SatResult::Unknown => {
                self.findings.push(failure(
                    Check::FailedModel,
                    format!(
                        "{} check inconclusive for {symbol}: {:?}",
                        check.as_str(),
                        self.model.solver().get_reason_unknown()
                    ),
                ));
                Err(())
            }
        }
    }

    fn condition(&self, expression: Option<&Expression>) -> Ternary {
        expression.map_or_else(Ternary::y, |expression| {
            model_condition(self.model.symbols(), expression.clone())
        })
    }

    fn dependencies(&self, definition: &Config) -> Vec<Ternary> {
        definition
            .attributes
            .iter()
            .filter_map(|attribute| match attribute {
                Attribute::DependsOn(dep) => Some(self.condition(Some(&dep.expression))),
                _ => None,
            })
            .collect()
    }

    fn visibility(&self, symbol: &str) -> Ternary {
        let mut prompts = Vec::new();
        if let Some(definitions) = self.analysis.definitions.get(symbol) {
            for definition in definitions {
                let dependencies = and(&self.dependencies(definition));
                for attribute in &definition.attributes {
                    if let Attribute::Prompt(prompt) = attribute {
                        prompts.push(and(&[
                            dependencies.clone(),
                            self.condition(prompt.r#if.as_ref()),
                        ]));
                    }
                }
            }
        }
        or(&prompts)
    }

    fn symbol(&mut self, symbol: &str, definitions: &[Config]) -> Result<(), ()> {
        let Some(ty) = self
            .model
            .symbols()
            .get(symbol)
            .and_then(|info| info.kconfig_type.as_ref())
        else {
            return Ok(());
        };
        let mut defaults = Vec::new();
        let mut ranges = Vec::new();
        let mut selects = Vec::new();
        let mut implies = Vec::new();
        for definition in definitions {
            let dependencies = self.dependencies(definition);
            let scope = and(&dependencies);
            if self.args.is_enabled(Check::DuplicateDependency) {
                self.dependencies_check(symbol, definition, &dependencies)?;
            }
            for attribute in &definition.attributes {
                if self.args.is_enabled(Check::ConstantCondition) {
                    let (kind, condition) = match attribute {
                        Attribute::Default(default) => ("default", default.r#if.as_ref()),
                        Attribute::Range(range) => ("range", range.r#if.as_ref()),
                        Attribute::Select(select) => ("select", select.r#if.as_ref()),
                        Attribute::Imply(imply) => ("imply", imply.r#if.as_ref()),
                        _ => ("", None),
                    };
                    if let Some(condition) = condition {
                        self.constant_condition(symbol, kind, condition, &scope)?;
                    }
                }
                match attribute {
                    Attribute::Default(default)
                        if self.enabled(&[
                            Check::DuplicateDefault,
                            Check::DeadDefault,
                            Check::DuplicateDefaultValue,
                            Check::OutOfRangeDefault,
                        ]) =>
                    {
                        let value = match ty {
                            Type::Int(_) | Type::Hex(_) => Z3Types::Integer(model_int_value_expr(
                                self.model.symbols(),
                                ty.clone(),
                                default.expression.clone(),
                            )),
                            Type::String(_) => Z3Types::String(model_string_value_expr(
                                self.model.symbols(),
                                default.expression.clone(),
                            )),
                            _ => model_kconfig_or_expr(
                                self.model.symbols(),
                                ty.clone(),
                                default.expression.clone(),
                            ),
                        };
                        defaults.push(DefaultProperty {
                            text: default.to_string(),
                            value,
                            condition: and(&[scope.clone(), self.condition(default.r#if.as_ref())]),
                            conditional: default.r#if.is_some(),
                        });
                    }
                    Attribute::Range(range)
                        if self.enabled(&[
                            Check::DeadRange,
                            Check::DuplicateRange,
                            Check::OutOfRangeDefault,
                        ]) && matches!(ty, Type::Int(_) | Type::Hex(_)) =>
                    {
                        let is_hex = matches!(ty, Type::Hex(_));
                        ranges.push(RangeProperty {
                            text: range.to_string(),
                            lower: model_int_bound(
                                self.model.symbols(),
                                &range.lower_bound,
                                is_hex,
                            ),
                            upper: model_int_bound(
                                self.model.symbols(),
                                &range.upper_bound,
                                is_hex,
                            ),
                            guard: and(&[scope.clone(), self.condition(range.r#if.as_ref())])
                                .gt_n(),
                        });
                    }
                    Attribute::Select(select)
                        if self.enabled(&[
                            Check::DeadSelect,
                            Check::DuplicateSelect,
                            Check::SelectVisible,
                        ]) =>
                    {
                        selects.push(Edge {
                            target: select.symbol.clone(),
                            text: format!("select {select}"),
                            pull: self.edge_pull(
                                symbol,
                                &select.symbol,
                                &scope,
                                select.r#if.as_ref(),
                                false,
                            ),
                        });
                    }
                    Attribute::Imply(imply)
                        if self.enabled(&[Check::DeadImply, Check::DuplicateImply]) =>
                    {
                        let target = imply.symbol.to_string();
                        let pull =
                            self.edge_pull(symbol, &target, &scope, imply.r#if.as_ref(), true);
                        implies.push(Edge {
                            target,
                            text: format!("imply {imply}"),
                            pull,
                        });
                    }
                    _ => {}
                }
            }
        }
        self.defaults(symbol, &defaults)?;
        self.ranges(symbol, &ranges)?;
        self.out_of_range_defaults(symbol, &defaults, &ranges)?;
        self.edges(symbol, &selects, Check::DuplicateSelect, Check::DeadSelect)?;
        self.edges(symbol, &implies, Check::DuplicateImply, Check::DeadImply)?;
        if self.args.is_enabled(Check::SelectVisible) {
            for select in selects {
                if self.possible(
                    symbol,
                    Check::SelectVisible,
                    bool_and(&select.pull.gt_n(), &self.visibility(&select.target).gt_n()),
                )? {
                    self.report(symbol, Check::SelectVisible, format!(
                        "selects the visible {}; consider using 'depends on' or 'imply' instead", select.target
                    ));
                }
            }
        }
        Ok(())
    }

    fn dependencies_check(
        &mut self,
        symbol: &str,
        definition: &Config,
        dependencies: &[Ternary],
    ) -> Result<(), ()> {
        let expressions: Vec<_> = definition
            .attributes
            .iter()
            .filter_map(|attribute| match attribute {
                Attribute::DependsOn(dep) => Some(&dep.expression),
                _ => None,
            })
            .collect();
        let mut previous = Ternary::y();
        for (index, dependency) in dependencies.iter().enumerate() {
            // Do not assume the option is enabled or all its dependencies hold:
            // either assumption would make its own dependencies tautological.
            if index > 0
                && !self.possible(
                    symbol,
                    Check::DuplicateDependency,
                    lt(dependency, &previous),
                )?
            {
                self.report(
                    symbol,
                    Check::DuplicateDependency,
                    format!(
                        "duplicate dependency on {}; implied by earlier dependencies",
                        expressions[index]
                    ),
                );
            }
            previous = and(&[previous, dependency.clone()]);
        }
        Ok(())
    }

    fn constant_condition(
        &mut self,
        symbol: &str,
        kind: &str,
        expression: &Expression,
        scope: &Ternary,
    ) -> Result<(), ()> {
        let check = Check::ConstantCondition;
        if !self.possible(symbol, check, scope.gt_n())? {
            return Ok(()); // no vacuous "always true" in an unreachable definition
        }
        let condition = self.condition(Some(expression));
        for (name, value) in [
            ("n", Ternary::n()),
            ("m", Ternary::m()),
            ("y", Ternary::y()),
        ] {
            if !self.possible(
                symbol,
                check,
                bool_and(&scope.gt_n(), &eq(&condition, &value).not()),
            )? {
                self.report(symbol, check, format!(
                    "constant {kind} condition 'if {expression}': always {name} when dependencies are met"
                ));
                return Ok(());
            }
        }
        // Even a varying tristate condition can be redundant: min(dep, cond)
        // equals dep at both m and y. Do not collapse m and y to booleans here.
        if !self.possible(symbol, check, lt(&condition, scope))? {
            self.report(symbol, check, format!(
                "constant {kind} condition 'if {expression}': always satisfied by the dependencies"
            ));
        }
        Ok(())
    }

    fn defaults(&mut self, symbol: &str, defaults: &[DefaultProperty]) -> Result<(), ()> {
        if !self.enabled(&[
            Check::DeadDefault,
            Check::DuplicateDefault,
            Check::DuplicateDefaultValue,
        ]) {
            return Ok(());
        }
        let dead_defaults = self.args.is_enabled(Check::DeadDefault);
        let check = if dead_defaults {
            Check::DeadDefault
        } else if self.args.is_enabled(Check::DuplicateDefault) {
            Check::DuplicateDefault
        } else {
            Check::DuplicateDefaultValue
        };
        let mut previous = Bool::from_bool(false);
        for (index, default) in defaults.iter().enumerate() {
            if index == 0 && !dead_defaults {
                continue;
            }
            let hit = default.condition.gt_n();
            // Unreachable conditions cannot establish value equivalence.
            if self.model.is_choice_member(symbol) || !self.possible(symbol, check, hit.clone())? {
                self.report(
                    symbol,
                    Check::DeadDefault,
                    format!(
                        "dead default {}: can never be the active default",
                        default.text
                    ),
                );
                continue;
            }
            let mut duplicate = false;
            if self.enabled(&[Check::DuplicateDefault, Check::DeadDefault]) {
                for earlier in &defaults[..index] {
                    let same = bool_and(
                        &eq(&default.condition, &earlier.condition),
                        &hit.implies(values_equal(&default.value, &earlier.value)),
                    );
                    if !self.possible(symbol, Check::DuplicateDefault, same.not())? {
                        duplicate = true;
                        break;
                    }
                }
                if duplicate {
                    self.report(
                        symbol,
                        Check::DuplicateDefault,
                        format!("duplicate default {}", default.text),
                    );
                } else if dead_defaults {
                    let reachable = bool_and(&hit, &previous.not());
                    if !self.possible(symbol, Check::DeadDefault, reachable)? {
                        self.report(
                            symbol,
                            Check::DeadDefault,
                            format!(
                                "dead default {}: can never be the active default",
                                default.text
                            ),
                        );
                    }
                }
            }
            if self.args.is_enabled(Check::DuplicateDefaultValue) && default.conditional {
                for earlier in defaults[..index]
                    .iter()
                    .filter(|earlier| earlier.conditional)
                {
                    if !self.possible(
                        symbol,
                        Check::DuplicateDefaultValue,
                        earlier.condition.gt_n(),
                    )? {
                        continue;
                    }
                    let different = bool_and(
                        &bool_or(&hit, &earlier.condition.gt_n()),
                        &values_equal(&default.value, &earlier.value).not(),
                    );
                    if !self.possible(symbol, Check::DuplicateDefaultValue, different)? {
                        self.report(symbol, Check::DuplicateDefaultValue, format!(
                            "duplicate default value in {}; consider combining the conditions with a logical-or: ||", default.text
                        ));
                        break;
                    }
                }
            }
            if dead_defaults {
                previous = bool_or(&previous, &hit);
            }
        }
        Ok(())
    }

    fn ranges(&mut self, symbol: &str, ranges: &[RangeProperty]) -> Result<(), ()> {
        if !self.enabled(&[Check::DeadRange, Check::DuplicateRange]) {
            return Ok(());
        }
        let mut previous = Bool::from_bool(false);
        for (index, range) in ranges.iter().enumerate() {
            if !self.possible(symbol, Check::DeadRange, range.guard.clone())? {
                self.report(
                    symbol,
                    Check::DeadRange,
                    format!("dead range {}: can never be the active range", range.text),
                );
                continue;
            }
            let reachable = bool_and(&range.guard, &previous.not());
            let mut duplicate = false;
            if self.enabled(&[Check::DuplicateRange, Check::DeadRange]) {
                for earlier in &ranges[..index] {
                    let same_bounds = bool_and(
                        &range.lower.eq(&earlier.lower),
                        &range.upper.eq(&earlier.upper),
                    );
                    let same = bool_and(
                        &range.guard.eq(&earlier.guard),
                        &range.guard.implies(same_bounds),
                    );
                    if !self.possible(symbol, Check::DuplicateRange, same.not())? {
                        duplicate = true;
                        break;
                    }
                }
                if duplicate {
                    self.report(
                        symbol,
                        Check::DuplicateRange,
                        format!("duplicate range {}", range.text),
                    );
                } else if self.args.is_enabled(Check::DeadRange)
                    && !self.possible(symbol, Check::DeadRange, reachable.clone())?
                {
                    self.report(
                        symbol,
                        Check::DeadRange,
                        format!("dead range {}: can never be the active range", range.text),
                    );
                }
            }
            previous = bool_or(&previous, &range.guard);
        }
        Ok(())
    }

    fn out_of_range_defaults(
        &mut self,
        symbol: &str,
        defaults: &[DefaultProperty],
        ranges: &[RangeProperty],
    ) -> Result<(), ()> {
        let check = Check::OutOfRangeDefault;
        if !self.args.is_enabled(check) || defaults.is_empty() || ranges.is_empty() {
            return Ok(());
        }
        let mut previous_defaults = Bool::from_bool(false);
        for default in defaults {
            let hit = default.condition.gt_n();
            let active_default = bool_and(&hit, &previous_defaults.not());
            previous_defaults = bool_or(&previous_defaults, &hit);
            let Z3Types::Integer(value) = &default.value else {
                continue;
            };
            let mut previous_ranges = Bool::from_bool(false);
            for range in ranges {
                let active_range = bool_and(&range.guard, &previous_ranges.not());
                previous_ranges = bool_or(&previous_ranges, &range.guard);
                let outside = bool_or(&value.lt(&range.lower), &value.gt(&range.upper));
                let reachable = bool_and(&bool_and(&active_default, &active_range), &outside);
                if self.possible(symbol, check, reachable)? {
                    self.report(
                        symbol,
                        check,
                        format!(
                            "default {} can be outside active range {} before clamping",
                            default.text, range.text
                        ),
                    );
                }
            }
        }
        Ok(())
    }

    fn edge_pull(
        &self,
        source: &str,
        target: &str,
        scope: &Ternary,
        condition: Option<&Expression>,
        imply: bool,
    ) -> Ternary {
        let Some(Z3Types::Ternary(source)) = self
            .model
            .symbols()
            .get(source)
            .and_then(|info| info.z3_type.as_ref())
        else {
            return Ternary::n();
        };
        let Some(target_info) = self.model.symbols().get(target) else {
            return Ternary::n();
        };
        if !matches!(target_info.z3_type, Some(Z3Types::Ternary(_)))
            || self.model.is_choice_member(target)
        {
            return Ternary::n();
        }
        let mut pull = and(&[source.clone(), scope.clone(), self.condition(condition)]);
        if imply {
            pull = and(&[
                pull,
                definition_dependencies(self.model.symbols(), target_info),
            ]);
        }
        if matches!(
            target_info.kconfig_type,
            Some(Type::Bool(_) | Type::DefBool(_))
        ) {
            pull = z3_ternary::clamp(&pull, &Bool::from_bool(true));
        }
        pull
    }

    fn edges(
        &mut self,
        symbol: &str,
        edges: &[Edge],
        duplicate_check: Check,
        dead_check: Check,
    ) -> Result<(), ()> {
        if !self.enabled(&[duplicate_check, dead_check]) {
            return Ok(());
        }
        let mut redundant = vec![false; edges.len()];
        for (index, edge) in edges.iter().enumerate() {
            if !self.possible(symbol, dead_check, edge.pull.gt_n())? {
                self.report(
                    symbol,
                    dead_check,
                    format!("dead {}: can never take effect", edge.text),
                );
                redundant[index] = true;
                continue;
            }
            let mut others = Vec::new();
            let mut duplicate = false;
            for (other_index, other) in edges.iter().enumerate() {
                if index == other_index || redundant[other_index] || edge.target != other.target {
                    continue;
                }
                let equal =
                    !self.possible(symbol, duplicate_check, eq(&edge.pull, &other.pull).not())?;
                if equal && other_index < index {
                    duplicate = true;
                    break;
                }
                // Keep the earliest equivalent edge. Selects/implies combine
                // by max(), unlike ordered defaults/ranges. A later stronger
                // edge can therefore make an earlier edge redundant.
                if !equal {
                    others.push(other.pull.clone());
                }
            }
            if duplicate {
                self.report(symbol, duplicate_check, format!("duplicate {}", edge.text));
                redundant[index] = true;
            } else if !others.is_empty()
                && !self.possible(symbol, dead_check, le(&edge.pull, &or(&others)).not())?
            {
                self.report(
                    symbol,
                    dead_check,
                    format!(
                        "dead {}: covered by other attributes for {}",
                        edge.text, edge.target
                    ),
                );
                redundant[index] = true;
            }
        }
        Ok(())
    }
}

fn values_equal(left: &Z3Types, right: &Z3Types) -> Bool {
    match (left, right) {
        (Z3Types::Ternary(left), Z3Types::Ternary(right)) => eq(left, right),
        (Z3Types::Integer(left), Z3Types::Integer(right)) => left.eq(right),
        (Z3Types::String(left), Z3Types::String(right)) => left.eq(right),
        _ => Bool::from_bool(false),
    }
}

#[cfg(test)]
mod tests;
