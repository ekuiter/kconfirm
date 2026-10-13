// SPDX-License-Identifier: GPL-2.0-only
//! Unreachable intervals within declared int/hex ranges.

use std::collections::BTreeMap;

use kconfirm_lib::{Check, Finding, Severity};
use kconfirm_smt::{SmtModel, TypeInfo, Z3Types, model_condition, model_int_bound};
use log::info;
use nom_kconfig::attribute::{range::RangeBound, r#type::Type};
use z3::{
    Model, SatResult, Solver,
    ast::{Bool as z3_bool, Int as z3_int},
};
use z3_ternary::Ternary;

pub(super) fn check(model: &SmtModel) -> Vec<Finding> {
    let mut findings = Vec::new();
    let mut checked = 0;
    let mut undecided = 0;
    info!("Checking ranged int/hex options for unreachable subranges");
    for (symbol, type_info) in model.symbols() {
        let Some(check) = build_dead_subrange_check(model.symbols(), symbol, type_info) else {
            continue;
        };
        checked += 1;
        match analyze_dead_subrange(model.solver(), &check) {
            DeadSubrangeResult::Complete => {}
            DeadSubrangeResult::Dead(intervals) => {
                for interval in intervals {
                    let lower = format_numeric_bound(interval.lower, check.is_hex);
                    let upper = format_numeric_bound(interval.upper, check.is_hex);
                    findings.push(Finding {
                        severity: Severity::Warning,
                        check: Check::DeadSubrange,
                        symbol: Some(symbol.clone()),
                        arch: None,
                        message: format!("cannot reach declared values {lower}..{upper}"),
                    });
                }
            }
            DeadSubrangeResult::Unknown(reason) => {
                undecided += 1;
                findings.push(Finding {
                    severity: Severity::Fatal,
                    check: Check::FailedModel,
                    symbol: Some(symbol.clone()),
                    arch: None,
                    message: format!("dead_subrange check inconclusive: {reason}"),
                });
            }
        }
    }
    info!("dead_subrange: checked {checked} ranged options; {undecided} inconclusive");
    findings
}

fn range_bound_is_modeled(symbol_table: &BTreeMap<String, TypeInfo>, bound: &RangeBound) -> bool {
    match bound {
        RangeBound::Number(_) | RangeBound::Hex(_) => true,
        RangeBound::Symbol(symbol) => matches!(
            symbol_table
                .get(symbol)
                .and_then(|type_info| type_info.z3_type.as_ref()),
            Some(Z3Types::Integer(_))
        ),
        RangeBound::Variable(_) => false,
    }
}

fn build_dead_subrange_check(
    symbol_table: &BTreeMap<String, TypeInfo>,
    symbol: &str,
    type_info: &TypeInfo,
) -> Option<DeadSubrangeCheck> {
    let is_hex = matches!(type_info.kconfig_type, Some(Type::Hex(_)));
    if !matches!(
        type_info.kconfig_type,
        Some(Type::Int(_)) | Some(Type::Hex(_))
    ) {
        return None;
    }

    let value: z3_int = type_info
        .z3_type
        .clone()
        .expect("already converted all Kconfig types to z3")
        .try_into()
        .expect("int/hex options are modeled as z3 integers");
    let mut dependencies: Option<Ternary> = None;
    let mut prompt: Option<Ternary> = None;
    let mut ranges: Vec<(z3_int, z3_int, Ternary, bool)> = Vec::new();
    if let Some(attributes) = &type_info.definition {
        dependencies = Some(match &attributes.kconfig_dependencies {
            None => Ternary::y(),
            Some(deps) => model_condition(symbol_table, deps.clone()),
        });
        prompt = Some(match &attributes.visibility {
            None => Ternary::n(),
            Some(vis) => model_condition(symbol_table, vis.clone()),
        });
        for range in &attributes.kconfig_ranges {
            let lower = model_int_bound(symbol_table, &range.lower_bound, is_hex);
            let upper = model_int_bound(symbol_table, &range.upper_bound, is_hex);
            let condition = match &range.r#if {
                None => Ternary::y(),
                Some(cond) => model_condition(symbol_table, cond.clone()),
            };
            ranges.push((
                lower,
                upper,
                condition,
                range_bound_is_modeled(symbol_table, &range.lower_bound)
                    && range_bound_is_modeled(symbol_table, &range.upper_bound),
            ));
        }
    }
    if ranges.is_empty() {
        return None;
    }

    let dependencies = dependencies.unwrap_or_else(Ternary::y);
    let prompt = prompt.unwrap_or_else(Ternary::n);
    let visible = z3_ternary::bool_and(&prompt.gt_n(), &dependencies.gt_n());

    let mut any_range_hit = z3_bool::from_bool(false);
    let mut declared_ranges = Vec::with_capacity(ranges.len());
    let mut has_unmodeled_bound = false;
    let mut free_ranges = Vec::with_capacity(ranges.len());
    for (lower, upper, condition, bounds_modeled) in ranges {
        let hit = condition.gt_n();
        let effective = z3_ternary::bool_and(&hit, &any_range_hit.not());
        any_range_hit = z3_ternary::bool_or(&any_range_hit, &hit);

        let interval = match (z3_integer_value(&lower), z3_integer_value(&upper)) {
            (Some(lower), Some(upper)) => Some(NumericInterval { lower, upper }),
            _ => None,
        };
        has_unmodeled_bound |= !bounds_modeled;
        declared_ranges.push(RangeIntervalContext {
            guard: z3_bool::from_bool(true),
            lower: lower.clone(),
            upper: upper.clone(),
            interval,
        });
        free_ranges.push(RangeIntervalContext {
            guard: z3_ternary::bool_and(&visible, &effective),
            lower,
            upper,
            interval,
        });
    }

    Some(DeadSubrangeCheck {
        symbol: symbol.to_string(),
        value,
        is_hex,
        declared_ranges,
        has_unmodeled_bound,
        unrestricted_guard: z3_ternary::bool_and(&visible, &any_range_hit.not()),
        free_ranges,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NumericInterval {
    lower: i128,
    upper: i128,
}

/// One possible numeric interval.
struct RangeIntervalContext {
    guard: z3_bool,
    lower: z3_int,
    upper: z3_int,
    interval: Option<NumericInterval>,
}

/// A ranged int/hex option whose declared domain is checked for unreachable
/// contiguous intervals.
struct DeadSubrangeCheck {
    symbol: String,
    value: z3_int,
    is_hex: bool,
    declared_ranges: Vec<RangeIntervalContext>,
    has_unmodeled_bound: bool,
    unrestricted_guard: z3_bool,
    free_ranges: Vec<RangeIntervalContext>,
}

enum DeadSubrangeResult {
    Complete,
    Dead(Vec<NumericInterval>),
    Unknown(String),
}

fn z3_integer_value(value: &z3_int) -> Option<i128> {
    value
        .as_i64()
        .map(i128::from)
        .or_else(|| value.as_u64().map(i128::from))
}

fn z3_integer_literal(value: i128) -> z3_int {
    if let Ok(signed) = i64::try_from(value) {
        z3_int::from_i64(signed)
    } else {
        z3_int::from_u64(u64::try_from(value).expect("Kconfig numerals fit in u64"))
    }
}

fn normalize_intervals(mut intervals: Vec<NumericInterval>) -> Vec<NumericInterval> {
    intervals.retain(|interval| interval.lower <= interval.upper);
    intervals.sort_by_key(|interval| (interval.lower, interval.upper));
    let mut merged: Vec<NumericInterval> = Vec::with_capacity(intervals.len());
    for interval in intervals {
        if let Some(previous) = merged.last_mut()
            && interval.lower <= previous.upper + 1
        {
            previous.upper = previous.upper.max(interval.upper);
        } else {
            merged.push(interval);
        }
    }
    merged
}

fn interval_membership(value: &z3_int, interval: NumericInterval) -> z3_bool {
    z3_ternary::bool_and(
        &z3_integer_literal(interval.lower).le(value),
        &value.le(z3_integer_literal(interval.upper)),
    )
}

fn model_numeric_interval(
    model: &Model,
    lower: &z3_int,
    upper: &z3_int,
) -> Option<NumericInterval> {
    let lower = model
        .eval(lower, true)
        .as_ref()
        .and_then(z3_integer_value)?;
    let upper = model
        .eval(upper, true)
        .as_ref()
        .and_then(z3_integer_value)?;
    (lower <= upper).then_some(NumericInterval { lower, upper })
}

fn reportable_range_bounds(context: &RangeIntervalContext) -> (z3_int, z3_int) {
    // Kconfig `int` literals use i64 and `hex` literals use u64 in this model.
    let minimum = z3_integer_literal(i128::from(i64::MIN));
    let maximum = z3_integer_literal(i128::from(u64::MAX));
    let lower = context.lower.ge(&minimum).ite(&context.lower, &minimum);
    let upper = context.upper.le(&maximum).ite(&context.upper, &maximum);
    (lower, upper)
}

enum RangeIntervalQuery {
    Sat(NumericInterval),
    Unsat,
    Unknown,
}

fn query_interval_containing(
    solver: &Solver,
    context: &RangeIntervalContext,
    reportable_lower: &z3_int,
    reportable_upper: &z3_int,
    point: i128,
    endpoint_constraint: z3_bool,
) -> RangeIntervalQuery {
    let point = z3_integer_literal(point);
    let query = z3_ternary::bool_and_all(&[
        context.guard.clone(),
        context.lower.le(&point),
        point.le(&context.upper),
        endpoint_constraint,
    ]);
    match solver.check_assumptions(std::slice::from_ref(&query)) {
        SatResult::Sat => solver
            .get_model()
            .as_ref()
            .and_then(|model| model_numeric_interval(model, reportable_lower, reportable_upper))
            .map_or(RangeIntervalQuery::Unknown, RangeIntervalQuery::Sat),
        SatResult::Unsat => RangeIntervalQuery::Unsat,
        SatResult::Unknown => RangeIntervalQuery::Unknown,
    }
}

/// Add intervals that extend from `point` to the largest reachable upper bound.
fn widen_symbolic_upper(
    solver: &Solver,
    context: &RangeIntervalContext,
    reportable_lower: &z3_int,
    reportable_upper: &z3_int,
    point: i128,
    initial: NumericInterval,
    intervals: &mut Vec<NumericInterval>,
) {
    let limit = i128::from(u64::MAX);
    let mut current = initial.upper;
    let mut step = (current - point).max(0) + 1;
    let mut first_infeasible = None;

    for _ in 0..128 {
        if current == limit {
            return;
        }
        let threshold = current.saturating_add(step).min(limit);
        match query_interval_containing(
            solver,
            context,
            reportable_lower,
            reportable_upper,
            point,
            reportable_upper.ge(z3_integer_literal(threshold)),
        ) {
            RangeIntervalQuery::Sat(interval) if interval.upper > current => {
                current = interval.upper;
                intervals.push(interval);
                step = step.saturating_mul(2);
            }
            RangeIntervalQuery::Sat(_) | RangeIntervalQuery::Unknown => return,
            RangeIntervalQuery::Unsat => {
                first_infeasible = Some(threshold);
                break;
            }
        }
    }

    let Some(first_infeasible) = first_infeasible else {
        return;
    };
    let mut low = current + 1;
    let mut high = first_infeasible - 1;
    while low <= high {
        let threshold = low + (high - low) / 2;
        match query_interval_containing(
            solver,
            context,
            reportable_lower,
            reportable_upper,
            point,
            reportable_upper.ge(z3_integer_literal(threshold)),
        ) {
            RangeIntervalQuery::Sat(interval) => {
                current = interval.upper;
                intervals.push(interval);
                low = current + 1;
            }
            RangeIntervalQuery::Unsat => high = threshold - 1,
            RangeIntervalQuery::Unknown => return,
        }
    }
}

/// Add intervals that extend from `point` to the smallest reachable lower
/// bound. This is the lower-bound version of `widen_symbolic_upper`.
fn widen_symbolic_lower(
    solver: &Solver,
    context: &RangeIntervalContext,
    reportable_lower: &z3_int,
    reportable_upper: &z3_int,
    point: i128,
    initial: NumericInterval,
    intervals: &mut Vec<NumericInterval>,
) {
    let limit = i128::from(i64::MIN);
    let mut current = initial.lower;
    let mut step = (point - current).max(0) + 1;
    let mut first_infeasible = None;

    for _ in 0..128 {
        if current == limit {
            return;
        }
        let threshold = current.saturating_sub(step).max(limit);
        match query_interval_containing(
            solver,
            context,
            reportable_lower,
            reportable_upper,
            point,
            reportable_lower.le(z3_integer_literal(threshold)),
        ) {
            RangeIntervalQuery::Sat(interval) if interval.lower < current => {
                current = interval.lower;
                intervals.push(interval);
                step = step.saturating_mul(2);
            }
            RangeIntervalQuery::Sat(_) | RangeIntervalQuery::Unknown => return,
            RangeIntervalQuery::Unsat => {
                first_infeasible = Some(threshold);
                break;
            }
        }
    }

    let Some(first_infeasible) = first_infeasible else {
        return;
    };
    let mut low = first_infeasible + 1;
    let mut high = current - 1;
    while low <= high {
        let threshold = low + (high - low) / 2;
        match query_interval_containing(
            solver,
            context,
            reportable_lower,
            reportable_upper,
            point,
            reportable_lower.le(z3_integer_literal(threshold)),
        ) {
            RangeIntervalQuery::Sat(interval) => {
                current = interval.lower;
                intervals.push(interval);
                high = current - 1;
            }
            RangeIntervalQuery::Unsat => low = threshold + 1,
            RangeIntervalQuery::Unknown => return,
        }
    }
}

fn widen_symbolic_interval(
    solver: &Solver,
    context: &RangeIntervalContext,
    reportable_lower: &z3_int,
    reportable_upper: &z3_int,
    point: i128,
    initial: NumericInterval,
    intervals: &mut Vec<NumericInterval>,
) {
    widen_symbolic_upper(
        solver,
        context,
        reportable_lower,
        reportable_upper,
        point,
        initial,
        intervals,
    );
    widen_symbolic_lower(
        solver,
        context,
        reportable_lower,
        reportable_upper,
        point,
        initial,
        intervals,
    );
}

fn collect_range_projection(
    solver: &Solver,
    context: &RangeIntervalContext,
    intervals: &mut Vec<NumericInterval>,
    probe_name: &str,
    description: &str,
    symbolic_models: &mut usize,
) -> Result<(), String> {
    if let Some(interval) = context.interval {
        if interval.lower > interval.upper {
            return Ok(());
        }
        if context.guard.as_bool() == Some(true) {
            intervals.push(interval);
            *intervals = normalize_intervals(std::mem::take(intervals));
            return Ok(());
        }
        return match solver.check_assumptions(std::slice::from_ref(&context.guard)) {
            SatResult::Sat => {
                intervals.push(interval);
                *intervals = normalize_intervals(std::mem::take(intervals));
                Ok(())
            }
            SatResult::Unsat => Ok(()),
            SatResult::Unknown => Err(format!(
                "solver could not decide whether the {description} range is reachable"
            )),
        };
    }

    const MAX_SYMBOLIC_INTERVAL_MODELS: usize = 4096;
    let probe = z3_int::fresh_const(probe_name);
    let (reportable_lower, reportable_upper) = reportable_range_bounds(context);
    loop {
        let outside_known = z3_ternary::bool_and_all(
            &intervals
                .iter()
                .map(|interval| interval_membership(&probe, *interval).not())
                .collect::<Vec<_>>(),
        );
        let query = z3_ternary::bool_and_all(&[
            context.guard.clone(),
            reportable_lower.le(&probe),
            probe.le(&reportable_upper),
            outside_known,
        ]);
        match solver.check_assumptions(std::slice::from_ref(&query)) {
            SatResult::Unsat => return Ok(()),
            SatResult::Unknown => {
                return Err(format!(
                    "solver could not project the {description} symbolic range"
                ));
            }
            SatResult::Sat => {
                if *symbolic_models == MAX_SYMBOLIC_INTERVAL_MODELS {
                    return Err(format!(
                        "more than {MAX_SYMBOLIC_INTERVAL_MODELS} SMT interval models are required for symbolic ranges"
                    ));
                }
                *symbolic_models += 1;
                let model = solver
                    .get_model()
                    .expect("a satisfiable range projection has a model");
                let Some(point) = model.eval(&probe, true).as_ref().and_then(z3_integer_value)
                else {
                    return Err("solver returned a non-numeral range point".to_string());
                };
                let Some(interval) =
                    model_numeric_interval(&model, &reportable_lower, &reportable_upper)
                else {
                    return Err("solver returned non-numeral symbolic bounds".to_string());
                };
                intervals.push(interval);
                widen_symbolic_interval(
                    solver,
                    context,
                    &reportable_lower,
                    &reportable_upper,
                    point,
                    interval,
                    intervals,
                );
                *intervals = normalize_intervals(std::mem::take(intervals));
            }
        }
    }
}

fn dead_parts(declared: &[NumericInterval], reachable: &[NumericInterval]) -> Vec<NumericInterval> {
    let mut dead = Vec::new();
    for declared_interval in declared {
        let mut cursor = declared_interval.lower;
        for reachable_interval in reachable {
            if reachable_interval.upper < cursor {
                continue;
            }
            if reachable_interval.lower > declared_interval.upper {
                break;
            }
            if reachable_interval.lower > cursor {
                dead.push(NumericInterval {
                    lower: cursor,
                    upper: declared_interval.upper.min(reachable_interval.lower - 1),
                });
            }
            cursor = cursor.max(reachable_interval.upper + 1);
            if cursor > declared_interval.upper {
                break;
            }
        }
        if cursor <= declared_interval.upper {
            dead.push(NumericInterval {
                lower: cursor,
                upper: declared_interval.upper,
            });
        }
    }
    normalize_intervals(dead)
}

/// Prove whole intervals dead with one query. Bisect satisfiable intervals
/// until reaching individual live values. Adjacent dead pieces are merged.
fn subdivide_dead_intervals(
    solver: &Solver,
    value: &z3_int,
    intervals: Vec<NumericInterval>,
) -> Result<Vec<NumericInterval>, String> {
    let mut pending = intervals;
    let mut dead = Vec::new();
    while let Some(interval) = pending.pop() {
        let query = interval_membership(value, interval);
        match solver.check_assumptions(std::slice::from_ref(&query)) {
            SatResult::Unsat => dead.push(interval),
            SatResult::Sat if interval.lower < interval.upper => {
                // i128 keeps the midpoint safe across the full i64/u64 domain.
                let midpoint = interval.lower + (interval.upper - interval.lower) / 2;
                pending.push(NumericInterval {
                    lower: midpoint + 1,
                    upper: interval.upper,
                });
                pending.push(NumericInterval {
                    lower: interval.lower,
                    upper: midpoint,
                });
            }
            SatResult::Sat => {}
            SatResult::Unknown => {
                return Err(format!(
                    "solver could not decide reachability of {}..{} during binary subdivision",
                    interval.lower, interval.upper
                ));
            }
        }
    }
    Ok(normalize_intervals(dead))
}

fn analyze_dead_subrange(solver: &Solver, check: &DeadSubrangeCheck) -> DeadSubrangeResult {
    match solver.check_assumptions(std::slice::from_ref(&check.unrestricted_guard)) {
        SatResult::Sat => return DeadSubrangeResult::Complete,
        SatResult::Unknown => {
            return DeadSubrangeResult::Unknown(
                "solver could not decide whether an unrestricted visible context exists"
                    .to_string(),
            );
        }
        SatResult::Unsat => {}
    }

    if check.has_unmodeled_bound {
        return DeadSubrangeResult::Unknown(
            "at least one range bound is an unresolved macro or is not numeric".to_string(),
        );
    }

    let mut symbolic_models = 0usize;

    let mut declared = Vec::new();
    for (index, context) in check.declared_ranges.iter().enumerate() {
        if let Err(reason) = collect_range_projection(
            solver,
            context,
            &mut declared,
            &format!(
                "dead_subrange_probe:{}:declared:{}",
                check.symbol,
                index + 1
            ),
            "declared",
            &mut symbolic_models,
        ) {
            return DeadSubrangeResult::Unknown(reason);
        }
    }
    let declared = normalize_intervals(declared);
    if declared.is_empty() {
        return DeadSubrangeResult::Complete;
    }

    let mut reachable = Vec::new();
    for (index, context) in check.free_ranges.iter().enumerate() {
        if let Err(reason) = collect_range_projection(
            solver,
            context,
            &mut reachable,
            &format!("dead_subrange_probe:{}:free:{}", check.symbol, index + 1),
            "visible",
            &mut symbolic_models,
        ) {
            return DeadSubrangeResult::Unknown(reason);
        }
    }
    reachable = normalize_intervals(reachable);

    match subdivide_dead_intervals(solver, &check.value, dead_parts(&declared, &reachable)) {
        Ok(dead) if dead.is_empty() => DeadSubrangeResult::Complete,
        Ok(dead) => DeadSubrangeResult::Dead(dead),
        Err(reason) => DeadSubrangeResult::Unknown(reason),
    }
}

fn format_numeric_bound(value: i128, is_hex: bool) -> String {
    if !is_hex {
        return value.to_string();
    }
    if value < 0 {
        format!("-0x{:x}", value.unsigned_abs())
    } else {
        format!("0x{value:x}")
    }
}

#[cfg(test)]
mod tests;
