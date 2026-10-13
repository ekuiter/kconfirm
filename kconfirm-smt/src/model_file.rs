//! Reusable SMT-LIB exports.

use crate::{TypeInfo, Z3Types};
use nom_kconfig::attribute::r#type::Type;
use std::{collections::BTreeMap, ffi::CStr, fmt::Write};
use z3::{
    Solver,
    ast::{Int, String as Z3String},
};

const HEADER: &str = "; kconfirm-smt-model 1\n";
const BODY: &str = "; kconfirm-smt-constraints\n";
const END: &str = "; end-kconfirm-smt-model\n";

pub(crate) fn export(
    solver: &Solver,
    symbols: &BTreeMap<String, TypeInfo>,
) -> Result<String, String> {
    #[cfg(feature = "debug")]
    let export_solver = {
        use z3::{DeclKind, ast::Ast};
        let exported = Solver::new();
        for assertion in solver.get_assertions() {
            if assertion.decl().kind() != DeclKind::Implies {
                return Err("expected a tracked base-model assertion".into());
            }
            let tracker = assertion
                .nth_child(0)
                .and_then(|a| a.as_bool())
                .ok_or("expected a Boolean tracking literal")?;
            exported.assert(&assertion);
            exported.assert(tracker);
        }
        exported
    };
    #[cfg(feature = "debug")]
    let solver = &export_solver;

    let mut out = HEADER.to_owned();
    for (name, info) in symbols {
        let kind = match info.kconfig_type.as_ref() {
            Some(Type::Bool(_) | Type::DefBool(_)) => "bool",
            Some(Type::Tristate(_) | Type::DefTristate(_)) => "tristate",
            Some(Type::Int(_)) => "int",
            Some(Type::Hex(_)) => "hex",
            Some(Type::String(_)) => "string",
            _ => return Err(format!("cannot export the Kconfig type of {name}")),
        };
        writeln!(out, "; symbol {kind} {name}").unwrap();
    }
    writeln!(out, "; assertions {}", solver.get_assertions().len()).unwrap();
    out.push_str(BODY);
    out.push_str(&solver.to_string());
    out.push('\n');
    out.push_str(END);
    Ok(out)
}

pub(crate) fn load(text: &str) -> Result<(Solver, BTreeMap<String, TypeInfo>), String> {
    if text.contains('\0') {
        return Err("model file contains a NUL byte".into());
    }
    let text = text.strip_prefix(HEADER).ok_or(
        "missing or unsupported symbol metadata; regenerate the file with --output-smt-lib",
    )?;
    let (metadata, body) = text
        .split_once(BODY)
        .ok_or("missing SMT constraints section")?;
    let body = body
        .strip_suffix(END)
        .ok_or("incomplete model file (missing end marker)")?;
    let mut symbols = BTreeMap::new();
    let mut assertion_count = None;
    for line in metadata.lines() {
        let fields: Vec<_> = line.split_whitespace().collect();
        match fields.as_slice() {
            [";", "symbol", kind, name] => {
                let (kconfig_type, z3_type) = match *kind {
                    "bool" => (
                        Type::Bool(None),
                        Z3Types::Ternary(z3_ternary::new_bool(name)),
                    ),
                    "tristate" => (
                        Type::Tristate(None),
                        Z3Types::Ternary(z3_ternary::new_tristate(name).0),
                    ),
                    "int" => (Type::Int(None), Z3Types::Integer(Int::new_const(*name))),
                    "hex" => (Type::Hex(None), Z3Types::Integer(Int::new_const(*name))),
                    "string" => (
                        Type::String(None),
                        Z3Types::String(Z3String::new_const(*name)),
                    ),
                    _ => return Err(format!("unknown Kconfig type {kind}")),
                };
                let info = TypeInfo {
                    kconfig_type: Some(kconfig_type),
                    z3_type: Some(z3_type),
                    ..Default::default()
                };
                if symbols.insert((*name).to_owned(), info).is_some() {
                    return Err(format!("duplicate symbol metadata for {name}"));
                }
            }
            [";", "assertions", count] if assertion_count.is_none() => {
                assertion_count = Some(
                    count
                        .parse::<usize>()
                        .map_err(|_| "invalid assertion count")?,
                );
            }
            _ => return Err(format!("invalid model metadata: {line}")),
        }
    }
    let expected = assertion_count.ok_or("missing assertion count")?;
    let solver = Solver::new();
    let context = solver.get_context().get_z3_context();
    solver.from_string(body);
    unsafe {
        let code = z3_sys::Z3_get_error_code(context);
        if code != z3_sys::ErrorCode::Ok {
            let error = CStr::from_ptr(z3_sys::Z3_get_error_msg(context, code));
            return Err(format!("invalid SMT-LIB: {}", error.to_string_lossy()));
        }
    }
    let actual = solver.get_assertions().len();
    if actual != expected {
        return Err(format!(
            "incomplete model: expected {expected} assertions, loaded {actual}"
        ));
    }
    Ok((solver, symbols))
}
