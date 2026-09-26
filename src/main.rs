pub mod diagnostics;
pub mod kernel;
mod lower;
pub mod surface;

use std::collections::HashMap;
use std::path::PathBuf;

use crate::diagnostics::{Diagnostic, Span};
use crate::lower::TypeScope;
use clap::Parser;

struct Summary {
    diagnostics: Vec<Diagnostic>,
    proved: u64,
    admitted: u64,
    failed: u64,
}

fn process_module(source: &str) -> Summary {
    let mut diagnostics = Vec::new();
    let mut proved = 0u64;
    let mut admitted = 0u64;
    let mut failed = 0u64;

    macro_rules! try_ {
        ($e:expr) => {
            match $e {
                Ok(val) => val,
                Err(err) => {
                    diagnostics.push(err);
                    return Summary {
                        diagnostics,
                        proved,
                        admitted,
                        failed,
                    };
                }
            }
        };
    }

    let module = try_!(surface::parse(source));

    let mut ctx = kernel::Context::new();
    let mut aliases: HashMap<String, kernel::Scheme> = HashMap::new();
    let mut bound: HashMap<String, Span> = HashMap::new();

    // TODO: Print error if we bail early; print skipped for skipped things

    for item in &module.items {
        let name = match item {
            surface::ast::Item::Axiom(axiom) => axiom.name.clone(),
            surface::ast::Item::Theorem(theorem) => theorem.name.clone(),
            surface::ast::Item::Proposition(proposition) => proposition.name.clone(),
        };

        if let Some(prev_span) = bound.insert(name.text.clone(), name.span) {
            diagnostics.push(
                Diagnostic::error(format!("redefinition of {}", name.text), name.span)
                    .with_label(prev_span, "previous definition was here"),
            );

            continue;
        }

        match item {
            surface::ast::Item::Axiom(axiom) => {
                let scope = TypeScope {
                    parameters: &axiom.parameters,
                    aliases: &aliases,
                };
                let parameters = try_!(lower::lower_type_parameters(&axiom.parameters));
                let typ = try_!(lower::lower_type(&axiom.typ, &scope));
                let scheme = kernel::Scheme::new(parameters, typ.clone());

                println!("axiom {}", axiom.name.text);

                ctx = ctx.bind(axiom.name.text.clone(), scheme);
            }
            surface::ast::Item::Theorem(theorem) => {
                let scope = TypeScope {
                    parameters: &theorem.parameters,
                    aliases: &aliases,
                };
                let parameters = try_!(lower::lower_type_parameters(&theorem.parameters));
                let typ = try_!(lower::lower_type(&theorem.typ, &scope));
                let scheme = kernel::Scheme::new(parameters, typ.clone());

                let trust = match lower::lower_term(&theorem.body, &scope) {
                    Ok(body) => match kernel::check(&ctx, &body, &scheme) {
                        Ok(kernel::Trust::Proved) => {
                            proved += 1;
                            println!("ok {}", theorem.name.text);
                            kernel::Trust::Proved
                        }
                        Ok(kernel::Trust::Admitted) => {
                            admitted += 1;
                            println!("admitted {}", theorem.name.text);
                            kernel::Trust::Admitted
                        }
                        Err(err) => {
                            failed += 1;
                            println!("failed {}", theorem.name.text);
                            diagnostics.push(Diagnostic::error(err, theorem.name.span));
                            kernel::Trust::Admitted
                        }
                    },
                    Err(diag) => {
                        failed += 1;
                        println!("error {}", theorem.name.text);
                        diagnostics.push(diag);
                        kernel::Trust::Admitted
                    }
                };

                ctx = ctx.bind_with_trust(theorem.name.text.clone(), scheme, trust);
            }
            surface::ast::Item::Proposition(proposition) => {
                let scope = TypeScope {
                    parameters: &proposition.parameters,
                    aliases: &aliases,
                };
                let parameters = try_!(lower::lower_type_parameters(&proposition.parameters));
                let typ = try_!(lower::lower_type(&proposition.typ, &scope));
                let scheme = kernel::Scheme::new(parameters, typ.clone());

                println!("proposition {}", proposition.name.text);

                // For now, allow redefinition of aliases
                //
                // Note that the alias body is lowered *before* the alias is added to the map, and
                // aliases are expanded eagerly when the body is lowered. This make alias recursion
                // impossible, keeping the logic consistent.
                aliases.insert(proposition.name.text.clone(), scheme);
            }
        }
    }

    Summary {
        diagnostics,
        proved,
        admitted,
        failed,
    }
}

#[derive(Parser)]
struct Args {
    /// Source file to check
    source_file: PathBuf,
}

fn main() {
    let args = Args::parse();

    let source = std::fs::read_to_string(&args.source_file).expect("Could not read source file");

    let summary = process_module(&source);

    println!(
        "\n{} proved, {} admitted, {} failed",
        summary.proved, summary.admitted, summary.failed
    );

    for diagnostic in &summary.diagnostics {
        diagnostic.emit(&source);
    }

    std::process::exit(if summary.failed == 0 && summary.diagnostics.is_empty() {
        0
    } else {
        1
    });
}
