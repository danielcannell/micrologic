pub mod diagnostics;
pub mod kernel;
mod lower;
pub mod surface;

use std::path::PathBuf;

use crate::diagnostics::Diagnostic;
use clap::Parser;

fn process_module(source: &str) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    macro_rules! try_ {
        ($e:expr) => {
            match $e {
                Ok(val) => val,
                Err(err) => {
                    diagnostics.push(err);
                    return diagnostics;
                }
            }
        };
    }

    let module = try_!(surface::parse(source));

    let mut ctx = kernel::Context::new();
    let mut proved = 0usize;
    let mut admitted = 0usize;
    let mut failed = 0usize;

    for item in &module.items {
        match item {
            surface::ast::Item::Axiom(axiom) => {
                let parameters = try_!(lower::lower_type_parameters(&axiom.parameters));
                let typ = try_!(lower::lower_type(&axiom.typ, &axiom.parameters));
                let scheme = kernel::Scheme::new(parameters, typ.clone());

                let mut name_and_params = vec![axiom.name.text.clone()];
                name_and_params.extend(axiom.parameters.iter().map(|ident| &ident.text).cloned());
                println!("axiom {}", name_and_params.join(" "));

                ctx = ctx.bind(axiom.name.text.clone(), scheme);
            }
            surface::ast::Item::Theorem(theorem) => {
                let parameters = try_!(lower::lower_type_parameters(&theorem.parameters));
                let typ = try_!(lower::lower_type(&theorem.typ, &theorem.parameters));
                let scheme = kernel::Scheme::new(parameters, typ.clone());

                let body = match lower::lower_term(&theorem.body, &theorem.parameters) {
                    Ok(body) => body,
                    Err(diag) => {
                        println!("error {}", theorem.name.text);
                        diagnostics.push(diag);
                        continue;
                    }
                };

                let trust = match kernel::check(&ctx, &body, &scheme) {
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
                        diagnostics.push(Diagnostic::error(err, theorem.name.span)); // TODO: Proper diagnostics from kernel
                        kernel::Trust::Admitted
                    }
                };

                ctx = ctx.bind_with_trust(theorem.name.text.clone(), scheme, trust);
            }
        }
    }

    println!("\n{proved} proved, {admitted} admitted, {failed} failed");

    diagnostics
}

#[derive(Parser)]
struct Args {
    /// Source file to check
    source_file: PathBuf,
}

fn main() {
    let args = Args::parse();

    let source = std::fs::read_to_string(&args.source_file).expect("Could not read source file");

    let diagnostics = process_module(&source);
    let ok = diagnostics.is_empty();

    for diagnostic in diagnostics {
        diagnostic.emit(&source);
    }

    std::process::exit(if ok { 0 } else { 1 });
}
