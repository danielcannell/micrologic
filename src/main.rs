pub mod diagnostics;
pub mod kernel;
pub mod surface;
mod lower;

use std::path::PathBuf;

use clap::Parser;

#[derive(Parser)]
struct Args {
    /// Source file to check
    source_file: PathBuf,
}

fn main() {
    let args = Args::parse();

    let source = std::fs::read_to_string(&args.source_file).expect("Could not read source file");

    let module = match surface::parse(&source) {
        Ok(module) => module,
        Err(diag) => {
            diag.emit(&source);
            std::process::exit(1);
        }
    };

    let mut ctx = kernel::Context::new();
    let mut proved = 0usize;
    let mut admitted = 0usize;
    let mut failed = 0usize;

    for item in &module.items {
        match item {
            surface::ast::Item::Axiom(axiom) => {
                let typ = lower::lower_type(&axiom.typ);
                println!("axiom {} : {}", axiom.name.text, typ);
                ctx = ctx.bind(axiom.name.text.clone(), typ);
            }
            surface::ast::Item::Theorem(theorem) => {
                let typ = lower::lower_type(&theorem.typ);
                let body = lower::lower_term(&theorem.body);

                let trust = match kernel::check(&ctx, &body, typ.clone()) {
                    Ok(kernel::Trust::Proved) => {
                        proved += 1;
                        println!("ok {} : {}", theorem.name.text, typ);
                        kernel::Trust::Proved
                    }
                    Ok(kernel::Trust::Admitted) => {
                        admitted += 1;
                        println!("admitted {} : {}", theorem.name.text, typ);
                        kernel::Trust::Admitted
                    }
                    Err(err) => {
                        failed += 1;
                        println!("failed {} : {}", theorem.name.text, err);
                        kernel::Trust::Admitted
                    }
                };

                ctx = ctx.bind_with_trust(theorem.name.text.clone(), typ, trust);
            }
        }
    }

    println!("\n{proved} proved, {admitted} admitted, {failed} failed");

    if failed > 0 {
        std::process::exit(1);
    }
}
