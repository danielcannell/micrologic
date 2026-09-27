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
    // Every item's name, what kind of item it is, and where it was defined.
    let mut bound: HashMap<String, (&str, Span)> = HashMap::new();

    // TODO: Print error if we bail early; print skipped for skipped things

    for item in &module.items {
        let (kind, name) = match item {
            surface::ast::Item::Axiom(axiom) => ("axiom", &axiom.name),
            surface::ast::Item::Theorem(theorem) => ("theorem", &theorem.name),
            surface::ast::Item::Proposition(proposition) => ("proposition", &proposition.name),
        };

        if let Some((prev_kind, prev_span)) = bound.insert(name.text.clone(), (kind, name.span)) {
            let mut diag = Diagnostic::error(
                format!("`{}` is defined more than once", name.text),
                name.span,
            )
            .with_primary_label("redefined here")
            .with_label(prev_span, "first defined here");
            if prev_kind != kind {
                diag = diag.with_note(format!(
                    "`{}` was first defined as {} {prev_kind}; theorems, axioms and propositions \
                     share one set of names",
                    name.text,
                    if prev_kind == "axiom" { "an" } else { "a" },
                ));
            }
            diagnostics.push(diag);

            continue;
        }

        match item {
            surface::ast::Item::Axiom(axiom) => {
                let scope = TypeScope {
                    parameters: &axiom.parameters,
                    aliases: &aliases,
                    defining: None,
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
                    defining: None,
                };
                let parameters = try_!(lower::lower_type_parameters(&theorem.parameters));
                let typ = try_!(lower::lower_type(&theorem.typ, &scope));
                let scheme = kernel::Scheme::new(parameters, typ.clone());

                let trust = match lower::lower_term(&theorem.body, &scope) {
                    Ok(body) => match kernel::check(&ctx, &body, &scheme, theorem.typ.span()) {
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
                            diagnostics.push(err);
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
                    defining: Some(&proposition.name.text),
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

    let filename = args.source_file.display().to_string();
    for diagnostic in &summary.diagnostics {
        diagnostic.emit(&filename, &source);
    }

    std::process::exit(if summary.failed == 0 && summary.diagnostics.is_empty() {
        0
    } else {
        1
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    fn messages(summary: &Summary) -> Vec<&str> {
        summary
            .diagnostics
            .iter()
            .map(|diag| diag.message.as_str())
            .collect()
    }

    fn assert_all_proved(source: &str) {
        let summary = process_module(source);
        assert_eq!(messages(&summary), Vec::<&str>::new());
        assert_eq!((summary.admitted, summary.failed), (0, 0));
        assert!(summary.proved > 0);
    }

    #[test]
    fn test_examples() {
        assert_all_proved(include_str!("../examples/example.ml"));
        assert_all_proved(include_str!("../examples/knights_and_knaves.ml"));
    }

    #[test]
    fn test_polymorphic_theorem_reuse() {
        assert_all_proved(
            r#"
            theorem swap A B : A and B -> B and A :=
                fun (p : A and B) => (snd p, fst p).
            theorem swap_back A B : B and A -> A and B :=
                swap [B] [A].
            theorem swap_twice A B : A and B -> A and B :=
                fun (p : A and B) => swap [B] [A] (swap [A] [B] p).
            "#,
        );
    }

    #[test]
    fn test_alias_is_transparent() {
        // `Knave A` and `not A` are interchangeable in both directions.
        assert_all_proved(
            r#"
            proposition Knave A := not A.
            theorem into A : not A -> Knave A := fun (x : not A) => x.
            theorem out_of A : Knave A -> not A := fun (x : Knave A) => x.
            theorem apply A : Knave A -> A -> False := fun (x : Knave A) => fun (a : A) => x a.
            "#,
        );
    }

    #[test]
    fn test_non_theorems_are_rejected() {
        // Plausible-looking "proofs" of things that aren't intuitionistic theorems.
        let attempts = [
            "theorem bad A B : A -> B := fun (x : A) => x.",
            "theorem bad A : A := absurd [A] (fun (f : False) => f).",
            "theorem bad A : not not A -> A := fun (h : not not A) => absurd [A] h.",
            "theorem bad A B : A or B -> A := fun (h : A or B) => case h of | inl x => x | inr y => y.",
            "theorem bad A B : (A -> B) -> B -> A := fun (f : A -> B) => fun (b : B) => f b.",
            "theorem id A : A -> A := fun (x : A) => x.\ntheorem bad : False := id [False].",
        ];
        for source in attempts {
            let summary = process_module(source);
            assert_eq!(summary.failed, 1, "should reject:\n{source}");
            assert_eq!(summary.diagnostics.len(), 1);
        }
    }

    #[test]
    fn test_free_atom_cannot_be_captured() {
        // If `ax : A` were accepted with a free `A`, `bad` would generalise over it and
        // `bad [False]` would prove False. The axiom is rejected, and checking stops there.
        let summary = process_module(
            r#"
            axiom ax : A.
            theorem bad A : A := ax.
            theorem boom : False := bad [False].
            "#,
        );
        assert_eq!(messages(&summary), vec!["cannot find proposition `A`"]);
        assert_eq!(
            (summary.proved, summary.admitted, summary.failed),
            (0, 0, 0)
        );
    }

    #[test]
    fn test_admitted_taints_transitively() {
        let summary = process_module(
            r#"
            theorem hole A : A -> A := trustme [A -> A].
            theorem user A : A -> A := hole [A].
            theorem user_of_user A : A -> A := user [A].
            theorem independent A : A -> A := fun (x : A) => x.
            "#,
        );
        assert_eq!(messages(&summary), Vec::<&str>::new());
        assert_eq!(
            (summary.proved, summary.admitted, summary.failed),
            (1, 3, 0)
        );
    }

    #[test]
    fn test_failed_theorem_is_bound_as_admitted() {
        // Later references resolve (no "cannot find" cascade) but are never reported proved.
        let summary = process_module(
            r#"
            theorem broken A : A -> A := fun (x : A) => fst x.
            theorem unlowerable A : A -> A := fun (x : B) => x.
            theorem user1 A : A -> A := broken [A].
            theorem user2 A : A -> A := unlowerable [A].
            "#,
        );
        assert_eq!(
            messages(&summary),
            vec![
                "`fst` expects a proof of a conjunction",
                "cannot find proposition `B`",
            ]
        );
        assert_eq!(
            (summary.proved, summary.admitted, summary.failed),
            (0, 2, 2)
        );
    }

    #[test]
    fn test_signature_error_stops_checking() {
        let summary = process_module(
            r#"
            theorem before A : A -> A := fun (x : A) => x.
            theorem bad A : B := trustme [B].
            theorem after A : A -> A := fun (x : A) => x.
            "#,
        );
        assert_eq!(messages(&summary), vec!["cannot find proposition `B`"]);
        assert_eq!(
            (summary.proved, summary.admitted, summary.failed),
            (1, 0, 0)
        );
    }

    #[test]
    fn test_redefinition() {
        let source = r#"
            proposition Knave A := not A.
            proposition Knave A := A.
        "#;
        let summary = process_module(source);
        assert_eq!(
            messages(&summary),
            vec!["`Knave` is defined more than once"]
        );
        let labels = &summary.diagnostics[0].labels;
        assert_eq!(labels[0].span.start, source.rfind("Knave").unwrap());
        assert_eq!(labels[1].span.start, source.find("Knave").unwrap());

        // Theorems, axioms and propositions share one namespace for redefinition.
        for source in [
            "theorem t A : A -> A := fun (x : A) => x.\ntheorem t A : A -> A := fun (x : A) => x.",
            "axiom t A : A.\ntheorem t A : A -> A := fun (x : A) => x.",
            "proposition t A := A.\naxiom t A : A.",
        ] {
            let summary = process_module(source);
            assert_eq!(
                messages(&summary),
                vec!["`t` is defined more than once"],
                "in:\n{source}"
            );
        }
    }

    #[test]
    fn test_parse_error() {
        let summary = process_module("theorem t : A := .");
        assert_eq!(summary.diagnostics.len(), 1);
        assert_eq!(
            (summary.proved, summary.admitted, summary.failed),
            (0, 0, 0)
        );
    }

    // Each label of the first diagnostic, as (source text under it, label message).
    fn labels(source: &str) -> Vec<(String, String)> {
        let summary = process_module(source);
        let diag = summary.diagnostics.first().expect("expected a diagnostic");
        diag.labels
            .iter()
            .map(|label| {
                (
                    source[label.span.start..label.span.end].to_string(),
                    label.message.clone().unwrap_or_default(),
                )
            })
            .collect()
    }

    fn pair(text: &str, message: &str) -> (String, String) {
        (text.to_string(), message.to_string())
    }

    #[test]
    fn test_mismatch_is_reported_at_innermost_sub_term() {
        let statement = pair("A -> B", "expected because of this statement");
        assert_eq!(
            labels("theorem t A B : A -> B := fun (x : A) => x."),
            vec![pair("x", "this has type `A`"), statement.clone()]
        );
        assert_eq!(
            labels("theorem t A B : A -> B := fun (x : B) => x."),
            vec![
                pair(
                    "fun (x : B) => x",
                    "`x` is declared as `B`, but `A` is expected"
                ),
                statement,
            ]
        );
        assert_eq!(
            labels("theorem t A B : A and B -> B and A := fun (p : A and B) => (fst p, snd p)."),
            vec![
                pair("fst p", "this has type `A`"),
                pair("A and B -> B and A", "expected because of this statement"),
            ]
        );
        assert_eq!(
            labels(
                "theorem t A B : A or B -> A := fun (h : A or B) => case h of | inl x => x | inr y => y."
            ),
            vec![
                pair("y", "this has type `B`"),
                pair("A or B -> A", "expected because of this statement"),
            ]
        );
    }

    #[test]
    fn test_errors_unrelated_to_the_statement_do_not_point_at_it() {
        assert_eq!(
            labels("theorem t A B : (A -> B) -> B -> B := fun (f : A -> B) => fun (b : B) => f b."),
            vec![
                pair("b", "this has type `B`"),
                pair("f", "this has type `A -> B`"),
            ]
        );
        assert_eq!(
            labels("theorem t A : A -> A := fun (x : A) => y."),
            vec![pair("y", "not a hypothesis, theorem or axiom")]
        );
    }

    #[test]
    fn test_messages_use_surface_syntax() {
        let summary = process_module(
            "proposition Knave A := not A.\ntheorem t A : Knave A <-> True := trustme [A].",
        );
        assert_eq!(
            messages(&summary),
            vec!["mismatched types: expected `not A <-> True`, found `A`"]
        );
    }

    #[test]
    fn test_type_arity_note() {
        let summary = process_module(
            "theorem swap A B : A and B -> B and A := fun (p : A and B) => (snd p, fst p).\n\
             theorem t A B : A and B -> B and A := swap.",
        );
        assert_eq!(
            messages(&summary),
            vec!["`swap` takes 2 type arguments but 0 were supplied"]
        );
        assert_eq!(
            summary.diagnostics[0].notes,
            vec!["`swap` has type parameters `A`, `B`; supply one type for each: `swap [A] [B]`"]
        );
    }
}
