pub mod diagnostics;
pub mod kernel;
pub mod lower;
pub mod surface;
pub mod tactic;

use std::collections::HashMap;
use std::path::PathBuf;

use crate::diagnostics::{Diagnostic, Result, Span};
use crate::lower::TypeScope;
use clap::Parser;

#[derive(Debug, Eq, PartialEq)]
struct Summary {
    proved: u64,
    admitted: u64,
}

struct BoundItem {
    // Kind of item: "axiom", "theorem" or "proposition"
    kind: &'static str,

    // Span for the identifier of the original definition
    span: Span,
}

fn process_module(source: &str) -> Result<Summary> {
    let mut proved = 0u64;
    let mut admitted = 0u64;

    let module = surface::parse(source)?;

    let mut ctx = kernel::Context::new();
    let mut aliases: HashMap<String, kernel::Scheme> = HashMap::new();
    // Every item's name, what kind of item it is, and where it was defined.
    let mut bound: HashMap<String, BoundItem> = HashMap::new();

    for item in &module.items {
        let (kind, name) = match item {
            surface::ast::Item::Axiom(axiom) => ("axiom", &axiom.name),
            surface::ast::Item::Theorem(theorem) => ("theorem", &theorem.name),
            surface::ast::Item::Proposition(proposition) => ("proposition", &proposition.name),
        };

        let bound_item = BoundItem {
            kind,
            span: name.span,
        };

        if let Some(prev_bound_item) = bound.insert(name.text.clone(), bound_item) {
            let mut diag = Diagnostic::error(
                format!("`{}` is defined more than once", name.text),
                name.span,
            )
            .with_primary_label("redefined here")
            .with_label(prev_bound_item.span, "first defined here");
            if prev_bound_item.kind != kind {
                diag = diag.with_note(format!(
                    "`{}` was first defined as {} {}; theorems, axioms and propositions \
                     share one set of names",
                    name.text,
                    if prev_bound_item.kind == "axiom" {
                        "an"
                    } else {
                        "a"
                    },
                    prev_bound_item.kind,
                ));
            }

            return Err(diag);
        }

        match item {
            surface::ast::Item::Axiom(axiom) => {
                let scope = TypeScope {
                    parameters: &axiom.parameters,
                    aliases: &aliases,
                    defining: None,
                };
                let parameters = lower::lower_type_parameters(&axiom.parameters)?;
                let typ = lower::lower_type(&axiom.typ, &scope)?;
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
                let parameters = lower::lower_type_parameters(&theorem.parameters)?;
                let typ = lower::lower_type(&theorem.typ, &scope)?;
                let scheme = kernel::Scheme::new(parameters, typ.clone());

                let body = match &theorem.body {
                    surface::ast::Body::Term(body) => lower::lower_term(body, &scope)?,
                    surface::ast::Body::Script(script) => {
                        tactic::elaborate(&ctx, &lower::lower_script(script, &scope)?, &typ)?
                    }
                };

                let trust = match kernel::check(&ctx, &body, &scheme, theorem.typ.span())? {
                    kernel::Trust::Proved => {
                        proved += 1;
                        println!("ok {}", theorem.name.text);
                        kernel::Trust::Proved
                    }
                    kernel::Trust::Admitted => {
                        admitted += 1;
                        println!("admitted {}", theorem.name.text);
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
                let parameters = lower::lower_type_parameters(&proposition.parameters)?;
                let typ = lower::lower_type(&proposition.typ, &scope)?;
                let scheme = kernel::Scheme::new(parameters, typ.clone());

                println!("proposition {}", proposition.name.text);

                // Note that the alias body is lowered *before* the alias is added to the map, and
                // aliases are expanded eagerly when the body is lowered. This make alias recursion
                // impossible, keeping the logic consistent.
                aliases.insert(proposition.name.text.clone(), scheme);
            }
        }
    }

    Ok(Summary { proved, admitted })
}

#[derive(Parser)]
struct Args {
    /// Source file to check
    source_file: PathBuf,
}

fn main() {
    let args = Args::parse();

    let source = std::fs::read_to_string(&args.source_file).expect("Could not read source file");

    match process_module(&source) {
        Ok(summary) => {
            println!("\n{} proved, {} admitted", summary.proved, summary.admitted);
        }
        Err(diagnostic) => {
            let filename = args.source_file.display().to_string();
            diagnostic.emit(&filename, &source);
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Check a module that should be accepted, returning its summary.
    fn accept(source: &str) -> Summary {
        match process_module(source) {
            Ok(summary) => summary,
            Err(diag) => panic!("should accept, but got `{}`:\n{source}", diag.message),
        }
    }

    // Check a module that should be rejected, returning the (first and only) diagnostic.
    fn reject(source: &str) -> Diagnostic {
        match process_module(source) {
            Ok(summary) => panic!("should reject, but got {summary:?}:\n{source}"),
            Err(diag) => diag,
        }
    }

    fn assert_all_proved(source: &str) {
        let summary = accept(source);
        assert!(summary.proved > 0);
        assert_eq!(summary.admitted, 0);
    }

    #[test]
    fn test_examples() {
        assert_all_proved(include_str!("../examples/example.ml"));
        assert_all_proved(include_str!("../examples/knights_and_knaves.ml"));
        assert_all_proved(include_str!("../examples/tactics.ml"));
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
        // Plausible-looking "proofs" of things that aren't intuitionistic theorems. The message is
        // pinned so that an unrelated error (e.g. a typo in the source) can't make a test pass.
        let attempts = [
            (
                "theorem bad A B : A -> B := fun (x : A) => x.",
                "mismatched types: expected `B`, found `A`",
            ),
            (
                "theorem bad A : A := absurd [A] (fun (f : False) => f).",
                "`absurd` expects a proof of `False`",
            ),
            (
                "theorem bad A : not not A -> A := fun (h : not not A) => absurd [A] h.",
                "`absurd` expects a proof of `False`",
            ),
            (
                "theorem bad A B : A or B -> A := fun (h : A or B) => case h of | inl x => x | inr y => y.",
                "mismatched types: expected `A`, found `B`",
            ),
            (
                "theorem bad A B : (A -> B) -> B -> A := fun (f : A -> B) => fun (b : B) => f b.",
                "mismatched argument: expected `A`, found `B`",
            ),
            (
                "theorem id A : A -> A := fun (x : A) => x.\ntheorem bad : False := id [False].",
                "mismatched types: expected `False`, found `True`",
            ),
        ];
        for (source, message) in attempts {
            assert_eq!(reject(source).message, message, "in:\n{source}");
        }
    }

    #[test]
    fn test_free_atom_cannot_be_captured() {
        // If `ax : A` were accepted with a free `A`, `bad` would generalise over it and
        // `bad [False]` would prove False. The axiom is rejected, and checking stops there.
        let diag = reject(
            r#"
            axiom ax : A.
            theorem bad A : A := ax.
            theorem boom : False := bad [False].
            "#,
        );
        assert_eq!(diag.message, "cannot find proposition `A`");
    }

    #[test]
    fn test_admitted_taints_transitively() {
        let summary = accept(
            r#"
            theorem hole A : A -> A := trustme [A -> A].
            theorem user A : A -> A := hole [A].
            theorem user_of_user A : A -> A := user [A].
            theorem independent A : A -> A := fun (x : A) => x.
            "#,
        );
        assert_eq!(
            summary,
            Summary {
                proved: 1,
                admitted: 3
            }
        );
    }

    #[test]
    fn test_first_error_stops_checking() {
        // Only the first error is reported, whether it is in a body (kernel or lowering) or a
        // signature. Later items are never checked, so an error in them is never reached.
        let later_errors = r#"
            theorem after A : A -> A := fun (x : B) => x.
            theorem after2 A : A -> A := fun (x : A) => fst x.
        "#;
        let first_errors = [
            (
                "theorem broken A : A -> A := fun (x : A) => fst x.",
                "`fst` expects a proof of a conjunction",
            ),
            (
                "theorem unlowerable A : A -> A := fun (x : C) => x.",
                "cannot find proposition `C`",
            ),
            (
                "theorem bad A : C := trustme [C].",
                "cannot find proposition `C`",
            ),
            ("axiom bad A : C.", "cannot find proposition `C`"),
            ("proposition Bad A := C.", "cannot find proposition `C`"),
        ];
        for (first, message) in first_errors {
            let source =
                format!("theorem before A : A -> A := fun (x : A) => x.\n{first}\n{later_errors}");
            assert_eq!(reject(&source).message, message, "in:\n{source}");
        }
    }

    #[test]
    fn test_redefinition() {
        let source = r#"
            proposition Knave A := not A.
            proposition Knave A := A.
        "#;
        let diag = reject(source);
        assert_eq!(diag.message, "`Knave` is defined more than once");
        assert_eq!(diag.labels[0].span.start, source.rfind("Knave").unwrap());
        assert_eq!(diag.labels[1].span.start, source.find("Knave").unwrap());

        // Theorems, axioms and propositions share one namespace for redefinition.
        for source in [
            "theorem t A : A -> A := fun (x : A) => x.\ntheorem t A : A -> A := fun (x : A) => x.",
            "axiom t A : A.\ntheorem t A : A -> A := fun (x : A) => x.",
            "proposition t A := A.\naxiom t A : A.",
        ] {
            assert_eq!(
                reject(source).message,
                "`t` is defined more than once",
                "in:\n{source}"
            );
        }

        // Checking stops at the redefinition: the later error is never reached.
        let diag =
            reject("axiom t A : A.\naxiom t A : A.\ntheorem u A : A -> A := fun (x : B) => x.");
        assert_eq!(diag.message, "`t` is defined more than once");
    }

    #[test]
    fn test_parse_error() {
        // A parse error stops everything, even items before it are not checked.
        let diag = reject("theorem ok A : A -> A := fun (x : A) => x.\ntheorem t : A := .");
        assert_eq!(diag.message, "expected a term, found `.`");
    }

    // Each label of the diagnostic, as (source text under it, label message).
    fn labels(source: &str) -> Vec<(String, String)> {
        reject(source)
            .labels
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
    fn test_mismatch_inside_an_injection() {
        // The expected type is pushed through `inl`/`inr`, so the error points at the wrong
        // sub-term, not the whole injection.
        let statement = pair("A or not A", "expected because of this statement");
        assert_eq!(
            labels("theorem t A : A or not A := inr [A] (fun (a : A) => a)."),
            vec![pair("a", "this has type `A`"), statement.clone()]
        );
        let source = "theorem t A : A or not A := by right; intro a; exact a.";
        assert_eq!(
            labels(source),
            vec![pair("a", "this has type `A`"), statement]
        );
        assert_eq!(
            reject(source).labels[0].span.start,
            source.find("exact a").unwrap() + "exact ".len()
        );

        // A wrong annotation is reported at the injection.
        assert_eq!(
            labels("theorem t A B : A -> A or B := fun (a : A) => inl [A] a."),
            vec![
                pair(
                    "inl [A] a",
                    "the right side is annotated as `A`, but `B` is expected"
                ),
                pair("A -> A or B", "expected because of this statement"),
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
        let diag =
            reject("proposition Knave A := not A.\ntheorem t A : Knave A <-> True := trustme [A].");
        assert_eq!(
            diag.message,
            "mismatched types: expected `not A <-> True`, found `A`"
        );
    }

    #[test]
    fn test_type_arity_note() {
        let diag = reject(
            "theorem swap A B : A and B -> B and A := fun (p : A and B) => (snd p, fst p).\n\
             theorem t A B : A and B -> B and A := swap.",
        );
        assert_eq!(
            diag.message,
            "`swap` takes 2 type arguments but 0 were supplied"
        );
        assert_eq!(
            diag.notes,
            vec!["`swap` has type parameters `A`, `B`; supply one type for each: `swap [A] [B]`"]
        );
    }

    #[test]
    fn test_tactic_proofs_and_term_proofs_mix() {
        // Tactic proofs can use term proofs via `exact`, and vice versa.
        assert_all_proved(
            r#"
            theorem swap A B : A and B -> B and A := fun (p : A and B) => (snd p, fst p).
            theorem swap_tactic A B : A and B -> B and A := by intro p; exact swap [A] [B] p.
            theorem pair_tactic A B : A -> B -> A and B := by
                intro a; intro b; split; exact a; exact b.
            theorem pair_swapped A B : A -> B -> B and A :=
                fun (a : A) => fun (b : B) => swap_tactic [A] [B] (pair_tactic [A] [B] a b).
            "#,
        );
    }

    #[test]
    fn test_wrong_exact_is_rejected_by_the_kernel() {
        // The elaborator doesn't check `exact` terms; the kernel does, and labels the mistake
        // inside the term rather than at the tactic.
        let source =
            "theorem t A B : A -> B -> B and A := by intro a; intro b; split; exact a; exact b.";
        let diag = reject(source);
        assert_eq!(diag.message, "mismatched types: expected `B`, found `A`");
        assert_eq!(
            labels(source),
            vec![
                pair("a", "this has type `A`"),
                pair("A -> B -> B and A", "expected because of this statement"),
            ]
        );
        assert_eq!(
            diag.labels[0].span.start,
            source.find("exact a").unwrap() + "exact ".len()
        );
    }

    #[test]
    fn test_non_theorems_are_rejected_with_tactics() {
        // Whether the elaborator or the kernel catches it, a tactic script can't prove a
        // non-theorem.
        let attempts = [
            (
                "theorem bad A B : A -> B := by intro a; exact a.",
                "mismatched types: expected `B`, found `A`",
            ),
            (
                "theorem bad A B : A -> B := by intro a; assumption.",
                "no hypothesis matches the goal",
            ),
            (
                "theorem bad A : not not A -> A := by intro h; exact h.",
                "mismatched types: expected `A`, found `not not A`",
            ),
            (
                "theorem bad A : A or not A := by left; assumption.",
                "no hypothesis matches the goal",
            ),
            (
                "theorem bad A : A or not A := by right; intro a; exact a.",
                "mismatched types: expected `False`, found `A`",
            ),
            (
                "theorem bad A B : A -> B := by intro a; exfalso; exact a.",
                "`absurd` expects a proof of `False`",
            ),
            (
                "theorem bad A B : A or B -> A := by intro h; destruct h as a b; exact a.",
                "`destruct` needs a hypothesis of the form `A and B`",
            ),
            (
                "theorem bad A : A or not A := by have h : A; { assumption }; { left; exact h }.",
                "no hypothesis matches the goal",
            ),
            (
                "theorem bad A B : A or B -> A := by intro h; cases h as a b; { exact a }; { exact b }.",
                "mismatched types: expected `A`, found `B`",
            ),
            // The second `h` hides the first, so `exact h` refers to `h : B`.
            (
                "theorem bad A B : A -> B -> A := by intro h; intro h; exact h.",
                "mismatched types: expected `A`, found `B`",
            ),
        ];
        for (source, message) in attempts {
            assert_eq!(reject(source).message, message, "in:\n{source}");
        }
    }

    #[test]
    fn test_admit() {
        // An admitted theorem is accepted (so the exit code is 0), but not counted as proved.
        assert_eq!(
            accept("theorem t A B : A -> B := by intro a; admit."),
            Summary {
                proved: 0,
                admitted: 1
            }
        );
    }

    #[test]
    fn test_admit_taints_transitively() {
        // Taint flows through `exact` in tactic proofs and into term proofs.
        let summary = accept(
            r#"
            theorem hole A B : A -> B := by intro a; admit.
            theorem user A B : A -> B := by exact hole [A] [B].
            theorem term_user A B : A -> B := fun (a : A) => user [A] [B] a.
            theorem independent A : A -> A := by intro a; exact a.
            "#,
        );
        assert_eq!(
            summary,
            Summary {
                proved: 1,
                admitted: 3
            }
        );
    }
}
