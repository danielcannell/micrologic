use std::ops::Range;

use ariadne::{Label as AriadneLabel, Report, ReportKind, Source};

/// A byte range into the source text. This is the single source-location
/// currency used throughout the compiler (lexer, parser, AST, and core).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    /// The span covering from the start of `self` to the end of `other`.
    pub fn to(self, other: Span) -> Span {
        Span {
            start: self.start,
            end: other.end,
        }
    }
}

impl From<Span> for Range<usize> {
    fn from(span: Span) -> Self {
        span.start..span.end
    }
}

/// A single annotated source location within a [`Diagnostic`].
#[derive(Debug, Clone)]
pub struct Label {
    pub span: Span,
    /// Text shown next to the underline. `None` underlines without comment.
    pub message: Option<String>,
}

/// A source-free description of a compile error. It carries everything needed
/// to render a nice report, but not the source text itself: `main` supplies
/// that at print time via [`Diagnostic::emit`]. This keeps the `ariadne`
/// dependency confined to this module, so the parser and (later) the core
/// type-checker can build diagnostics without knowing how they are rendered.
#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub message: String,
    /// Annotated locations, primary first.
    pub labels: Vec<Label>,
    pub notes: Vec<String>,
}

impl Diagnostic {
    /// A diagnostic whose primary location is `span`. `message` is the headline: it says what is
    /// wrong. Use [`Diagnostic::with_primary_label`] to say what is wrong *here*.
    pub fn error(message: impl Into<String>, span: Span) -> Self {
        Diagnostic {
            message: message.into(),
            labels: vec![Label {
                span,
                message: None,
            }],
            notes: Vec::new(),
        }
    }

    /// Set the text shown at the primary location.
    pub fn with_primary_label(mut self, message: impl Into<String>) -> Self {
        self.labels[0].message = Some(message.into());
        self
    }

    /// Attach an additional annotated location.
    pub fn with_label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.labels.push(Label {
            span,
            message: Some(message.into()),
        });
        self
    }

    /// Attach a note shown beneath the labelled source.
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Render this diagnostic against `source`, read from the file `filename`, and print it to
    /// stderr.
    pub fn emit(&self, filename: &str, source: &str) {
        let primary = self
            .labels
            .first()
            .map(|label| Range::from(label.span))
            .unwrap_or(0..0);

        let mut builder =
            Report::build(ReportKind::Error, (filename, primary)).with_message(&self.message);

        for label in &self.labels {
            let mut ariadne_label = AriadneLabel::new((filename, Range::from(label.span)));
            if let Some(message) = &label.message {
                ariadne_label = ariadne_label.with_message(message);
            }
            builder = builder.with_label(ariadne_label);
        }
        for note in &self.notes {
            builder = builder.with_note(note);
        }

        // Printing to stderr should not itself fail; if it does there is
        // nothing useful to recover to.
        builder
            .finish()
            .eprint((filename, Source::from(source)))
            .expect("failed to write diagnostic");
    }
}

/// Convenience alias for fallible compiler passes.
pub type Result<T> = std::result::Result<T, Diagnostic>;
