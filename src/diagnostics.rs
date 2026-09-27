use std::ops::Range;

use ariadne::{Config, IndexType, Label as AriadneLabel, Report, ReportKind, Source};

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
        eprint!("{}", self.render(filename, source, true));
    }

    /// Render this diagnostic against `source`, read from the file `filename`, as a string.
    /// `color` adds ANSI escape codes.
    pub fn render(&self, filename: &str, source: &str, color: bool) -> String {
        let primary = self
            .labels
            .first()
            .map(|label| Range::from(label.span))
            .unwrap_or(0..0);

        let config = Config::default()
            .with_index_type(IndexType::Byte)
            .with_color(color);

        let mut builder = Report::build(ReportKind::Error, (filename, primary))
            .with_config(config)
            .with_message(&self.message);

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

        let mut out = Vec::new();
        builder
            .finish()
            .write((filename, Source::from(source)), &mut out)
            .expect("writing to a Vec cannot fail");
        String::from_utf8(out).expect("ariadne output is UTF-8")
    }
}

/// Convenience alias for fallible compiler passes.
pub type Result<T> = std::result::Result<T, Diagnostic>;

#[cfg(test)]
mod tests {
    use super::*;

    fn span_of(source: &str, needle: &str) -> Span {
        let start = source.find(needle).expect("needle should be in source");
        Span {
            start,
            end: start + needle.len(),
        }
    }

    // Render an error labelled at the first occurrence of `needle`, then return the report
    // header (`file:line:column`) and the (column, width) of the underline, both in characters.
    fn render_at(source: &str, needle: &str) -> (String, (usize, usize)) {
        let rendered = Diagnostic::error("oops", span_of(source, needle))
            .with_primary_label("here")
            .render("test.ml", source, false);
        let lines: Vec<&str> = rendered.lines().collect();

        let header = lines
            .iter()
            .find_map(|line| {
                let start = line.find("test.ml:")?;
                let end = line[start..].find(' ')? + start;
                Some(line[start..end].to_string())
            })
            .expect("report should have a header");

        // The underline is on the line after the labelled source line. Measure both in chars,
        // relative to the `│` gutter, which is at the same column on both lines.
        let source_line = lines
            .iter()
            .position(|line| line.contains(needle))
            .expect("report should quote the labelled line");
        let gutter = |line: &str| line.chars().position(|c| c == '│').unwrap();
        let text_start = gutter(lines[source_line]);
        let underline: Vec<char> = lines[source_line + 1].chars().collect();
        let column = underline
            .iter()
            .position(|c| matches!(c, '─' | '┬'))
            .expect("report should underline the label");
        let width = underline[column..]
            .iter()
            .take_while(|c| matches!(c, '─' | '┬'))
            .count();

        let needle_column = lines[source_line].chars().count()
            - lines[source_line][lines[source_line].find(needle).unwrap()..]
                .chars()
                .count();
        assert_eq!(
            column - gutter(lines[source_line + 1]),
            needle_column - text_start,
            "underline should start under `{needle}`:\n{rendered}"
        );
        (header, (column - gutter(lines[source_line + 1]), width))
    }

    #[test]
    fn test_ascii_source() {
        let (header, (_, width)) = render_at("-- comment\nprop A := A.", "prop");
        assert_eq!(header, "test.ml:2:1");
        assert_eq!(width, 4);
    }

    #[test]
    fn test_multi_byte_character_on_earlier_line() {
        // `”` is 3 bytes but 1 character. With character offsets, the label would land 2 columns
        // too far right (`2:3`, under `op A`).
        let (header, (_, width)) = render_at("-- ”\nprop A := A.", "prop");
        assert_eq!(header, "test.ml:2:1");
        assert_eq!(width, 4);
    }

    #[test]
    fn test_multi_byte_character_earlier_on_same_line() {
        let (header, (_, width)) = render_at("theorem t α : β := x.", "β");
        assert_eq!(header, "test.ml:1:15");
        assert_eq!(width, 1);
    }

    #[test]
    fn test_span_covering_multi_byte_characters() {
        // `αβγ` is 6 bytes but 3 characters wide.
        let (header, (_, width)) = render_at("theorem t : αβγ := x.", "αβγ");
        assert_eq!(header, "test.ml:1:13");
        assert_eq!(width, 3);
    }
}
