use oxc_allocator::{Box, Vec};
use oxc_diagnostics::{OxcDiagnostic, Result};
use oxc_span::Atom as SpanAtom;

use crate::{ast, body_parser::unicode};

impl<'a> super::parse::PatternParser<'a> {
    // ```
    // PatternCharacter ::
    //   SourceCharacter but not SyntaxCharacter
    // ```
    // <https://tc39.es/ecma262/#prod-PatternCharacter>
    pub(super) fn consume_pattern_character(&mut self) -> Option<ast::Atom<'a>> {
        let span_start = self.reader.span_position();

        let cp = self.reader.peek().filter(|&cp| !unicode::is_syntax_character(cp))?;
        self.reader.advance();

        Some(ast::Atom::Character(Box::new_in(
            ast::Character {
                span: self.span_factory.create(span_start, self.reader.span_position()),
                value: cp,
            },
            self.allocator,
        )))
    }

    pub(super) fn consume_dot(&mut self) -> Option<ast::Atom<'a>> {
        let span_start = self.reader.span_position();

        if !self.reader.eat('.') {
            return None;
        }

        Some(ast::Atom::CharacterSet(Box::new_in(
            ast::CharacterSet::AnyCharacterSet(Box::new_in(
                ast::AnyCharacterSet {
                    span: self.span_factory.create(span_start, self.reader.span_position()),
                },
                self.allocator,
            )),
            self.allocator,
        )))
    }

    // ```
    // AtomEscape[UnicodeMode, NamedCaptureGroups] ::
    //   DecimalEscape
    //   CharacterClassEscape[?UnicodeMode]
    //   CharacterEscape[?UnicodeMode]
    //   [+NamedCaptureGroups] k GroupName[?UnicodeMode]
    // ```
    // <https://tc39.es/ecma262/#prod-AtomEscape>
    pub(super) fn consume_atom_escape(&mut self) -> Result<Option<ast::Atom<'a>>> {
        let span_start = self.reader.span_position();

        if !self.reader.eat('\\') {
            return Ok(None);
        }

        // `DecimalEscape`: \1 means Backreference
        if let Some(normal_backreference) = self.consume_normal_backreference(span_start) {
            return Ok(Some(ast::Atom::Backreference(Box::new_in(
                normal_backreference,
                self.allocator,
            ))));
        }

        // `CharacterClassEscape`: \d
        if let Some(character_class_escape) = self.consume_character_class_escape(span_start) {
            return Ok(Some(ast::Atom::CharacterSet(Box::new_in(
                ast::CharacterSet::EscapeCharacterSet(Box::new_in(
                    character_class_escape,
                    self.allocator,
                )),
                self.allocator,
            ))));
        }
        // `CharacterClassEscape`: \p{...}
        if self.state.is_unicode_mode() {
            if let Some(character_class_escape_unicode) =
                self.consume_character_class_escape_unicode(span_start)?
            {
                return Ok(Some(ast::Atom::CharacterSet(Box::new_in(
                    ast::CharacterSet::UnicodePropertyCharacterSet(Box::new_in(
                        character_class_escape_unicode,
                        self.allocator,
                    )),
                    self.allocator,
                ))));
            }
        }

        // `CharacterEscape`: \n, \cM, \0, etc...
        if let Some(character) = self.consume_character_escape(span_start)? {
            return Ok(Some(ast::Atom::Character(Box::new_in(character, self.allocator))));
        }

        // `k<GroupName>`: \k<name> means Backreference
        if let Some(named_backreference) = self.consume_named_backreference(span_start)? {
            return Ok(Some(ast::Atom::Backreference(Box::new_in(
                named_backreference,
                self.allocator,
            ))));
        }

        Err(OxcDiagnostic::error("Invalid escape"))
    }

    // ```
    // CharacterClass[UnicodeMode, UnicodeSetsMode] ::
    //   [ [lookahead ≠ ^] ClassContents[?UnicodeMode, ?UnicodeSetsMode] ]
    //   [^ ClassContents[?UnicodeMode, ?UnicodeSetsMode] ]
    // ```
    // <https://tc39.es/ecma262/#prod-CharacterClass>
    pub(super) fn consume_character_class(&mut self) -> Result<Option<ast::Atom<'a>>> {
        let span_start = self.reader.span_position();

        if self.reader.eat('[') {
            let negate = self.reader.eat('^');

            if self.state.is_unicode_sets_mode() {
                let contents = self.consume_class_contents_unicode_sets()?;
                if self.reader.eat(']') {
                    return Ok(Some(ast::Atom::CharacterClass(Box::new_in(
                        ast::CharacterClass::UnicodeSetsCharacterClass(Box::new_in(
                            ast::UnicodeSetsCharacterClass {
                                span: self
                                    .span_factory
                                    .create(span_start, self.reader.span_position()),
                                negate,
                                elements: contents,
                            },
                            self.allocator,
                        )),
                        self.allocator,
                    ))));
                }
            }

            let contents = self.consume_class_contents()?;
            if self.reader.eat(']') {
                return Ok(Some(ast::Atom::CharacterClass(Box::new_in(
                    ast::CharacterClass::ClassRangesCharacterClass(Box::new_in(
                        ast::ClassRangesCharacterClass {
                            span: self.span_factory.create(span_start, self.reader.span_position()),
                            negate,
                            elements: contents,
                        },
                        self.allocator,
                    )),
                    self.allocator,
                ))));
            }

            return Err(OxcDiagnostic::error("Unterminated character class"));
        }

        Ok(None)
    }

    // ```
    // ClassContents[UnicodeMode, UnicodeSetsMode] ::
    //   [empty]
    //   [~UnicodeSetsMode] NonemptyClassRanges[?UnicodeMode]
    //   [+UnicodeSetsMode] ClassSetExpression
    // ```
    // <https://tc39.es/ecma262/#prod-ClassContents>
    fn consume_class_contents(
        &mut self,
    ) -> Result<Vec<'a, ast::ClassRangesCharacterClassElement<'a>>> {
        self.consume_nonempty_class_ranges()
    }
    fn consume_class_contents_unicode_sets(
        &mut self,
    ) -> Result<Vec<'a, ast::UnicodeSetsCharacterClassElement<'a>>> {
        // self.consume_class_set_expression()
        if self.reader.eat('👻') {
            return Err(OxcDiagnostic::error("TODO"));
        }
        Ok(Vec::new_in(self.allocator))
    }

    // ```
    //  ( GroupSpecifier[?UnicodeMode]opt Disjunction[?UnicodeMode, ?UnicodeSetsMode, ?NamedCaptureGroups] )
    // ```
    pub(super) fn consume_capturing_group(&mut self) -> Result<Option<ast::Atom<'a>>> {
        let span_start = self.reader.span_position();

        if self.reader.eat('(') {
            let group_name = self.consume_group_specifier()?;
            let disjunction = self.consume_disjunction()?;

            if self.reader.eat(')') {
                return Ok(Some(ast::Atom::CapturingGroup(Box::new_in(
                    ast::CapturingGroup {
                        span: self.span_factory.create(span_start, self.reader.span_position()),
                        name: group_name,
                        alternatives: disjunction,
                    },
                    self.allocator,
                ))));
            }

            return Err(OxcDiagnostic::error("Unterminated group"));
        }

        Ok(None)
    }

    // ```
    // GroupSpecifier[UnicodeMode] ::
    //   ? GroupName[?UnicodeMode]
    // ```
    // <https://tc39.es/ecma262/#prod-GroupSpecifier>
    fn consume_group_specifier(&mut self) -> Result<Option<SpanAtom<'a>>> {
        if self.reader.eat('?') {
            if let Some(group_name) = self.consume_group_name()? {
                // TODO: Implement
                // if (this._groupSpecifiers.hasInScope(this._lastStrValue)) {
                //   this.raise("Duplicate capture group name");
                // }
                // this._groupSpecifiers.addToScope(this._lastStrValue);
                return Ok(Some(group_name));
            }

            return Err(OxcDiagnostic::error("Invalid group"));
        }

        Ok(None)
    }

    // ```
    // (?: Disjunction[?UnicodeMode, ?UnicodeSetsMode, ?NamedCaptureGroups] )
    // ```
    pub(super) fn consume_non_capturing_group(&mut self) -> Result<Option<ast::Atom<'a>>> {
        let span_start = self.reader.span_position();

        if self.reader.eat3('(', '?', ':') {
            let disjunction = self.consume_disjunction()?;

            if self.reader.eat(')') {
                return Ok(Some(ast::Atom::NonCapturingGroup(Box::new_in(
                    ast::NonCapturingGroup {
                        span: self.span_factory.create(span_start, self.reader.span_position()),
                        alternatives: disjunction,
                    },
                    self.allocator,
                ))));
            }

            return Err(OxcDiagnostic::error("Unterminated group"));
        }

        Ok(None)
    }
}