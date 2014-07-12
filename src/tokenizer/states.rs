// Copyright 2014 The HTML5 for Rust Project Developers. See the
// COPYRIGHT file at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Tokenizer states.
//!
//! This is public for use by the tokenizer tests.  Other library
//! users should not have to care about this.

#[deriving(PartialEq, Eq, Clone, Hash)]
pub enum ScriptEscapeKind {
    Escaped,
    DoubleEscaped,
}

#[deriving(PartialEq, Eq, Clone, Hash)]
pub enum DoctypeIdKind {
    Public,
    System,
}

#[deriving(PartialEq, Eq, Clone, Hash)]
pub enum RawKind {
    Rcdata,
    Rawtext,
    ScriptData,
    ScriptDataEscaped(ScriptEscapeKind),
}

#[deriving(PartialEq, Eq, Clone, Hash)]
pub enum AttrValueKind {
    Unquoted,
    SingleQuoted,
    DoubleQuoted,
}

#[deriving(PartialEq, Eq, Clone, Hash)]
pub enum State {
    Data,
    Plaintext,
    TagOpen,
    EndTagOpen,
    TagName,
    RawData(RawKind),
    RawLessThanSign(RawKind),
    RawEndTagOpen(RawKind),
    RawEndTagName(RawKind),
    ScriptDataEscapeStart(ScriptEscapeKind),
    ScriptDataEscapeStartDash,
    ScriptDataEscapedDash(ScriptEscapeKind),
    ScriptDataEscapedDashDash(ScriptEscapeKind),
    ScriptDataDoubleEscapeEnd,
    BeforeAttributeName,
    AttributeName,
    AfterAttributeName,
    BeforeAttributeValue,
    AttributeValue(AttrValueKind),
    AfterAttributeValueQuoted,
    SelfClosingStartTag,
    BogusComment,
    MarkupDeclarationOpen,
    CommentStart,
    CommentStartDash,
    Comment,
    CommentEndDash,
    CommentEnd,
    CommentEndBang,
    Doctype,
    BeforeDoctypeName,
    DoctypeName,
    AfterDoctypeName,
    AfterDoctypeKeyword(DoctypeIdKind),
    BeforeDoctypeIdentifier(DoctypeIdKind),
    DoctypeIdentifierDoubleQuoted(DoctypeIdKind),
    DoctypeIdentifierSingleQuoted(DoctypeIdKind),
    AfterDoctypeIdentifier(DoctypeIdKind),
    BetweenDoctypePublicAndSystemIdentifiers,
    BogusDoctype,
    CdataSection,
}
