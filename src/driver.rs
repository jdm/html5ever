// Copyright 2014 The html5ever Project Developers. See the
// COPYRIGHT file at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! High-level interface to the parser.

use tokenizer::{TokenizerOpts, Tokenizer, TokenSink};
use tree_builder::{TreeBuilderOpts, TreeBuilder, TreeSink};

use std::default::Default;
use std::option;

/// Convenience function to turn a single `String` into an iterator.
pub fn one_input(x: String) -> option::Item<String> {
    Some(x).move_iter()
}

/// Tokenize and send results to a `TokenSink`.
///
/// ## Example
///
/// ```rust
/// let mut sink = MySink;
/// tokenize_to(&mut sink, one_input(my_str), Default::default());
/// ```
pub fn tokenize_to<
        Sink: TokenSink,
        It: Iterator<String>
    >(
        sink: &mut Sink,
        mut input: It,
        opts: TokenizerOpts) {

    let mut tok = Tokenizer::new(sink, opts);
    for s in input {
        tok.feed(s);
    }
    tok.end();
}

/// All-encompassing options struct for the parser.
#[deriving(Clone, Default)]
pub struct ParseOpts {
    /// Tokenizer options.
    pub tokenizer: TokenizerOpts,

    /// Tree builder options.
    pub tree_builder: TreeBuilderOpts,
}

/// Parse and send results to a `TreeSink`.
///
/// ## Example
///
/// ```rust
/// let mut sink = MySink;
/// parse_to(&mut sink, one_input(my_str), Default::default());
/// ```
pub fn parse_to<
        Handle: Clone,
        Sink: TreeSink<Handle>,
        It: Iterator<String>
    >(
        sink: &mut Sink,
        mut input: It,
        opts: ParseOpts) {

    let mut tb  = TreeBuilder::new(sink, opts.tree_builder);
    let mut tok = Tokenizer::new(&mut tb, opts.tokenizer);
    for s in input {
        tok.feed(s);
    }
    tok.end();
}

/// Results which can be extracted from a `TreeSink`.
///
/// Implement this for your parse tree data type so that it
/// can be returned by `parse()`.
pub trait ParseResult<Sink> {
    fn get_result(sink: Sink) -> Self;
}

/// Parse into a type which implements `ParseResult`.
///
/// ## Example
///
/// ```rust
/// let dom: RcDom = parse(one_input(my_str), Default::default());
/// ```
pub fn parse<
        Handle: Clone,
        Sink: Default + TreeSink<Handle>,
        Output: ParseResult<Sink>,
        It: Iterator<String>
    >(
        input: It,
        opts: ParseOpts) -> Output {

    let mut sink: Sink = Default::default();
    parse_to(&mut sink, input, opts);
    ParseResult::get_result(sink)
}
