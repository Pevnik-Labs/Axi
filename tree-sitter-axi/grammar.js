/**
 * @file Axi grammar for tree-sitter
 * @author Mateusz Pyzik <mateusz@tunnelvisionlabs.xyz>
 * @license MIT
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

// brackets
const lparen = "(";
const rparen = ")";
const lbrace = "{";
const rbrace = "}";

// punctuation
const colon = ":";
const comma = ",";
const dot = ".";
const lambda = "\\";
const pipe = "|";

// operators
const amp = "&";
const and = "/\\";
const arrow = "->";
const eq = "=";
const equality = "===";
const equivalence = "<-->";
const implication = "-->";
const negation = "~";
const or = "\\/";

// anonymous keyword nodes
const apply = "apply";
const assume = "assume";
const axiom = "axiom";
const by = "by";  
const forall = "forall";
const lemma = "lemma";
const of = "of";
const proof = "proof";
const qed = "qed";
const theorem = "theorem";
const where = "where";

// named keyword nodes
const assumption = "assumption";
const data = "data";
const module_ = "module";
const proposition = "proposition";
const record = "record";
const type = "type";

module.exports = grammar({
  name: "axi",

  word: $ => $.identifier,

  externals: $ => [
    $.begin,
    $.separator,
    $.end
  ],

  extras: $ => [
    /\s/,
    $.block_comment,
    $.line_comment
  ],

  conflicts: $ => [],

  rules: {
    // start rule
    source_file: $ => seq(
      optional(seq(
        $.separator,
        $.shebang,
      )),
      repeat(seq(
        $.separator,
        $._declaration
      )),
      optional($.separator),
    ),

    // comments
    block_comment: $ => /\/\*[^*]*\*+([^/*][^*]*\*+)*\//,
    line_comment: $ => /\/\/.*/,

    // tokens
    shebang: $ => /#!.*/,
    identifier: $ => /[a-zA-Z_][-a-zA-Z0-9_']*/,
    hole_identifier: $ => /[?][a-zA-Z_][-a-zA-Z0-9_']*/,
    number: $ => /\d+/,

    _declaration: $ => choice(
      $.structure_declaration,
      $.constant_declaration,
      $.theorem_declaration,
      $.axiom_declaration
    ),

    structure_declaration: $ => seq(
      $._structure_specifier,
      optional($._sort_specifier),
      $.identifier,
      optional($.parameters),
      $.where_block
    ),

    constant_declaration: $ => seq(
      optional($._sort_specifier),
      $.identifier,
      optional($.parameters),
      optional($._ann),
      optional($.value)
    ),

    theorem_declaration: $ => seq(
      theorem,
      $.identifier,
      optional($.parameters),
      $.type_ann,
      $._definition
    ),

    lemma_declaration: $ => seq(
      lemma,
      $.identifier,
      optional($.parameters),
      optional($.type_ann),
      $._definition
    ),

    axiom_declaration: $ => seq(
      axiom,
      $.identifier,
      optional($.parameters),
      $.type_ann
    ),

    _structure_specifier: $ => choice(
      $.data,
      $.record,
      $.module
    ),

    data: $ => data,

    record: $ => record,

    module: $ => module_,

    _sort_specifier: $ => choice(
      $.type,
      $.proposition
    ),

    type: $ => type,

    proposition: $ => proposition,

    parameters: $ => repeat1($._parameter_group),

    _parameter_group: $ => choice(
      $.identifier,
      $.explicit_parameters,
      $.implicit_parameters
    ),

    explicit_parameters: $ => seq(lparen, repeat1($.identifier), $.type_ann, rparen),
    implicit_parameters: $ => seq(lbrace, repeat1($.identifier), optional($.type_ann), rbrace),

    where_block: $ => seq(
      where,
      $.begin,
      repeat(seq(
        $.separator,
        $._declaration
      )),
      $.end
    ),

    _definition: $ => choice(
      $.by_block,
      $.proof_block,
      $.value
    ),

    bullet_block: $ => seq(
      dot,
      $.begin,
      repeat(seq(
        $.separator,
        $._proof_step
      )),
      $.end
    ),

    by_block: $ => seq(
      by,
      $.begin,
      repeat(seq(
        $.separator,
        $._proof_step
      )),
      $.end
    ),

    proof_block: $ => seq(
      proof,
      $.begin,
      repeat(seq(
        $.separator,
        $._proof_step
      )),
      $.end,
      qed
    ),

    _proof_step: $ => choice(
      $.assume,
      $.bullet_block,
      $.lemma_declaration,
      $._term,
    ),

    assume: $ => seq(assume, optional($.patterns)),

    patterns: $ => seq(
      repeat1($._atomic_pattern),
      optional($.type_ann),
    ),

    _atomic_pattern: $ => choice(
      $.identifier,
      seq(lparen, $._nested_pattern, rparen)
    ),

    _nested_pattern: $ => choice(
      $._atomic_pattern,
      $.ctor_pattern,
      $.ann_pattern
    ),

    ctor_pattern: $ => seq(
      $.identifier,
      repeat1($._atomic_pattern),
    ),

    ann_pattern: $ => seq(
      $._nested_pattern,
      $.type_ann,
    ),

    _ann: $ => choice(
      $.con_ann,
      $.type_ann
    ),

    con_ann: $ => prec(1, seq(of, $._term, repeat(seq(amp, prec(1, $._term))))),

    type_ann: $ => seq(colon, prec(2, $._term)),

    value: $ => seq(eq, $._term),

    _term: $ => choice(
      $.lambda,
      $.clauses,
      $.apply,
      $.call_by,
      $.forall,
      $.arrow,
      $.implication,
      $.equivalence,
      $.disjunction,
      $.conjunction,
      $.negation,
      $.equality,
      $.call,
      $.assumption,
      $.number,
      $.identifier,
      $.hole_identifier,
      seq(lparen, $._term, rparen),
    ),

    lambda: $ => prec.right(seq(
      lambda,
      optional($.patterns),
      arrow,
      $._term
    )),

    clauses: $ => prec.right(seq(
      lambda,
      optional($.patterns),
      where,
      $.begin,
      repeat(seq(
        $.separator,
        $.clause
      )),
      $.end
    )),

    clause: $ => seq(optional(pipe), $.patterns, arrow, $._term),

    assume_in: $ => prec.right(seq($.assume, "in", $._term)),

    apply: $ => prec.left(seq(apply, $._term, repeat(seq(comma, prec.left($._term))))),

    call_by: $ => seq($._term, $.by_block),

    forall: $ => prec.right(seq(forall, optional($.parameters), comma, $._term)),

    arrow: $ => prec.right(1, seq($._term, arrow, $._term)),

    implication: $ => prec.right(1, seq($._term, implication, $._term)),

    equivalence: $ => prec.right(2, seq($._term, equivalence, $._term)),

    disjunction: $ => prec.right(3, seq($._term, or, $._term)),

    conjunction: $ => prec.right(4, seq($._term, and, $._term)),

    negation: $ => prec.right(5, seq(negation, $._term)),

    equality: $ => prec.right(seq($._term, choice(eq, equality), $._term)),

    call: $ => prec.left(10, seq($._term, $._term)),

    assumption: $ => assumption,
  }
});
