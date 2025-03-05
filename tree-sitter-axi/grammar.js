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
const both = "both";
const forall = "forall";
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
      $.block
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

    parameters: $ => repeat1($._parameter),

    _parameter: $ => choice(
      $.identifier,
      $.explicit_parameters,
      $.implicit_parameters
    ),

    explicit_parameters: $ => seq(lparen, repeat1($.identifier), optional($.type_ann), rparen),
    implicit_parameters: $ => seq(lbrace, repeat1($.identifier), optional($.type_ann), rbrace),

    block: $ => seq(
      where,
      $.begin,
      repeat(seq(
        $.separator,
        $._declaration)),
      $.end
    ),

    _definition: $ => choice(
      $.proof,
      $.value
    ),

    proof: $ => seq(
      $.separator,
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
      $._term,
    ),

    assume: $ => seq(assume, optional($.ann_patterns)),

    patterns: $ => repeat1($._atomic_pattern),

    _atomic_pattern: $ => choice(
      $.identifier,
      seq(lparen, $._nested_pattern, rparen)
    ),

    _nested_pattern: $ => choice(
      $.ann_patterns,
      $.both_pattern
    ),

    ann_patterns: $ => seq(
      repeat1($._atomic_pattern),
      optional($.type_ann),
    ),

    both_pattern: $ => seq(both, $._atomic_pattern, $._atomic_pattern),

    _ann: $ => choice(
      $.con_ann,
      $.type_ann
    ),

    con_ann: $ => seq(of, $._term, repeat(seq(amp, $._term))),

    type_ann: $ => seq(colon, $._term),

    value: $ => seq(eq, $._term),

    _term: $ => choice(
      $.lambda,
      $.clauses,
      $.bullet,
      $.apply,
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
      seq(lparen, $._term, rparen),
    ),

    lambda: $ => seq(
      lambda,
      optional($.ann_patterns),
      arrow,
      $._term
    ),

    clauses: $ => seq(
      lambda,
      optional($.ann_patterns),
      where,
      $.begin,
      repeat($.clause),
      $.end
    ),

    clause: $ => seq($.separator, optional(pipe), $.patterns, arrow, $._term),

    assume_in: $ => seq($.assume, "in", $._term),

    bullet: $ => seq(
      dot,
      $.begin,
      $._proof_step,
      repeat(seq(
        $.separator,
        $._proof_step
      )),
      $.end
    ),

    apply: $ => prec.right(0, seq(apply, $._term, repeat(seq(comma, $._term)))),

    forall: $ => prec.right(0, seq(forall, optional($.parameters), comma, $._term)),

    arrow: $ => prec.right(1, seq($._term, arrow, $._term)),

    implication: $ => prec.right(1, seq($._term, implication, $._term)),

    equivalence: $ => prec.right(2, seq($._term, equivalence, $._term)),

    disjunction: $ => prec.right(3, seq($._term, or, $._term)),

    conjunction: $ => prec.right(4, seq($._term, and, $._term)),

    negation: $ => prec.right(5, seq(negation, $._term)),

    equality: $ => prec.left(6, seq($._term, equality, $._term)),

    call: $ => prec.left(10, seq($._term, $._term)),

    assumption: $ => assumption,
  }
});
