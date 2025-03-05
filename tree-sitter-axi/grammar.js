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
const data = "data";
const forall = "forall";
const of = "of";
const proof = "proof";
const proposition = "proposition";
const qed = "qed";
const record = "record";
const theorem = "theorem";
const type = "type";
const where = "where";

// named keyword nodes
const assumption = "assumption";
const refl = "refl";
const trivial = "trivial";

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
      $.data_type_definition,
      $.record_type_definition,
      $.constant_definition,
      $.theorem_definition,
      $.axiom_declaration,
      $.proposition_definition
    ),

    data_type_definition: $ => seq(
      data,
      type,
      $.identifier,
      optional($.parameters),
      where,
      $.begin,
      repeat(seq(
        $.separator,
        $.constructor_declaration
      )),
      $.end
    ),

    constructor_declaration: $ => seq(
      $.identifier,
      optional($.parameters),
      optional(choice(
        seq(
          of,
          optional(seq(
            $._term,
            repeat(seq(
              amp,
              $._term
            ))
          ))
        ),
        $.type
      ))
    ),

    record_type_definition: $ => seq(
      record,
      type,
      $.identifier,
      optional($.parameters),
      where,
      $.begin,
      repeat(seq(
        $.separator,
        $.record_field_declaration
      )),
      $.end
    ),

    record_field_declaration: $ => seq(
      $.identifier,
      optional($.parameters),
      optional($.type)
    ),

    constant_definition: $ => seq(
      $.identifier,
      optional($.parameters),
      optional($.type),
      optional($.value)
    ),

    parameters: $ => prec.left(repeat1($._parameter)),

    _parameter: $ => choice(
      $.identifier,
      $.explicit_parameters,
      $.implicit_parameters
    ),

    explicit_parameters: $ => seq(lparen, repeat1($.identifier), optional($.type), rparen),
    implicit_parameters: $ => seq(lbrace, repeat1($.identifier), optional($.type), rbrace),

    theorem_definition: $ => seq(
      theorem,
      $.identifier,
      optional($.parameters),
      $.type,
      $.separator,
      choice(
        $.proof,
        $.value
      )
    ),

    axiom_declaration: $ => prec(1, seq(
      axiom,
      optional($.identifier),
      optional($.parameters),
      $.type
    )),

    proof: $ => seq(
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
      $.assumption,
      $.identifier,
      $.refl,
      $.trivial,
      $.assume,
      $.apply,
    ),

    assumption: $ => assumption,

    refl: $ => refl,

    trivial: $ => trivial,

    assume: $ => $._assumptions,

    _assumptions: $ => seq(
      assume,
      repeat1($._atomic_proof_pattern)
    ),

    proof_patterns: $ => repeat1($._atomic_proof_pattern),

    _atomic_proof_pattern: $ => choice(
      $.identifier,
      $.refl,
      $.trivial,
      seq(lparen, $._nested_proof_pattern, rparen)
    ),

    _nested_proof_pattern: $ => choice(
      $.typed_assumptions,
      $.both_pattern,
      $._atomic_proof_pattern
    ),

    typed_assumptions: $ => seq(
      repeat1($._atomic_proof_pattern),
      $.type,
    ),

    both_pattern: $ => seq(both, $._atomic_proof_pattern, $._atomic_proof_pattern),

    apply: $ => seq(
      apply,
      $._term,
      repeat(seq(comma, $._term))
    ),

    proposition_definition: $ => seq(
      proposition,
      $.identifier,
      optional($.parameters),
      optional($.type),
      optional($.value)
    ),

    type: $ => seq(colon, $._term),

    value: $ => seq(eq, $._term),

    _term: $ => choice(
      $.lambda,
      $.cases,
      $.forall,
      $.arrow,
      $.implication,
      $.equivalence,
      $.disjunction,
      $.conjunction,
      $.negation,
      $.equality,
      $.call,
      $.number,
      $.identifier,
      seq(lparen, $._term, rparen),
    ),

    lambda: $ => prec.right(0, seq(
      lambda,
      $.parameters,
      arrow,
      $._term
    )),

    cases: $ => seq(pipe, arrow),

    case: $ => prec.left(10, seq(pipe, repeat($.pattern), arrow, prec.right(0, $._term))),

    pattern: $ => choice(
      prec(10, seq($.pattern, repeat1($.pattern))),
      prec(11, $.identifier),
      prec(11, seq(lparen, $.pattern, rparen)),
    ),

    forall: $ => prec.right(0, seq(forall, optional($.parameters), comma, $._term)),

    arrow: $ => prec.right(1, seq($._term, arrow, $._term)),

    implication: $ => prec.right(1, seq($._term, implication, $._term)),

    equivalence: $ => prec.right(2, seq($._term, equivalence, $._term)),

    disjunction: $ => prec.right(3, seq($._term, or, $._term)),

    conjunction: $ => prec.right(4, seq($._term, and, $._term)),

    negation: $ => prec.right(5, seq(negation, $._term)),

    equality: $ => prec.left(6, seq($._term, equality, $._term)),

    call: $ => prec.left(10, seq($._term, $._term)),
  }
});
