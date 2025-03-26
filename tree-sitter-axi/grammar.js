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
const eq = "=";
const equality = "===";
const equivalence = "<-->";
const laarrow = "<--";
const Larrow = "<=";
const larrow = "<-";
const negation = "~";
const or = "\\/";
const raarrow = "-->";
const Rarrow = "=>";
const rarrow = "->";

// anonymous keyword nodes
const apply = "apply";
const assume = "assume";
const axiom = "axiom";
const by = "by";
const by_contradiction = "by-contradiction";
const case_ = "case";
const cases = "cases";
const chaining = "chaining";
const declaration = "declaration";
const exists = "exists";
const for_ = "for";
const forall = "forall";
const in_ = "in";
const ind = "ind";
const induction = "induction";
const instance = "instance";
const instantiate = "instantiate";
const lemma = "lemma";
const let_ = "let";
const match = "match";
const noncomputational = "noncomputational";
const of = "of";
const pick_any = "pick-any";
const pick_witness = "pick-witness";
const proof = "proof";
const proving = "proving";
const rewrite = "rewrite";
const such_that = "such-that";
const suffices = "suffices";
const qed = "qed";
const theorem = "theorem";
const unfold = "unfold";
const where = "where";
const with_ = "with";
const witness = "witness";

// named keyword nodes
const assumption = "assumption";
const class_ = "class";
const data = "data";
const module_ = "module";
const proposition = "proposition";
const record = "record";
const type = "type";

// subtokens
const char = /[^'"\\]|\\([abefnrtv\\'"?]|[0-7]{1,3}|x[0-9a-fA-F]+|u[0-9a-fA-F]{4}|U[0-9a-fA-F]{8})/;

module.exports = grammar({
  name: "axi",

  word: $ => $.identifier,

  externals: $ => [
    $.error_recovery,
    $.begin,
    $.separator,
    $.end
  ],

  extras: $ => [
    /\s/,
    $.block_comment,
    $.line_comment,
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
    line_comment: $ => /\/\/(.|\\\n)*/,

    // tokens
    shebang: $ => /#!.*/,
    identifier: $ => /[a-zA-Z_][-a-zA-Z0-9_']*/,
    direction: $ => /<===|===>/,
    hole_identifier: $ => /[?][a-zA-Z_][-a-zA-Z0-9_']*/,
    number: $ => /-?\d+(\.\d*)?(e-?\d+)?/,
    char: $ => token(seq("'", choice(char, "\""), "'")),
    string: $ => token(seq("\"", repeat(choice(char, "'")), "\"")),

    _declaration: $ => choice(
      $.structure_declaration,
      $.instance_declaration,
      $.constant_declaration,
      $.theorem_declaration,
      $.axiom_declaration,
      $.declaration,
      $.pipe_clause,
    ),

    structure_declaration: $ => seq(
      $._structure_specifier,
      optional($._sort_specifier),
      $.identifier,
      optional($.parameters),
      $.where_block
    ),

    instance_declaration: $ => seq(
      instance,
      $._nested_pattern,
      optional(seq(Larrow, $._term, repeat(seq(comma, $._term)))),
      $.where_block,
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

    declaration: $ => seq(
      declaration,
      $.parameters,
      optional($.type_ann)
    ),

    _structure_specifier: $ => choice(
      $.class,
      $.data,
      $.module,
      $.record,
    ),

    class: $ => class_,

    data: $ => data,

    module: $ => module_,

    record: $ => record,

    _sort_specifier: $ => choice(
      $.type,
      $.proposition
    ),

    type: $ => type,

    proposition: $ => proposition,

    parameters: $ => repeat1($._parameter_group),

    _parameter_group: $ => choice(
      $.identifier,
      $._ctor_parameter,
      $.explicit_parameters,
      $.implicit_parameters
    ),

    _ctor_parameter: $ => seq(lparen, $.ctor_pattern, rparen),
    explicit_parameters: $ => seq(lparen, repeat1($._atomic_pattern), $.type_ann, rparen),
    implicit_parameters: $ => seq(lbrace, repeat1($._atomic_pattern), optional($.type_ann), rbrace),

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
      $._proof_decl,
      $.bullet_block,
      $.cases,
      $.induction,
      $.pipe_clause,
      $.proving,
      $.instantiate,
      $.intro,
      $.witness,
      $._term,
    ),

    _proof_decl: $ => choice(
      $.assume,
      $.by_contradiction,
      seq(let_, optional(noncomputational), $._declaration),
      $.lemma_declaration,
      $.pick_any,
      $.pick_witness,
      $.chaining,
      $.rewrite,
      $.unfold,
    ),

    assume: $ => seq(assume, $.patterns),

    by_contradiction: $ => seq(by_contradiction, $._atomic_pattern, optional($.type_ann)),

    pick_any: $ => seq(pick_any, $.patterns),

    pick_witness: $ => seq(pick_witness, $.patterns, for_, $._term),

    patterns: $ => seq(
      repeat1($._atomic_pattern),
      optional($.type_ann),
    ),

    _atomic_pattern: $ => choice(
      $.identifier,
      $.direction,
      seq(lparen, $.witness_pattern, rparen),
      seq(lparen, $._nested_pattern, rparen)
    ),

    witness_pattern: $ => seq(
      witness,
      $._nested_pattern,
      such_that,
      $._nested_pattern
    ),

    _nested_pattern: $ => choice(
      $._atomic_pattern,
      $.ctor_pattern,
      $.and_pattern,
      $.ind_pattern,
      $.ann_pattern,
    ),

    ctor_pattern: $ => seq(
      repeat1($._atomic_pattern),
      $._atomic_pattern,
    ),

    and_pattern: $ => prec.right(seq(
      $._nested_pattern,
      amp,
      $._nested_pattern
    )),

    ind_pattern: $ => prec.right(seq(ind, $._nested_pattern)),

    ann_pattern: $ => seq(
      $._nested_pattern,
      $.type_ann,
    ),

    _ann: $ => choice(
      $.ctor_ann,
      $.type_ann
    ),

    ctor_ann: $ => prec(1, seq(of, $._term, repeat(seq(comma, prec(1, $._term))))),

    type_ann: $ => seq(colon, prec.left(2, $._term)),

    chaining: $ => seq(chaining, $.begin, repeat($.chain_link), $.end),

    chain_link: $ => prec.left(seq(choice(
      laarrow,
      larrow,
      raarrow,
      rarrow,
      eq,
      equality,
      equivalence,
      prec(11, $._term),
    ), $._term, optional($.by_block))),

    rewrite: $ => seq(rewrite, optional($._direction), $._term, repeat(seq(comma, optional($._direction), $._term))),

    unfold: $ => seq(unfold, $._atomic_pattern, repeat(seq(comma, $._atomic_pattern))),

    _direction: $ => choice(larrow, rarrow),

    cases: $ => seq(cases, $._term, optional(with_)),

    induction: $ => seq(induction, $._term, optional(with_)),

    proving: $ => seq(proving, $._term),

    instantiate: $ => seq(instantiate, $._term),

    intro: $ => seq(lambda, optional($.patterns)),

    witness: $ => seq(witness, optional(seq($._term))),

    value: $ => seq(eq, $._term),

    _term: $ => choice(
      $.ann_term,
      $.decl_in,
      $.witness_such_that,
      $.lambda,
      $.case,
      $.clauses,
      $.match_with,
      $.apply,
      $.proving_by,
      $.suffices_by,
      $.exists,
      $.forall,
      $.arrow,
      $.implication,
      $.equivalence,
      $.disjunction,
      $.conjunction,
      $.negation,
      $.equality,
      $.call,
      $.implicit_call,
      $.instantiate_with,
      $.assumption,
      $.number,
      $.char,
      $.string,
      $.identifier,
      $.hole_identifier,
      prec(11, seq(lparen, prec(0, $._term), rparen)),
    ),

    lambda: $ => prec.right(seq(
      lambda,
      optional($.patterns),
      rarrow,
      $._term
    )),

    case: $ => prec.right(seq(
      case_,
      $._term,
      where,  
      $.begin,
      repeat(seq(
        $.separator,
        $.clause
      )),
      $.end
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

    clause: $ => seq($.patterns, rarrow, $._term),

    match_with: $ => prec.right(seq(match, $._term, with_, repeat($.pipe_clause))),

    pipe_clause: $ => seq(pipe, $._nested_pattern, repeat(seq(comma, $._nested_pattern)), Rarrow, $.begin, repeat(seq($.separator, $._proof_step)), $.end),

    ann_term: $ => prec.left(1, seq($._term, colon, $._term)),

    decl_in: $ => prec.right(seq($._proof_decl, in_, $._term)),

    witness_such_that: $ => prec.right(seq(witness, $._term, such_that, $._term)),

    apply: $ => prec.left(seq(apply, $._term, repeat(seq(comma, prec.left($._term))))),

    proving_by: $ => seq(proving, optional($._term), $.by_block),

    suffices_by: $ => seq(suffices, $._term, $.by_block),

    exists: $ => prec.right(seq(exists, optional($.parameters), optional($.type_ann), comma, $._term)),

    forall: $ => prec.right(seq(forall, optional($.parameters), optional($.type_ann), comma, $._term)),

    arrow: $ => prec.right(1, seq($._term, rarrow, $._term)),

    implication: $ => prec.right(1, seq($._term, raarrow, $._term)),

    equivalence: $ => prec.right(2, seq($._term, equivalence, $._term)),

    disjunction: $ => prec.right(3, seq($._term, or, $._term)),

    conjunction: $ => prec.right(4, seq($._term, and, $._term)),

    negation: $ => prec.right(5, seq(negation, $._term)),

    equality: $ => prec.right(seq($._term, choice(eq, equality), $._term)),

    call: $ => prec.left(10, seq($._term, $._term)),

    implicit_call: $ => prec.left(10, seq($._term, lbrace, $._term, rbrace)),

    instantiate_with: $ => seq(instantiate, $._term, with_),

    assumption: $ => assumption,
  }
});
