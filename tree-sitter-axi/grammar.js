/**
 * @file Axi grammar for tree-sitter
 * @author Mateusz Pyzik <mateusz@tunnelvisionlabs.xyz>
 * @license MIT
 */

/// <reference types='tree-sitter-cli/dsl' />
// @ts-check

const axiom = 'axiom';
const data = 'data';
const forall = 'forall';
const fun = 'fun';
const proof = 'proof';
const proposition = 'proposition';
const qed = 'qed';
const record = 'record';
const refl = 'refl';
const theorem = 'theorem';
const trivial = 'trivial';
const type = 'type';
const where = 'where';

module.exports = grammar({
  name: 'axi',

  word: $ => $.identifier,

  externals: $ => [
    $.begin,
    $.separator,
    $.end
  ],

  extras: $ => [
    /\s/,
    $.line_comment,
    $.block_comment
  ],

  conflicts: $ => [],

  rules: {
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

    shebang: $ => /#!.*/,

    line_comment: $ => /\/\/.*/,

    block_comment: $ => /\/\*[^*]*\*+([^/*][^*]*\*+)*\//,

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
      field('name', $.identifier),
      optional(field('parameters', $.parameters)),
      optional(field('constructors', seq(
        $.begin,
        $.constructor_declaration,
        repeat(seq(
          $.separator,
          $.constructor_declaration
        )),
        $.end
      )))
    ),

    constructor_declaration: $ => seq(
      field('name', $.identifier),
      optional(field('parameters', $.parameters)),
      optional(choice(
        seq(
          'of',
          field('arguments', optional(seq(
            $.type,
            repeat(seq(
              '&',
              $.type
            ))
          )))
        ),
        seq(
          ':',
          field('type', $.type)
        )
      ))
    ),

    record_type_definition: $ => seq(
      record,
      type,
      field('name', $.identifier),
      optional(field('parameters', $.parameters)),
      where,
      $.begin,
      optional(seq(
        repeat(seq(
          $.separator,
          $.record_field_declaration,
        )),
      )),
      $.end
    ),

    record_field_declaration: $ => seq(
      field('name', $.identifier),
      optional(field('parameters', $.parameters)),
      optional(field('type', seq(':', $.type)))
    ),

    constant_definition: $ => seq(
      field('name', $.identifier),
      optional(field('parameters', $.parameters)),
      optional(seq(':', field('type', $.type))),
      optional(seq(':=', field('value', $.expression)))
    ),

    parameters: $ => prec.left(repeat1(choice(
      $.identifier,
      seq('(', $.typed_identifiers, ')'),
      seq('{', $.typed_identifiers, '}')
    ))),

    typed_identifiers: $ => seq(repeat1($.identifier), optional(seq(':', $.type))),

    theorem_definition: $ => seq(
      theorem,
      field('name', $.identifier),
      optional(field('parameters', $.parameters)),
      ':',
      field('proposition', $.expression),
      proof,
      optional(field('proof', $.proof)),
      qed
    ),

    axiom_declaration: $ => prec(1, seq(
      axiom,
      optional(field('name', $.identifier)),
      optional(field('parameters', $.parameters)),
      ':',
      field('proposition', $.expression)
    )),

    proof: $ => seq(
      $.begin,
      $.proof_step,
      repeat(seq(
        $.separator,
        $.proof_step
      )),
      $.end
    ),

    proof_step: $ => choice(
      refl,
      trivial
    ),

    proposition_definition: $ => seq(
      proposition,
      field('name', $.identifier),
      optional(field('parameters', $.parameters)),
      optional(seq(':', field('type', $.type))),
      optional(seq(':=', field('value', $.expression)))
    ),

    identifier: $ => /[a-zA-Z_][a-zA-Z0-9_]*/,

    type: $ => choice(
      prec.right(0, seq($.type, '->', $.type)),
      prec.left(10, seq($.type, repeat1(prec.left(11, $.type)))),
      prec(11, $.identifier),
      prec(11, seq('(', $.type, ')')),
    ),

    expression: $ => choice(
      prec.right(0, $.lambda_expression),
      prec.right(0, $.cases),
      prec.right(0, seq(forall, optional($.parameters), ',', $.expression)),
      prec.right(1, seq($.expression, '-->', $.expression)),       // implication
      prec.right(2, seq($.expression, '<-->', $.expression)),      // equivalence
      prec.right(3, seq($.expression, '\\/', $.expression)),       // disjunction
      prec.right(4, seq($.expression, '/\\', $.expression)),       // conjunction
      prec.right(5, seq('~', $.expression)),                       // negation
      prec.left(6, seq(prec(7, $.expression), '=', $.expression)), // equality
      prec(10, $.function_call),
      prec(11, $.number),
      prec(11, $.identifier),
      prec(11, seq('(', $.expression, ')')),
    ),

    number: $ => /\d+/,

    lambda_expression: $ => seq(
      fun,
      $.parameters,
      '=>',
      $.expression
    ),

    cases: $ => choice(
      seq(repeat1($.case), '$.end'),
      seq('|', '=>', '$.end')
    ),

    case: $ => prec.left(10, seq('|', repeat($.expression), '=>', prec.right(0, $.expression))),

    pattern: $ => choice(
      prec(10, seq($.pattern, repeat1($.pattern))),
      prec(11, $.identifier),
      prec(11, seq('(', $.pattern, ')')),
    ),

    function_call: $ => prec.left(10, seq(
      field('function', $.expression),
      field('arguments', repeat1($.expression))
    )),
  }
});
