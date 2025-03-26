[
  (class)
  (data)
  "instance"
  (module)
  (proposition)
  (record)
  (type)
  "where"
] @typedefinition

[
  "theorem"
  "declaration"
  "axiom"
] @toplevel

[
  "proof"
  "qed"
] @proofblock

(hole_identifier) @variable

(identifier) @variable

((identifier) @kind
 (#match? @kind "^Type|Prop$"))

((identifier) @typeoperator
 (#match? @typeoperator "^[A-Z]"))

((identifier) @typevar
 (#match? @typevar "^[A-Z]$"))

((identifier) @proofterm
 (#match? @proofterm "^absurd|and-left|and-right|both|cases|or-left|or-right|refl|simpl|symmetry|transitivity|trivial$"))

[
  "assume"
  "apply"
  (assumption)
] @proofterm

((identifier) @absurd
 (#match? @absurd "^absurd$"))

((identifier) @typepropformer
 (#match? @typepropformer "^True|False$"))

[
  "/\\"
  "==="
  "<-->"
  "-->"
  "->"
  "<-"
  "~"
  "\\/"
  "<--"
  "<-"
  "forall"
] @typepropformer

((identifier) @typepropformer
 (#match? @typepropformer "^exists$"))

[
  "("
  ")"
  "{"
  "}"
] @punctuation.bracket

[
  "&"
  ":"
  ","
  "."
  "\\"
  "|"
] @punctuation.delimiter

[
  "="
] @operator

[
  "by"
  "by-contradiction"
  "case"
  "cases"
  "chaining"
  "in"
  "ind"
  "induction"
  "instantiate"
  "for"
  "lemma"
  "let"
  "match"
  "noncomputational"
  "of"
  "pick-any"
  "pick-witness"
  "proving"
  "rewrite"
  "such-that"
  "suffices"
  "unfold"
  "with"
  "witness"
] @keyword

[
  (block_comment)
  (line_comment)
  (shebang)
] @comment
