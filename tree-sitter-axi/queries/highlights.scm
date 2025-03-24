[
  (type)
  (record)
  (data)
  (proposition)
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
 (#match? @proofterm "^absurd|and-left|and-right|both|cases|instantiate|or-left|or-right|refl|simpl|symmetry|transitivity|trivial|with$"))

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
  ":"
  ","
  "."
  "\\"
  "|"
] @punctuation.delimiter

[
  "&"
  "="
] @operator

[
  "by"
  "by-contradiction"
  "chaining"
  "in"
  "for"
  "lemma"
  "of"
  "pick-any"
  "pick-witness"
  "proving"
  "rewrite"
  "such-that"
  "suffices"
  "unfold"
] @keyword

[
  (block_comment)
  (line_comment)
  (shebang)
] @comment
