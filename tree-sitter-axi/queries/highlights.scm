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
 (#match? @proofterm "^absurd|and-left|and-right|both|cases|or-left|or-right|proving|refl|suffices|trivial$"))

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
  "~"
  "\\/"
  "->"
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
  "in"
  "lemma"
  "of"
] @keyword

[
  (block_comment)
  (line_comment)
  (shebang)
] @comment
