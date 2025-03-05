(identifier) @variable

((identifier) @constructor
 (#match? @constructor "^[A-Z]"))

((identifier) @constant
 (#match? @constant "^[A-Z][A-Z0-9_]*$"))

((identifier) @keyword
 (#match? @keyword "^absurd|and-left|and-right|cases|or-left|or-right|refl|trivial$"))

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
  "/\\"
  "->"
  "="
  "==="
  "==="
  "<-->"
  "-->"
  "~"
  "\\/"
] @operator

[
  "apply"
  "assume"
  "axiom"
  "both"
  "forall"
  "of"
  "proof"
  "qed"
  "theorem"
  "where"
  (assumption)
  (data)
  (proposition)
  (record)
  (type)
] @keyword

[
  (block_comment)
  (line_comment)
  (shebang)
] @comment
