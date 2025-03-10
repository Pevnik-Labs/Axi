(hole_identifier) @variable

(identifier) @variable

((identifier) @constructor
 (#match? @constructor "^[A-Z]"))

((identifier) @constant
 (#match? @constant "^[A-Z][A-Z0-9_]*$"))

((identifier) @keyword
 (#match? @keyword "^absurd|and-left|and-right|both|cases|or-left|or-right|proving|refl|suffices|trivial$"))

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
  "by"
  "declaration"
  "forall"
  "in"
  "lemma"
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
