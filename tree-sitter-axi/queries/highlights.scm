(identifier) @variable

((identifier) @constructor
 (#match? @constructor "^[A-Z]"))

((identifier) @constant
 (#match? @constant "^[A-Z][A-Z0-9_]*$"))

[
  "("
  ")"
  "{"
  "}"
] @punctuation.bracket

[
  ":"
  ","
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
  "data"
  "forall"
  "of"
  "proof"
  "proposition"
  "qed"
  "record"
  "theorem"
  (assumption)
  (refl)
  (trivial)
] @keyword

[
  (block_comment)
  (line_comment)
  (shebang)
] @comment
