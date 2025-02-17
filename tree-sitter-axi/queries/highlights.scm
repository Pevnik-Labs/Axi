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
  ","
] @punctuation.delimiter

[
  "->"
  "=>"
  ":"
  ":="
  "-->"
  "<-->"
  "\\/"
  "/\\"
  "~"
  "="
] @operator

[
  "axiom"
  "data"
  "forall"
  "fun"
  "proof"
  "proposition"
  "qed"
  "record"
  "refl"
  "theorem"
  "trivial"
  "type"
] @keyword

[
  (shebang)
  (line_comment)
  (block_comment)
] @comment
