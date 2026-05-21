; Identifiers (most general — more specific captures below override)
(identifier) @variable

; Types
(primitive_type) @type.builtin
(type (identifier) @type)

; Function declarations
(function_declaration name: (identifier) @function)
(parameter name: (identifier) @variable.parameter)

; Function calls
(call_expression function: (identifier) @function.call)

; Built-in calls — match on name
((call_expression function: (identifier) @function.builtin)
 (#match? @function.builtin "^(print|argc|arg)$"))

; Path calls: `module::fn(...)` — leading segments are modules, last is the fn
(call_expression
  function: (path (identifier) @function.call .))

(path (identifier) @namespace
  (identifier) @function.call .)

; Standalone paths (non-call position): `math::pi` — last segment is the value
(path (identifier) @namespace
  (identifier) @variable .)

; `use` paths: all segments rendered as namespaces (last segment is also a
; namespace when the import is a module, or an item — we can't tell here, so
; pick a single sensible default).
(use_declaration
  path: (use_path (identifier) @namespace))

; Literals
(integer_literal) @number
(float_literal) @number
(boolean_literal) @boolean
(string_literal) @string
(escape_sequence) @string.escape

; Keywords
[
  "fn"
  "inline"
  "let"
  "pub"
  "return"
  "use"
] @keyword

[
  "if"
  "else"
  "while"
] @keyword

; Operators
[
  "+" "-" "*" "/" "%" "**"
  "==" "!=" "<" "<=" ">" ">="
  "&&" "||" "!"
  "&" "|" "^" "~" "<<" ">>"
  "=" "->"
] @operator

; Punctuation
[ ";" ":" "::" "," ] @punctuation.delimiter
[ "(" ")" "{" "}" ] @punctuation.bracket

; Comments
(line_comment) @comment
