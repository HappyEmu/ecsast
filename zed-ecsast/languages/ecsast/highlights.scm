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
  "return"
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
[ ";" ":" "," ] @punctuation.delimiter
[ "(" ")" "{" "}" ] @punctuation.bracket

; Comments
(line_comment) @comment
