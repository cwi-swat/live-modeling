module lang::nextstep::CoreSyntax

syntax Type 
  = class: ClassName className
  | \int: "int"
  ;

// COMMON LEXEMES
  
lexical ClassName = ([A-Z] !<< [A-Z][a-zA-Z0-9_\']* !>> [a-zA-Z0-9_]) \ Keywords;
lexical VarName = ([a-z] !<< [a-z][a-zA-Z0-9_\']* !>> [a-zA-Z0-9_]) \ Keywords;
lexical Atom = ([a-zA-Z] !<< [a-zA-Z][a-zA-Z0-9_\']* !>> [a-zA-Z0-9_]) \ Keywords;

lexical Int = [0-9]+;

keyword Keywords = "static" | "runtime" | "migration" | "class" | "invariant" | "invariants" | "not" | "no" | "some" | "one" | "forall" | "exists" | "int" | "old" | "new" | "input" | "this";

layout Standard 
  = WhitespaceOrComment* !>> [\ \t\n\f\r] !>> "//";
  
syntax WhitespaceOrComment 
  = whitespace: Whitespace
  | comment: Comment
  ; 

lexical Comment = @category="Comment" "//" ![\n]* $;

lexical Whitespace 
  = [\u0009-\u000D \u0020 \u0085 \u00A0 \u1680 \u180E \u2000-\u200A \u2028 \u2029 \u202F \u205F \u3000]
  ; 
  