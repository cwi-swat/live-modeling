module lang::nextstep::Syntax

extend lang::nextstep::CoreSyntax;

start syntax Spec = StaticDef static DynamicDef dynamic MigrationDef migration DistanceDef? distance;

syntax StaticDef = "static" Class* classes;

syntax DynamicDef = "runtime" Class* classes;

syntax MigrationDef = "migration" Formula* rules;

syntax DistanceDef = "distance" PriorityDistance* priorities;

syntax Class = "class" ClassName name "{" ClassBody body "}";

syntax ClassBody = FieldDecl* fields Invariant? inv;

syntax FieldDecl 
  = VarName fieldName ":" Type type "*"? ;

syntax Invariant
  = Formula+ forms
  ;

syntax Formula 
  = bracket "(" Formula ")"
  > neg:        "not" Formula
  > some:       "some" Expr
  | no:         "no" Expr
  | \one:       "one" Expr
  > subset:     Expr "in" Expr
  | equality:   Expr "=" Expr
  | inequality: Expr "!=" Expr
  > implies:    Formula "=\>" Formula
  | iff:        Formula "\<=\>" Formula
  > conj:       Formula "&&" Formula
  | disj:       Formula "||" Formula
  > forall:     "forall" {QuantDecl ","}+ decls "|" Formula form
  | exists:     "exists" {QuantDecl ","}+ decls "|" Formula form
  ;
  
syntax QuantDecl = VarName ":" Expr;  
  
syntax Formula
  = intGte:     Expr "\>=" Expr
  | intGt:      Expr "\>" Expr
  | intLte:     Expr "\<=" Expr
  | intLt:      Expr "\<" Expr
//  | intEq:	Expr "=" Expr  
  ;

syntax Expr
  = bracket       "(" Expr ")"
  > var:          VarName 
  | cls:          ClassName
  | this:         "this"
  | lit:          Literal
  | left dotJoin: Expr "." Expr
  | left relJoin: Expr "_" Expr
  > restrict:     Expr "where" RestrictStat
  > left ( union: Expr "++" Expr
         | intersec: Expr "&" Expr
         | setDif: Expr "--" Expr
         )
  > transCl:      "^" Expr
  | reflTrans:    "*" Expr
  > old: "old" "[" Expr expr "]"
  | new: "new" "[" Expr expr "]" 
  ;


syntax Expr
  = count:      "count" "(" Expr ")"	// not implemented
  | avg:        "avg" "(" Expr ")"		// not implemented
  | min:        "min" "(" Expr ")"		// not implemented
  | max:        "max" "(" Expr ")"		// not implemented
  | abs:        "|" Expr "|"
  > left ( div: Expr "\\" Expr
         | mul: Expr "*" Expr
         > add: Expr "+" Expr
         | sub: Expr "-" Expr
         )
  ;

syntax RestrictStat
  = "(" RestrictExpr "=" RestrictExpr ")"
  ;

syntax RestrictExpr
  = QualifiedName att
  ;

syntax QualifiedName 
  = left VarName ("." VarName)*
  ; 

syntax Literal
  = intLit: Int
  ;
  
syntax PriorityDistance
  = Expr distance ":" Int priority
  ;
