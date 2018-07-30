module lang::nextstep::Syntax

extend lang::std::Layout;

start syntax Spec = StaticDef static DynamicDef dynamic MigrationDef migration InstanceDef instance;

syntax StaticDef = "static" "{" Class* classes "}";

syntax DynamicDef = "runtime" "{" Class* classes "}";

syntax MigrationDef = "migration" "{" Formula* rules "}";

syntax InstanceDef = "input" "{" "old" "static" ObjectDef* oldStat "old" "runtime" ObjectDef* oldRun "new" "static" ObjectDef* newStat "}";

//syntax Class = "class" ClassName name Super? Bounds? bounds "{" ClassBody body "}";
syntax Class = "class" ClassName name "{" ClassBody body "}";

//syntax Super = "extends" ClassName parent;

//syntax Bounds
//  = upperOnly:      "(" Int upper ")"
//  | upperAndLower:  "(" Int from ".." Int to ")"
//  ;

syntax ClassBody = FieldDecl* fields Invariant* inv;

syntax FieldDecl 
  = VarName fieldName ":" Type type "*"? ;

syntax Invariant
  = "invariant" ":" Formula form
  | "invariants" "{" Formula+ forms "}"
  ;

syntax Type 
  = class: ClassName className
  | \int: "int"
  ;

syntax Formula 
  = bracket "(" Formula ")"
  > neg:        "not" Formula
  > some:       "some" Expr
  | no:         "no" Expr
  | \one:       "one" Expr
  > subset:     Expr "in" Expr
  | equality:   Expr "=" Expr
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
  ;

syntax Expr
  = bracket       "(" Expr ")"
  > var:          VarName 
  | lit:          Literal
  | left dotJoin: Expr "." Expr
  > restrict:     Expr "where" RestrictStat
  > left ( union: Expr "++" Expr
         | intersec: Expr "&" Expr
         | setDif: Expr "--" Expr
         )
  > transCl:      "^" Expr
  | reflTrans:    "*" Expr
  > old: "old" //Expr
  | new: "new" //Expr 
  ;


syntax Expr
  = count:      "count" "(" Expr ")"
  | avg:        "avg" "(" Expr ")"
  | min:        "min" "(" Expr ")"
  | max:        "max" "(" Expr ")"
  | abs:        "|" Expr "|"
  > left ( div: Expr "\\" Expr
         | mul: Expr "*" Expr
         > add: Expr "+" Expr
         | sub: Expr "-" Expr
         )
  ;

syntax RestrictStat
  = bracket "(" RestrictStat ")"
  | RestrictExpr "=" RestrictExpr
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
  
syntax ObjectDef 
  = Type type Atom objectName  FieldInstantiation+ fields 
  | Type type {Atom ","}* objects 
  ;  

syntax FieldInstantiation 
  = VarName fieldName "=" {Atom ","}* atoms
  | VarName fieldName "=" {Int ","}* atoms
  ;

lexical ClassName = ([A-Z] !<< [A-Z][a-zA-Z0-9_\']* !>> [a-zA-Z0-9_]) \ Keywords;
lexical VarName = ([a-zA-Z] !<< [a-zA-Z][a-zA-Z0-9_\']* !>> [a-zA-Z0-9_]) \ Keywords;
lexical Atom = ([a-zA-Z] !<< [a-zA-Z][a-zA-Z0-9_\']* !>> [a-zA-Z0-9_]) \ Keywords;

lexical Int = [0-9]+;

keyword Keywords = "static" | "runtime" | "migration" | "class" | "invariant" | "invariants" | "not" | "no" | "some" | "one" | "forall" | "exists" | "int" | "old" | "new" | "input";