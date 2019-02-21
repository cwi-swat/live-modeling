module lang::nextstep::InstanceSyntax

extend lang::nextstep::CoreSyntax;

start syntax NextepInstance = "input" "{" "old" "static" ObjectDef* oldStat "old" "runtime" ObjectDef* oldRun "new" "static" ObjectDef* newStat "}";

syntax ObjectDef 
  = Type type Atom objectName  FieldInstantiation+ fields 
  | Type type {Atom ","}* objects 
  ;  

syntax FieldInstantiation 
  = VarName fieldName "=" {Atom ","}* atoms
  | VarName fieldName "=" {Int ","}* atoms
  | VarName fieldName "=" "[" "]"
  ;
