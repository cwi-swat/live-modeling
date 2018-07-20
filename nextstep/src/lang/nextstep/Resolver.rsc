module lang::nextstep::Resolver

import lang::nextstep::Syntax;

import ParseTree;
import IO;

alias Ref = rel[loc use, loc def];
alias ResolvedTypes = map[loc use, Class cls];

ResolvedTypes resolveTypes(Spec spec) { 
  map[str className, Class cls] defs = ("<c.name>":c | /Class c := spec);  
  
  return (t@\loc : defs["<className>"] | /t:(Type)`<ClassName className>` := spec);
}