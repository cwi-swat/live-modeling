module lang::nextstep::Annotator

import lang::nextstep::Resolver;
import lang::nextstep::Extractor;
import lang::nextstep::RelationsGenerator;
import lang::nextstep::Syntax;

import translation::AST;
import translation::theories::integer::AST;

import IO;
import ParseTree;

anno str Class@alleRel;
anno str Expr@alleRel;

anno list[HeaderAttribute] Expr@header;

alias AlleRel = tuple[str name, list[HeaderAttribute] header];

alias Env = map[tuple[str nxtstRel, Step stp, Part prt], AlleRel];

alias Collect = tuple[void (loc,AlleRel) addAlleRel, AlleRel (loc) getAlleRel, void (loc,list[HeaderAttribute]) addHeader, list[HeaderAttribute] (loc) getHeader, void (str,Step,AlleRel) addToEnv, void (loc,str) addType, str (loc) getType, AlleRel (str,Step) lookupClass, AlleRel (str,Cls,Step) lookupField, Cls (str) lookupCls, Cls (Cls,str) lookupFieldCls];

alias ResolvedAlleRels = map[loc,AlleRel];
alias ResolvedFieldTypes = map[loc,str];
alias ResolvedHeaders = map[loc,list[HeaderAttribute]];

data Part
  = static()
  | runtime()
  ;

data Step
  = new()
  | old()
  ;
 
data Scope 
  = top(Step stp)
  | scope(Step stp,Cls cls, Scope parent)
  ; 

data Cls = class(str name, list[Field] fields);
data Field 
  = field(str name, str tipe)
  | intField(str name)
  ;
 
Spec annotate(Spec spc, NX2AlleMapping mapping) {
  ResolvedAlleRels resolvedRels = ();
  void addAlleRel(loc l, AlleRel alleRel) {
    resolvedRels[l] = alleRel;
  }
  AlleRel getAlleRel(loc l) = resolvedRels[l];
  
  ResolvedHeaders resolvedHeaders = ();
  void addHeader(loc l, list[HeaderAttribute] header) {
    resolvedHeaders[l] = header;
  }
  list[HeaderAttribute] getHeader(loc l) = resolvedHeaders[l] when l in resolvedHeaders;
  default list[HeaderAttribute] getHeader(loc l) = [];
    
  Env env = buildEnv(mapping);
  void addToEnv(str name, Step stp, AlleRel r) {
    env[<name,stp,runtime()>] = r;
  }
  
  AlleRel lookupClassRel(str class, Step stp) {
    if (<class,stp,runtime()> in env) {
      return env[<class,stp,runtime()>];
    } else if (<class,stp,static()> in env) {
      return env[<class,stp,static()>];
    } else {
      throw "Unable to find relation for class <class> in <stp> runtime or new static"; 
    }
  }

  AlleRel lookupFieldRel(str fieldName, Cls cls, Step stp) {
    if (Field fld <- cls.fields, fld.name == fieldName) {
      str fieldRel = "<cls.name>_<fieldName>";
      
      if (<fieldRel,stp,runtime()> in env) {
        return env[<fieldRel,stp,runtime()>];
      } else if (<fieldRel,stp,static()> in env) {
        return env[<fieldRel,stp,static()>];
      } else {
        throw "Unable to find relation for field <fieldRel> in <stp> runtime or new static";
      }
    } else {
      throw "Unable to find field <fieldName> for class <cls> in specification";
    }
  }    
  
  map[loc,str] types = ();
  void addType(loc l, str class) { types[l] = class; }
  str getType(loc l) = types[l] when l in types;
  default str getType(loc l) { throw "Cannot find type for loc <l>"; }
   
  map[str,Cls] classes = constructClasses(spc);
  Cls lookupCls(str clsName) = classes[clsName] when clsName in classes;
  default Cls lookupCls(str clsName) { throw "Cannot find class <clsName>"; }
  
  Cls lookupFieldCls(Cls cls, str field) = lookupCls(tipe) when /field(field, str tipe) <- cls.fields;    
  Cls lookupFieldCls(Cls cls, str field) = cls when /intField(field) <- cls.fields;    
  default Cls lookupFieldCls(Cls cls, str field) { throw "Cannot find field <field> in class <cls.name>"; }  
    
  resolve(spc, top(new()), <addAlleRel,getAlleRel,addHeader,getHeader,addToEnv,addType,getType,lookupClassRel,lookupFieldRel,lookupCls,lookupFieldCls>);
  
  //iprintln(resolvedHeaders);
  
  return annotate(spc, resolvedRels, resolvedHeaders);
}

Spec annotate(Spec spc, ResolvedAlleRels rels, ResolvedHeaders headers) {
  spc.\dynamic =visit(spc.\dynamic) {
    case Class cls => cls[@alleRel = rels[cls@\loc].name] 
    case Expr expr => expr[@header = headers[expr@\loc]][@alleRel = rels[expr@\loc].name] when (Expr)`<VarName _>` := expr
    case Expr expr => expr[@header = headers[expr@\loc]] when (Expr)`<VarName _>` !:= expr 
  }
  spc.migration =visit(spc.migration) {
    case Expr expr => expr[@header = headers[expr@\loc]][@alleRel = rels[expr@\loc].name] when (Expr)`<VarName _>` := expr   
    case Expr expr => expr[@header = headers[expr@\loc]] when (Expr)`<VarName _>` !:= expr
  }
  if ((Spec)`<StaticDef _> <DynamicDef _> <MigrationDef _> distance {<PriorityDistance* _>}` := spc) {
    spc.distance =visit(spc.distance) {
      case Expr expr => expr[@header = headers[expr@\loc]][@alleRel = rels[expr@\loc].name] when bprintln("Its here! " + expr + "<expr@\loc>"), (Expr)`<VarName _>` := expr, bprintln("Now its here" + " Alle relation: " + rels[expr@\loc].name)
      case Expr expr => expr[@header = headers[expr@\loc]] when (Expr)`<VarName _>` !:= expr
    }     
  }
  
  return spc;
}

private map[str,Cls] constructClasses(Spec spc) {
  Field constructField(FieldDecl fd) = field("<fd.fieldName>", "<tipe>") when /(Type)`<ClassName tipe>` := fd.\type;
  default Field constructField(FieldDecl fd) = intField("<fd.fieldName>");
  
  map[str,Cls] clss = ("<name>" : class("<name>", [constructField(f) | /FieldDecl f := bd]) | /(Class)`class <ClassName name> { <ClassBody bd> }` := spc);
  
  return clss;
}

private Env buildEnv(NX2AlleMapping mp) 
  = (<"<cls.name>", stp, pt> : <r.name, r.heading> | <UnaryRelation(Class cls), RelationDef r, Model md> <- mp, md != distance(), <Step stp, Part pt> := modelToStepAndPart(md))
  + (<relation, stp, pt> : <r.name, r.heading> | <NaryRelation(str relation, Class domain, RangeType range, bool isSet), RelationDef r, Model md> <- mp, md != distance(), <Step stp, Part pt> := modelToStepAndPart(md))
  ;

private tuple[Step stp, Part prt] modelToStepAndPart(newRuntime()) = <new(),runtime()>;
private tuple[Step stp, Part prt] modelToStepAndPart(newStatic()) = <new(),static()>;
private tuple[Step stp, Part prt] modelToStepAndPart(oldRuntime()) = <old(),runtime()>;
private tuple[Step stp, Part prt] modelToStepAndPart(oldStatic()) = <old(),static()>;

void resolve(Spec spc, Scope scp, Collect col) {
  resolve(spc.\dynamic, scp, col);
  resolve(spc.migration, scp, col);
  if ((Spec)`<StaticDef _> <DynamicDef _> <MigrationDef _> <DistanceDef d>` := spc) {
    resolve(d, scp, col);
  }
}
  
void resolve((DynamicDef)`runtime { <Class* cs> }`, Scope scp, Collect col) {
  for (Class c <- cs) {
    resolve(c, scp, col);
  }
}
  
void resolve((MigrationDef)`migration { <Formula* rules>}`, Scope scp, Collect col) { 
  for (Formula f <- rules) {
    resolve(f, scope(new(), col.lookupCls("Runtime"), scp), col);
  }
}

void resolve((DistanceDef)`distance { <PriorityDistance* priorities>}`, Scope scp, Collect col) { 
  for (PriorityDistance p <- priorities) {
    resolve(p, scope(new(), col.lookupCls("Runtime"), scp), col);
  }
}

void resolve(c:(Class)`class <ClassName name> { <ClassBody body>}`, Scope scp, Collect col) {
  col.addAlleRel(c@\loc, col.lookupClass("<name>", scp.stp));  
  
  resolve(body, scope(scp.stp,col.lookupCls("<name>"), scp), col);
}
  
void resolve((ClassBody)`<FieldDecl* fields> <Invariant* inv>`, Scope scp, Collect col) {
  for (Invariant i <- inv) {
    resolve(i, scp, col);
  }
}

void resolve((PriorityDistance)`<Expr expr> : <Int p>`, Scope scp, Collect col) {
  resolve (expr, scp, col);
}

void resolve((Invariant)`invariant: <Formula form>`, Scope scp, Collect col) { 
  resolve(form, scp, col);
}

void resolve((Invariant)`invariants { <Formula+ forms> }`, Scope scp, Collect col) {
  for (Formula f <- forms) {
    resolve(f, scp, col); 
  }
}

void resolve((Formula)`(<Formula form>)`, Scope scp, Collect col) { resolve(form,scp,col); }
void resolve((Formula)`not <Formula form>`, Scope scp, Collect col) { resolve(form,scp,col); }
void resolve((Formula)`some <Expr expr>`, Scope scp, Collect col) { resolve(expr,scp,col); }
void resolve((Formula)`no <Expr expr>`, Scope scp, Collect col) { resolve(expr,scp,col); }
void resolve((Formula)`one <Expr expr>`, Scope scp, Collect col) { resolve(expr,scp,col); }
void resolve((Formula)`<Expr lhs> in <Expr rhs>`, Scope scp, Collect col) { resolve(lhs,scp,col); resolve(rhs,scp,col);}
void resolve((Formula)`<Expr lhs> = <Expr rhs>`, Scope scp, Collect col) { resolve(lhs,scp,col); resolve(rhs,scp,col);}
void resolve((Formula)`<Expr lhs> != <Expr rhs>`, Scope scp, Collect col){ resolve(lhs,scp,col); resolve(rhs,scp,col);}
void resolve((Formula)`<Formula lhs> =\> <Formula rhs>`, Scope scp, Collect col) { resolve(lhs,scp,col); resolve(rhs,scp,col);}
void resolve((Formula)`<Formula lhs> \<=\> <Formula rhs>`, Scope scp, Collect col) { resolve(lhs,scp,col); resolve(rhs,scp,col);} 
void resolve((Formula)`<Formula lhs> && <Formula rhs>`, Scope scp, Collect col) { resolve(lhs,scp,col); resolve(rhs,scp,col);}
void resolve((Formula)`<Formula lhs> || <Formula rhs>`, Scope scp, Collect col) { resolve(lhs,scp,col); resolve(rhs,scp,col);}

default void resolve(Formula f, Scope scp, Collect col) { throw "Unable to resolve formula <f>"; }

private str findType((Expr)`<Expr _>.<Expr rhs>`, Collect col) = findType(rhs,col);
private str findType(ex:(Expr)`<VarName v>`, Collect col) = col.getType(ex@\loc);
private str findType(ex:(Expr)`new[<Expr rhs>]`, Collect col) = findType(rhs,col);
private str findType(ex:(Expr)`old[<Expr rhs>]`, Collect col) = findType(rhs,col);

private str findType((Expr)`(<Expr rhs>)`, Collect col) = findType(rhs,col);
private str findType((Expr)`<Expr _> ++ <Expr rhs>`, Collect col) = findType(rhs,col);
private str findType((Expr)`<Expr _> & <Expr rhs>`, Collect col) = findType(rhs,col);
private str findType((Expr)`<Expr _> -- <Expr rhs>`, Collect col) = findType(rhs,col);

private default str findType(Expr expr, Collect col) { throw "Unable to resolve the type for expression <expr>"; }

private Scope resolveQuantDecl((QuantDecl)`<VarName v>: <Expr expr>`, Scope scp, Collect col) {
  resolve(expr, scp, col);
    
  // findType() used to support only '.'-notation and variable names, but no other expressions. Why?
  str tipe = findType(expr,col);  
  scp.cls.fields += [field("<v>",tipe)];

  //UT: this is a HACK! 19-04-2019
  if ((Expr)`old[<Expr _>]` := expr) {
    col.addToEnv("<scp.cls.name>_<v>",old(),<"<v>",col.getHeader(expr@\loc)>);
  } else {  
    col.addToEnv("<scp.cls.name>_<v>",scp.stp,<"<v>",col.getHeader(expr@\loc)>);
  }
        
  return scp;
}

void resolve((Formula)`forall <{QuantDecl ","}+ decls> | <Formula form>`, Scope scp, Collect col) { 
  for (QuantDecl d <- decls) {
    scp = resolveQuantDecl(d,scp,col); // This is a BUG: resulting scopes can be different (old and new for the migration part) 
  }

  resolve(form, scp, col);
}

void resolve((Formula)`exists <{QuantDecl ","}+ decls> | <Formula form>`,  Scope scp, Collect col) { 
  for (QuantDecl d <- decls) {
    scp = resolveQuantDecl(d,scp,col);
  }

  resolve(form, scp, col);
}

void resolve((Formula)`<Expr lhs> \>= <Expr rhs>`, Scope scp, Collect col) { resolve(lhs,scp,col); resolve(rhs,scp,col);} 
void resolve((Formula)`<Expr lhs> \> <Expr rhs>`, Scope scp, Collect col) { resolve(lhs,scp,col); resolve(rhs,scp,col);} 
void resolve((Formula)`<Expr lhs> \<= <Expr rhs>`, Scope scp, Collect col) { resolve(lhs,scp,col); resolve(rhs,scp,col);} 
void resolve((Formula)`<Expr lhs> \< <Expr rhs>`, Scope scp, Collect col) { resolve(lhs,scp,col); resolve(rhs,scp,col);} 

void resolve(e:(Expr)`( <Expr expr> )`, Scope scp, Collect col) {
  resolve(expr, scp, col);
  col.addHeader(e@\loc, col.getHeader(expr@\loc)); 
}

void resolve(e:(Expr)`<VarName v>`, Scope scp, Collect col) {  
  if (col.getHeader(e@\loc) == []) {
    AlleRel r;
    try {
      // Probably a referenced field
      r = col.lookupField("<v>",scp.cls,scp.stp);
      col.addType(e@\loc,col.lookupFieldCls(scp.cls,"<v>").name);
    } catch: {
      // could also be a class ...
      r = col.lookupClass("<v>",scp.stp);
      col.addType(e@\loc,"<v>");
    }  
    
    col.addAlleRel(e@\loc,r);
    col.addHeader(e@\loc,r.header);
  }
} 

void resolve(e:(Expr)`<Literal l>`, Scope scp, Collect col) {
  col.addHeader(e@\loc,[header("val",intDom())]);
}

void resolve(e:(Expr)`<Expr lhs>.<Expr rhs>`, Scope scp, Collect col) {
  resolve(lhs,scp,col);

  Cls lhsCls = col.lookupCls(findType(lhs,col));
  resolve(rhs,scope(scp.stp,lhsCls,scp),col);
  
  list[HeaderAttribute] lHeader = col.getHeader(lhs@\loc);
  list[HeaderAttribute] rHeader = col.getHeader(rhs@\loc);
  
  list[HeaderAttribute] joinedHeader = [h | HeaderAttribute h <- lHeader, h notin rHeader] + [h | HeaderAttribute h <- rHeader, h notin lHeader];
        
  col.addHeader(e@\loc, joinedHeader); 
}

void resolve(e:(Expr)`<Expr expr> where <RestrictStat restr>`, Scope scp, Collect col) {
  resolve(expr,scp,col);
  
}

private void resolveUnionCompatibleExpr(Expr orig, Expr lhs, Expr rhs, Scope scp, Collect col) {
  resolve(lhs,scp,col);
  resolve(rhs,scp,col);
  
  list[HeaderAttribute] lhsHeader = col.getHeader(lhs@\loc);
  list[HeaderAttribute] rhsHeader = col.getHeader(rhs@\loc);
    
  if (lhsHeader != rhsHeader) {
    println("Orig expr: <orig>");
    println("LHS header: <lhsHeader>, RHS header: <rhsHeader>");
    throw ("Intersection only works on compatible classes");
  }
  
  col.addHeader(orig@\loc, lhsHeader);
}

void resolve(e:(Expr)`<Expr lhs> ++ <Expr rhs>`, Scope scp, Collect col) { resolveUnionCompatibleExpr(e,lhs,rhs,scp,col); } 
void resolve(e:(Expr)`<Expr lhs> & <Expr rhs>`, Scope scp, Collect col) { resolveUnionCompatibleExpr(e,lhs,rhs,scp,col); }
void resolve(e:(Expr)`<Expr lhs> -- <Expr rhs>`, Scope scp, Collect col) { resolveUnionCompatibleExpr(e,lhs,rhs,scp,col); }
//         )
//  > transCl:      "^" Expr
//  | reflTrans:    "*" Expr
void resolve(e:(Expr)`old[<Expr expr>]`, Scope scp, Collect col) {
  Scope newScp = scope(old(),scp.cls,scp.parent);
  resolve(expr, newScp, col); 
  
  col.addHeader(e@\loc, col.getHeader(expr@\loc));  
}

void resolve(e:(Expr)`new[<Expr expr>]`, Scope scp, Collect col) {
  Scope newScp = scope(new(),scp.cls,scp.parent);
  resolve(expr, newScp, col); 
  
  col.addHeader(e@\loc, col.getHeader(expr@\loc));
}

// UT: update for the arithmetic expressions
// The header of an arithmetic expression is the same as of its operands
void resolve(e: (Expr)`<Expr lhs> \\ <Expr rhs>`, Scope scp, Collect col) { 
  resolve(lhs,scp,col); 
  resolve(rhs,scp,col);
  col.addHeader(e@\loc, col.getHeader(lhs@\loc));
 } 
void resolve(e: (Expr)`<Expr lhs> * <Expr rhs>`, Scope scp, Collect col) { 
  resolve(lhs,scp,col); 
  resolve(rhs,scp,col);
  col.addHeader(e@\loc, col.getHeader(lhs@\loc));
} 
void resolve(e: (Expr)`<Expr lhs> + <Expr rhs>`, Scope scp, Collect col) { 
  resolve(lhs,scp,col); 
  resolve(rhs,scp,col);
  col.addHeader(e@\loc, col.getHeader(lhs@\loc)); 
 } 
void resolve(e: (Expr)`<Expr lhs> - <Expr rhs>`, Scope scp, Collect col) { 
  resolve(lhs,scp,col); 
  resolve(rhs,scp,col);
  col.addHeader(e@\loc, col.getHeader(lhs@\loc));
} 
void resolve(e: (Expr)`|<Expr expr>|`, Scope scp, Collect col) { 
  resolve(expr,scp,col);
  col.addHeader(e@\loc, col.getHeader(expr@\loc)); 
}

//
//syntax Expr
//  = count:      "count" "(" Expr ")"
//  | avg:        "avg" "(" Expr ")"
//  | min:        "min" "(" Expr ")"
//  | max:        "max" "(" Expr ")"
//  | abs:        "|" Expr "|"
//  > left ( div: Expr "\\" Expr
//         | mul: Expr "*" Expr
//         > add: Expr "+" Expr
//         | sub: Expr "-" Expr
//         )
//  ;

default void resolve(Expr expr, Scope scp, Collect col) { throw "Unable to resolve expression <expr>"; }
//syntax RestrictStat
//  = bracket "(" RestrictStat ")"
//  | RestrictExpr "=" RestrictExpr
//  ;
//
//syntax RestrictExpr
//  = QualifiedName att
//  ;
//
//syntax QualifiedName 
//  = left VarName ("." VarName)*
//  ; 
//
//syntax Literal
//  = intLit: Int
//  ;
//  
//syntax ObjectDef 
//  = Type type Atom objectName  FieldInstantiation+ fields 
//  | Type type {Atom ","}* objects 
//  ;  
//
//syntax FieldInstantiation 
//  = VarName fieldName "=" {Atom ","}* atoms
//  | VarName fieldName "=" {Int ","}* atoms
//  ;
