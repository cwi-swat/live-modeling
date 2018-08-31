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

alias Env = map[tuple[str nxtstRel, Model m], AlleRel];

alias Collect = tuple[void (loc,AlleRel) addAlleRel, AlleRel (loc) getAlleRel, void (loc,list[HeaderAttribute]) addHeader, list[HeaderAttribute] (loc) getHeader, void (str,AlleRel) addToEnv, void (loc,str) addType, str (loc) getType, AlleRel (str) lookupClass, AlleRel (str,Cls) lookupField, Cls (str) lookupCls, Cls (Cls,str) lookupFieldCls];

alias ResolvedAlleRels = map[loc,AlleRel];
alias ResolvedFieldTypes = map[loc,str];
alias ResolvedHeaders = map[loc,list[HeaderAttribute]];
 
data Scope 
  = top()
  | scope(Cls cls, Scope parent)
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
  list[HeaderAttribute] getHeader(loc l) = resolvedHeaders[l];
    
  Env env = buildEnv(mapping);
  void addToEnv(str name, AlleRel r) {
    env[<name,newRuntime()>] = r;
  }
  
  AlleRel lookupClassRel(str class) {
    if (<class,newRuntime()> in env) {
      return env[<class,newRuntime()>];
    } else if (<class,newStatic()> in env) {
      return env[<class,newStatic()>];
    } else {
      throw "Unable to find relation for class <class> in new runtime or new static"; 
    }
  }

  AlleRel lookupFieldRel(str fieldName, Cls cls) {
    if (Field fld <- cls.fields, fld.name == fieldName) {
      str fieldRel = "<cls.name>_<fieldName>";
      
      if (<fieldRel,newRuntime()> in env) {
        return env[<fieldRel,newRuntime()>];
      } else if (<fieldRel,newStatic()> in env) {
        return env[<fieldRel,newStatic()>];
      } else {
        throw "Unable to find relation for field <fieldRel> in new runtime or new static";
      }
    } else {
      throw "Unable to find field <fieldName> for class <cls> in specification";
    }
  }    
  
  map[loc,str] types = ();
  void addType(loc l, str class) { types[l] = class; }
  str getType(loc l) = types[l];
  default str getType(loc l) { throw "Cannot find type for loc <l>"; }
   
  map[str,Cls] classes = constructClasses(spc);
  Cls lookupCls(str clsName) = classes[clsName] when clsName in classes;
  default Cls lookupCls(str clsName) { throw "Cannot find class <clsName>"; }
  
  Cls lookupFieldCls(Cls cls, str field) = lookupCls(tipe) when /field(field, str tipe) <- cls.fields;    
  Cls lookupFieldCls(Cls cls, str field) = cls when /intField(field) <- cls.fields;    
  default Cls lookupFieldCls(Cls cls, str field) { throw "Cannot find field <field> in class <cls.name>"; }  
    
  resolve(spc, top(), <addAlleRel,getAlleRel,addHeader,getHeader,addToEnv,addType,getType,lookupClassRel,lookupFieldRel,lookupCls,lookupFieldCls>);
  
  iprintln(resolvedHeaders);
  
  return annotate(spc, resolvedRels, resolvedHeaders);
}

Spec annotate(Spec spc, ResolvedAlleRels rels, ResolvedHeaders headers) {
  spc.\dynamic =visit(spc.\dynamic) {
    case Class cls => cls[@alleRel = rels[cls@\loc].name] 
    case Expr expr => expr[@header = headers[expr@\loc]][@alleRel = rels[expr@\loc].name] when (Expr)`<VarName _>` := expr
    case Expr expr => expr[@header = headers[expr@\loc]] when (Expr)`<VarName _>` !:= expr 
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
  = (<"<cls.name>", md> : <r.name, r.heading> | <UnaryRelation(Class cls), RelationDef r, Model md> <- mp)
  + (<relation, md> : <r.name, r.heading> | <NaryRelation(str relation, Class domain, RangeType range, bool isSet), RelationDef r, Model md> <- mp)
  ;

void resolve(Spec spc, Scope scp, Collect col) {
  resolve(spc.\dynamic, scp, col);
  //resolve(spc.migration, env, col);
}
  
void resolve((DynamicDef)`runtime { <Class* cs> }`, Scope scp, Collect col) {
  for (Class c <- cs) {
    resolve(c, scp, col);
  }
}
  
//void resolve((MigrationDef)`migration { <Formula* rules>}`, Env env, Collect col) { 
//  for (Formula f <- rules) {
//    annotate(f, modOnly(newRuntime()));
//  }
//}

void resolve(c:(Class)`class <ClassName name> { <ClassBody body>}`, Scope scp, Collect col) {
  col.addAlleRel(c@\loc, col.lookupClass("<name>"));  
  
  resolve(body, scope(col.lookupCls("<name>"), scp), col);
}
  
void resolve((ClassBody)`<FieldDecl* fields> <Invariant* inv>`, Scope scp, Collect col) {
  for (Invariant i <- inv) {
    resolve(i, scp, col);
  }
}

void resolve((Invariant)`invariant: <Formula form>`, Scope scp, Collect col) { 
  resolve(form, scp, col);
}

void resolve((Invariant)`invariants { <Formula+ forms> }`, Scope scp, Collect col) {
  for (Formula f <- forms) {
    resolve(f, scp, col); 
  }
}

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

private str findType((Expr)`<Expr _>.<Expr rhs>`, Collect col) = findType(rhs,col);
private str findType(ex:(Expr)`<VarName v>`, Collect col) = col.getType(ex@\loc);

private AlleRel findRel((Expr)`<Expr _>.<Expr rhs>`, Collect col) = findRel(rhs,col);
private AlleRel findRel(ex:(Expr)`<VarName v>`, Collect col) = col.getAlleRel(ex@\loc);

private Scope resolveQuantDecl((QuantDecl)`<VarName v>: <Expr expr>`, Scope scp, Collect col) {
  resolve(expr, scp, col);
    
  str tipe = findType(expr,col);
  scp.cls.fields += [field("<v>",tipe)];

  col.addToEnv("<scp.cls.name>_<v>",<"<v>",col.getHeader(expr@\loc)>);
        
  return scp;
}

void resolve((Formula)`forall <{QuantDecl ","}+ decls> | <Formula form>`, Scope scp, Collect col) { 
  for (QuantDecl d <- decls) {
    scp = resolveQuantDecl(d,scp,col);
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
  AlleRel r = col.lookupField("<v>",scp.cls);    
  
  col.addAlleRel(e@\loc,r);
  col.addHeader(e@\loc,r.header);
  col.addType(e@\loc,col.lookupFieldCls(scp.cls,"<v>").name);
} 

void resolve(e:(Expr)`<Literal l>`, Scope scp, Collect col) {
  col.addHeader(e@\loc,[header("val",intDom())]);
}

void resolve(e:(Expr)`<Expr lhs>.<Expr rhs>`, Scope scp, Collect col) {
  if ((Expr)`<VarName v>` := lhs) {
    resolve(lhs,scp,col);
    Cls lhsCls = col.lookupFieldCls(scp.cls,"<v>");
    resolve(rhs,scope(lhsCls,scp),col);
  
    AlleRel lRel = col.lookupField("<v>",scp.cls);
    list[HeaderAttribute] rHeader = col.getHeader(rhs@\loc);
    list[HeaderAttribute] joinedHeader = [h | HeaderAttribute h <- lRel.header, h notin rHeader] + [h | HeaderAttribute h <- rHeader, h notin lRel.header];
        
    col.addHeader(e@\loc, joinedHeader); 
  } else {
    throw "LHS of join is not a VarName?";
  }
}

//  > restrict:     Expr "where" RestrictStat
//  > left ( union: Expr "++" Expr
void resolve(e:(Expr)`<Expr lhs> & <Expr rhs>`, Scope scp, Collect col) {
  resolve(lhs,scp,col);
  resolve(rhs,scp,col);
  
  list[HeaderAttribute] lhsHeader = col.getHeader(lhs@\loc);
  list[HeaderAttribute] rhsHeader = col.getHeader(rhs@\loc);
  
  println(lhs);
  println(rhs);
  println("lhs header: <lhsHeader>, rhs header: <rhsHeader>");
  
  if (lhsHeader != rhsHeader) {
    throw ("Intersection only works on compatible classes");
  }
  
  col.addHeader(e@\loc,lhsHeader);
}
//         | setDif: Expr "--" Expr
//         )
//  > transCl:      "^" Expr
//  | reflTrans:    "*" Expr
//  > old: "old" //Expr
//  | new: "new" //Expr 
//  ;
//
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
//
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
