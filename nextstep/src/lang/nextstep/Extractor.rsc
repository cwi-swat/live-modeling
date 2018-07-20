module lang::nextstep::Extractor

import lang::nextstep::Syntax;
import lang::nextstep::Resolver;

import String;
import List;
import IO;

import ParseTree;

// intermediate model
data NXRelation 
	= UnaryRelation(Class class)
	| NaryRelation(str relation, Class domain, RangeType range, bool isSet)
	;

data RangeType 
  = class(Class c)
  | intType()
  ;

data NXBounds = bounds(NXRelation r, set[NXTuple] tup);

data NXTuple 
  = single(NXAtom a)
  | bin(NXAtom a, NXAtom b)
  ;
  
data NXAtom
  = strAt(str a)
  | intAt(int i)
  ;

data Model
 = oldStatic()
 | newStatic()
 | oldRuntime()
 | newRuntime()
 ;

alias Models = map[Model,set[NXBounds]];
	
// alternative n-ary relation: (only for originally unbounded classes, not for the fields of the bounded classes)
// An n-ary relation connects all fields of the class
// NaryRelation (Class relation, rel[str attrname, Class attrtype, bool multiple]])

Models extract(Spec spc, ResolvedTypes res) {
  list[NXRelation] rels = extractRelations(spc, res);

  map[str,NXRelation] def = ("<c.name>" : r | r:UnaryRelation(Class c) <- rels)
                          + (name : r       | r:NaryRelation(str name, _, _, _) <- rels);
  
  Models result = (oldStatic():  extractBounds({objd | ObjectDef objd <- spc.instance.oldStat}, def)) +
                  (newStatic():  extractBounds({objd | ObjectDef objd <- spc.instance.newStat}, def)) +
                  (oldRuntime(): extractBounds({objd | ObjectDef objd <- spc.instance.oldRun}, def));
  
  //println(result);
  
  return result;
}

set[NXBounds] extractBounds(set[ObjectDef] objDefs, map[str,NXRelation] rels) {
  set[NXBounds] bnds = {};
  
  set[str] declaredRels = {"<tp>" | (ObjectDef)`<Atom _> : <Type tp> ( <{FieldInstantiation ";"}* _> )` <- objDefs, "<tp>" != "Runtime"};
  
  for (str relName <- declaredRels, UnaryRelation(_) := rels[relName]) {
    set[NXTuple] tpls = {single(strAt("<a>")) | (ObjectDef)`<Atom a> : <Type tp> ( <{FieldInstantiation ";"}* _> )` <- objDefs, "<tp>" == relName};
    
    println("Rel: <relName>");
    println("Tuples: <tpls>");
    
    bnds += bounds(rels[relName], tpls);
  }
  
  return bnds;
}

// FIRST STEP: ------------------------------------------------------------------ 
// extract the intermediate model from the input file
list[NXRelation] extractRelations(Spec spec, ResolvedTypes res) {
  // A unary relation for all classes except Runtime
  list[NXRelation] class2relation(c:(Class)`class <ClassName x> {<ClassBody _>}`) 
    = [ UnaryRelation(c) ] when "<x>" != "Runtime";

  // OPT: No separate (unary) relation for the Runtime class
  default list[NXRelation] class2relation(Class _)= []; 
  
//  // An n-ary relation for each field of the class
  NXRelation field2relation (Class domain, (FieldDecl)`<VarName f> : <ClassName t>*`)
    = NaryRelation ("<f>", domain, class(res[t@\loc]), true);
  NXRelation field2relation (Class domain, (FieldDecl)`<VarName f> : <ClassName t>`)
    = NaryRelation ("<f>", domain, class(res[t@\loc]), false);
  NXRelation field2relation (Class domain, (FieldDecl)`<VarName f> : int*`)
    = NaryRelation ("<f>", domain, intType(), true); 
  NXRelation field2relation (Class domain, (FieldDecl)`<VarName f> : int`)
    = NaryRelation ("<f>", domain, intType(), false); 
  
  // A relation for each field of the class 
  list[NXRelation] fields2relations (Class class)
    = [field2relation(class, f) | FieldDecl f <- class.body.fields];
    
  // Generate relations for the class and its fields
  list[NXRelation] class2relations(Class c)
    = class2relation(c) + fields2relations(c);
   
  // extract the intermediate model from all classes of the specification
  list[NXRelation] intermModel = [ *class2relations(c) | Class c <- spec.static.classes ] 
                               + [ *class2relations(c) | Class c <- spec.\dynamic.classes ];

  return intermModel;              
}


	