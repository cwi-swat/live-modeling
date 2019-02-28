/* First step of the translation: 
 * extract the intermediate model from the input file
 * 
 * contributors: ulyanatikhonova, joukestoel
 */

module lang::nextstep::Extractor

import lang::nextstep::Syntax;
import lang::nextstep::InstanceSyntax;
import lang::nextstep::Resolver;

import String;
import List;
import IO;
import ParseTree;

/* The structure for the intermediate model */
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
  | binary(NXAtom a, NXAtom b)
  ;
  
data NXAtom
  = strAt(str a)
  | intAt(int i)
  | intHole()
  ;

data Model
 = oldStatic()
 | newStatic()
 | oldRuntime()
 | newRuntime()
 | distance()
 ;

alias Models = map[Model, set[NXBounds]];

// Main entry	
Models extract(Spec spc, ResolvedTypes res, NextepInstance inst) {
  
  // Extract (generic) relations
  list[NXRelation] rels = extractRelations(spc, res);
  
  println("   debug generic part");
  println([ "<c.name>"| UnaryRelation(Class c) <- rels]);
  println();

  map[str, NXRelation] relDefs = ("<c.name>" : r | r: UnaryRelation(Class c) <- rels)
                               + (name : r       | r: NaryRelation(str name, _, _, _) <- rels);
  
  // Extract bounds (concrete instances)
  Models result = (oldStatic():  extractBounds({objd | ObjectDef objd <- inst.oldStat}, relDefs)) +
                  (newStatic():  extractBounds({objd | ObjectDef objd <- inst.newStat}, relDefs)) +
                  (oldRuntime(): extractBounds({objd | ObjectDef objd <- inst.oldRun}, relDefs));
  
  return result;
}

set[NXBounds] extractBounds(set[ObjectDef] objDefs, map[str, NXRelation] rels) {
  set[NXBounds] bnds = {};
  
  // extract bounds for unary relations from objects definitions (including those without fields)
  set[str] declaredRels = {"<tp>" | (ObjectDef)`<Type tp> <Atom _> <FieldInstantiation+ _>` <- objDefs}
                        + {"<tp>" | (ObjectDef)`<Type tp> <{Atom ","}* _>;` <- objDefs};
  
  for (str relName <- declaredRels, UnaryRelation(_) := rels[relName]) {
    set[NXTuple] tpls = {single(strAt("<a>")) | (ObjectDef)`<Type tp> <Atom a> <FieldInstantiation+ _>` <- objDefs, "<tp>" == relName}
                      + {single(strAt("<a>")) | (ObjectDef)`<Type tp> <{Atom ","}* objs>;` <- objDefs, "<tp>" == relName, a <- objs};
    
    bnds += bounds(rels[relName], tpls);
  } 
  
  // extract bounds for (bi)nary relations from the fields instatiation
  set[str] declaredBins = {"<tp>_<fld.fieldName>" | (ObjectDef)`<Type tp> <Atom _> <FieldInstantiation+ flds>` <- objDefs, 
                                                fld <- flds};
  println(rels<0>);
  for (str relName <- declaredBins) {//, NaryRelation(_) := rels[relName]) {
    set[NXTuple] tpls = {binary(strAt("<a>"), extractAtom(b)) | 
                          (ObjectDef)`<Type tp> <Atom a> <FieldInstantiation+ flds>` <- objDefs, 
                          fld <- flds, (FieldInstantiation)`<VarName _> = [ ]` !:= fld, 
                          "<tp>_<fld.fieldName>" == relName, b <- fld.atoms};
    
    bnds += bounds(rels[relName], tpls);
  }
  
  // Deprivated!! add relations without object or field definitions (without instances): with an empty set of bounds
  //bnds += {bounds(rels[relName], {}) | relName <- rels, relName notin (declaredRels + declaredBins)};                              
  
  return bnds;
}

NXAtom extractAtom(Atom a) = strAt("<a>");
NXAtom extractAtom(Int i) = intAt(toInt("<i>"));

// Extract the generic structure of the static and run-time models
list[NXRelation] extractRelations(Spec spec, ResolvedTypes res) {
  // A unary relation for all classes 
  list[NXRelation] class2relation(c:(Class)`class <ClassName x> {<ClassBody _>}`) 
    = [ UnaryRelation(c) ];

  // An n-ary relation for each field of the class
  NXRelation field2relation (Class domain, (FieldDecl)`<VarName f> : <ClassName t>*`)
    = NaryRelation ("<domain.name>_<f>", domain, class(res[t@\loc]), true);
  NXRelation field2relation (Class domain, (FieldDecl)`<VarName f> : <ClassName t>`)
    = NaryRelation ("<domain.name>_<f>", domain, class(res[t@\loc]), false);
  NXRelation field2relation (Class domain, (FieldDecl)`<VarName f> : int*`)
    = NaryRelation ("<domain.name>_<f>", domain, intType(), true); 
  NXRelation field2relation (Class domain, (FieldDecl)`<VarName f> : int`)
    = NaryRelation ("<domain.name>_<f>", domain, intType(), false); 
  
  // A relation for each field of the class 
  list[NXRelation] fields2relations (Class class)
    = [field2relation(class, f) | FieldDecl f <- class.body.fields];
    
  // Generate relations for the class and its fields
  list[NXRelation] class2relations(Class c)
    = class2relation(c) + fields2relations(c);
   
  // Extract the intermediate model from all classes of the specification
  list[NXRelation] intermModel = [ *class2relations(c) | Class c <- spec.static.classes ] 
                               + [ *class2relations(c) | Class c <- spec.\dynamic.classes ];

  return intermModel;              
}