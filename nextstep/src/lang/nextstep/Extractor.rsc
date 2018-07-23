/* First step of the translation: 
 * extract the intermediate model from the input file
 * 
 * contributors: ulyanatikhonova, joukestoel
 */

module lang::nextstep::Extractor

import lang::nextstep::Syntax;
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
  ;

data Model
 = oldStatic()
 | newStatic()
 | oldRuntime()
 | newRuntime()
 ;

alias Models = map[Model, set[NXBounds]];

// Main entry	
Models extract(Spec spc, ResolvedTypes res) {
  
  // Extract (generic) relations
  list[NXRelation] rels = extractRelations(spc, res);

  map[str, NXRelation] relDefs = ("<c.name>" : r | r: UnaryRelation(Class c) <- rels)
                               + (name : r       | r: NaryRelation(str name, _, _, _) <- rels);
  
  // Extract bounds (concrete instances)
  Models result = (oldStatic():  extractBounds({objd | ObjectDef objd <- spc.instance.oldStat}, relDefs)) +
                  (newStatic():  extractBounds({objd | ObjectDef objd <- spc.instance.newStat}, relDefs)) +
                  (oldRuntime(): extractBounds({objd | ObjectDef objd <- spc.instance.oldRun}, relDefs));
  
  //println(result);
  
  return result;
}

set[NXBounds] extractBounds(set[ObjectDef] objDefs, map[str, NXRelation] rels) {
  set[NXBounds] bnds = {};
  
  // extract bounds for unary relations from objects definitions
  set[str] declaredRels = {"<tp>" | (ObjectDef)`<Atom _> : <Type tp> ( <{FieldInstantiation ";"}* _> )` <- objDefs};
  
  for (str relName <- declaredRels, UnaryRelation(_) := rels[relName]) {
    set[NXTuple] tpls = {single(strAt("<a>")) | (ObjectDef)`<Atom a> : <Type tp> ( <{FieldInstantiation ";"}* _> )` <- objDefs, "<tp>" == relName};
    
    bnds += bounds(rels[relName], tpls);
  }
  
  // extract bounds for (bi)nary relations from the fields instatiation
  set[str] declaredBins = {"<fld.fieldName>" | (ObjectDef)`<Atom _> : <Type tp> ( <{FieldInstantiation ";"}* flds> )` <- objDefs, 
                                                fld <- flds};
  
  for (str relName <- declaredBins) {//, NaryRelation(_) := rels[relName]) {
    set[NXTuple] tpls = {binary(strAt("<a>"), extractAtom(b)) | 
                          (ObjectDef)`<Atom a> : <Type _> ( <{FieldInstantiation ";"}* flds> )` <- objDefs, 
                          fld <- flds, "<fld.fieldName>" == relName, b <- fld.atoms};
    
    bnds += bounds(rels[relName], tpls);
  }                                 
  
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
   
  // Extract the intermediate model from all classes of the specification
  list[NXRelation] intermModel = [ *class2relations(c) | Class c <- spec.static.classes ] 
                               + [ *class2relations(c) | Class c <- spec.\dynamic.classes ];

  return intermModel;              
}


	