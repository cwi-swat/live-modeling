/* Second step of the translation: 
 * translate the intermediate model into AlleAlle structures
 * 
 * contributors: ulyanatikhonova, joukestoel
 */

module lang::nextstep::RelationsGenerator

import lang::nextstep::Extractor;
import lang::nextstep::Syntax;
import translation::AST;                    // AlleAlle
import translation::theories::integer::AST; // AlleAlle

import String;
import IO;

Models addNewRuntime (Models models) 
  = models +
    (newRuntime(): generateNX4NewRuntime(models[oldRuntime()], models[oldStatic()], models[newStatic()]));  

list[RelationDef] generateAlleRelations (Models models) 
  = [genFixedBoundsRel(r, "po") | r <- models[oldStatic()]]
  + [genFixedBoundsRel(r, "pn") | r <- models[newStatic()]]
  + [genFixedBoundsRel(r, "xo") | r <- models[oldRuntime()]]
  + [genUpperBoundsRel(r, "xn") | r <- models[newRuntime()]]
  + [genDistanceRel(r, "d") | r <- models[newRuntime()]];

// Unary relation
RelationDef genFixedBoundsRel (bounds(UnaryRelation(Class c), set[NXTuple] nxtuples), str prefix) 
  = relation ("<prefix>_<c.name>", [nxType2alleHeader(c)], 
              exact([tup([nxAtom2alle(a)]) | single(NXAtom a) <- nxtuples]));

RelationDef genUpperBoundsRel (bounds(UnaryRelation(Class c), set[NXTuple] nxtuples), str prefix) 
  = relation ("<prefix>_<c.name>", [nxType2alleHeader(c)], 
              atMost([tup([nxAtom2alle(a)]) | single(NXAtom a) <- nxtuples]));

RelationDef genDistanceRel (b:bounds(UnaryRelation(Class _), set[NXTuple] _), str prefix) 
  = genUpperBoundsRel(b, prefix);
              
// Nary relation
RelationDef genFixedBoundsRel (bounds(NaryRelation(str relName, Class dom, RangeType ran, bool isSet), set[NXTuple] nxtuples), str prefix) 
  = relation ("<prefix>_<relName>", [nxType2alleHeader(dom), nxType2alleHeader(ran)], 
               exact([ tup([nxAtom2alle(t.a), nxAtom2alle(t.b)]) | t <- nxtuples ]));

RelationDef genUpperBoundsRel (bounds(NaryRelation(str relName, Class dom, RangeType ran, bool isSet), set[NXTuple] nxtuples), str prefix) 
  = relation ("<prefix>_<relName>", [nxType2alleHeader(dom), nxType2alleHeader(ran)], 
               atMost([ tup([nxAtom2alle(t.a), nxAtom2alle(t.b)]) | t <- nxtuples ]));

RelationDef genDistanceRel (b:bounds(NaryRelation(str _, Class _, class(Class _), bool _), set[NXTuple] _), str prefix) 
  = genUpperBoundsRel(b, prefix);

RelationDef genDistanceRel (b:bounds(NaryRelation(str relName, Class dom, intType(), bool _), set[NXTuple] tups), str prefix) 
  = relation ("<prefix>_<relName>", [nxType2alleHeader(dom), header("delta", intDom())], 
               atMost([ tup([nxAtom2alle(t.a), nxAtom2alle(t.b)]) | t <- tups ]));

HeaderAttribute nxType2alleHeader (Class c)        = header("<c.name>Id", id());
HeaderAttribute nxType2alleHeader (class(Class c)) = header("<c.name>Id", id());
HeaderAttribute nxType2alleHeader (intType())      = header("val", intDom());

AlleValue nxAtom2alle (strAt(str a)) = idd(a);
AlleValue nxAtom2alle (intAt(int i)) = alleLit(translation::theories::integer::AST::intLit(i));  
AlleValue nxAtom2alle (intHole()) = hole();  

// Generate NXRelations and NXBounds for the new run-time model
set[NXBounds] generateNX4NewRuntime(set[NXBounds] oldRuntime, set[NXBounds] oldStatic, set[NXBounds] newStatic) {  
  // General idea
  // 1) All classes defined in the runtime, add n (n = 2) extra atoms to the list 
  // 2) All fields in runtime of types defined in the static parts (both old and new) calculate the 'absolute' atoms that are assigned to this type
  //    Use these 'absolute' atoms to calculate new cartesian products

  rel[Class, NXTuple] getUnaryRelsAndTuples(set[NXBounds] allRels) = {<c,t> | bounds(UnaryRelation(Class c), set[NXTuple] tups) <- allRels, NXTuple t <- tups};

  rel[Class, NXTuple] absoluteStaticTups = getUnaryRelsAndTuples(oldStatic) + getUnaryRelsAndTuples(newStatic);
  rel[Class, NXTuple] oldRuntimeTups = getUnaryRelsAndTuples(oldRuntime);  
      
  // Step 1: Calculate the bounds of the new runtime unary relations (the defined classes)
  int n = 2; // extra atoms per defined class in the runtime
  rel[Class, NXTuple] newRuntimeUnaries = oldRuntimeTups + {<c, single(strAt(toLowerCase("<c.name>_new_<i+1>")))> | bounds(UnaryRelation(Class c), _) <- oldRuntime, "<c.name>" != "Runtime", int i <- [0..n]}; 
   
  // Step 2: Calculate the bounds of the new runtime binary relations (the defined fiels)
  // The new bounds are the cartesian product of the bounds of the underlying unary relations
  
  // First do the classes:
  map[str, tuple[Class,Class]] classLookup = (fieldName : <dom,range> | bounds(NaryRelation(str fieldName, Class dom, class(Class range), bool isSet), _) <- oldRuntime);
  
  set[NXTuple] lookup(Class c) = (newRuntimeUnaries + absoluteStaticTups)[c];
  
  rel[str, NXTuple] newRuntimeBinaries = {<fieldName, binary(d,r)> | str fieldName <- classLookup, <Class dom, Class range> := classLookup[fieldName], single(NXAtom d) <- lookup(dom), single(NXAtom r) <- lookup(range)};
   
  // Now do the integer fields:
  rel[str, NXTuple] newRuntimeBinaryIntFields = {<fieldName, binary(d,intHole())> | bounds(NaryRelation(str fieldName, Class dom, intType(), _), _) <- oldRuntime, single(NXAtom d) <- lookup(dom)}; 
  
  // Last step, convert everything to NXBounds
  Class findDomain(str binRel) = dom when /bounds(NaryRelation(str r, Class dom, _, _), _) := oldRuntime, r == binRel; 
  RangeType findRange(str binRel) = range when /bounds(NaryRelation(str r, _, range:class(_), _), _) := oldRuntime, r == binRel; 
  bool findMultiplicity(str binRel) = isSet when /bounds(NaryRelation(str r, _, _, bool isSet), _) := oldRuntime, r == binRel; 
  
  set[NXBounds] newRuntime = {bounds(UnaryRelation(c), newRuntimeUnaries[c]) | Class c <- newRuntimeUnaries<0>}
                           + {bounds(NaryRelation(fieldName, findDomain(fieldName), findRange(fieldName), findMultiplicity(fieldName)), newRuntimeBinaries[fieldName]) | str fieldName <- newRuntimeBinaries<0>}
                           + {bounds(NaryRelation(fieldName, findDomain(fieldName), intType(), false), newRuntimeBinaryIntFields[fieldName]) | str fieldName <- newRuntimeBinaryIntFields<0>};

  return newRuntime;
}
