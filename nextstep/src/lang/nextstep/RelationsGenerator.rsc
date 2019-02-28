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
import Map;

alias NX2AlleMapping = rel[NXRelation nx, RelationDef alle, Model model];

Models addNewRuntime (Models models) 
  = models 
  + (newRuntime(): generateNX4NewRuntime(models[oldRuntime()], models[oldStatic()], models[newStatic()]))
  + (distance(): generateNX4NewRuntime(models[oldRuntime()], models[oldStatic()], models[newStatic()]));  

NX2AlleMapping generateAlleRelations (Models models) 
  = {<r, genFixedBoundsRel(r, t, "po"), oldStatic()> | bounds(r, t) <- models[oldStatic()]}
  + {<r, genFixedBoundsRel(r, t, "pn"), newStatic()> | bounds(r, t) <- models[newStatic()]}
  + {<r, genFixedBoundsRel(r, t, "xo"), oldRuntime()> | bounds(r, t) <- models[oldRuntime()]}
  + {<r, genUpperBoundsRel(r, t, "xn"), newRuntime()> | bounds(r, t) <- models[newRuntime()], !(UnaryRelation(Class c) := r && "<c.name>" == "Runtime")}
  + {<r, genFixedBoundsRel(r, t, "xn"), newRuntime()> | bounds(r, t) <- models[newRuntime()], (UnaryRelation(Class c) := r && "<c.name>" == "Runtime")}
  + {<r, genDistanceRel(r, t, "d"), distance()> | bounds(r, t) <- models[distance()]};

// Unary relation
RelationDef genFixedBoundsRel (UnaryRelation(Class c), set[NXTuple] nxtuples, str prefix) 
  = relation ("<prefix>_<c.name>", [nxType2alleHeader(c)], 
              exact([tup([nxAtom2alle(a)]) | single(NXAtom a) <- nxtuples]));

RelationDef genUpperBoundsRel (UnaryRelation(Class c), set[NXTuple] nxtuples, str prefix) 
  = relation ("<prefix>_<c.name>", [nxType2alleHeader(c)], 
              atMost([tup([nxAtom2alle(a)]) | single(NXAtom a) <- nxtuples]));

RelationDef genDistanceRel (r:UnaryRelation(Class c), set[NXTuple] nxtuples, str prefix) 
  = genUpperBoundsRel(r, nxtuples, prefix);
              
// Nary relation
RelationDef genFixedBoundsRel (NaryRelation(str relName, Class dom, RangeType ran, bool isSet), set[NXTuple] nxtuples, str prefix) 
  = relation ("<prefix>_<relName>", [nxType2alleHeader(dom), nxType2alleHeader(ran)], 
               exact([ tup([nxAtom2alle(t.a), nxAtom2alle(t.b)]) | t <- nxtuples ]));

RelationDef genUpperBoundsRel (NaryRelation(str relName, Class dom, RangeType ran, bool isSet), set[NXTuple] nxtuples, str prefix) 
  = relation ("<prefix>_<relName>", [nxType2alleHeader(dom), nxType2alleHeader(ran)], 
               atMost([ tup([nxAtom2alle(t.a), nxAtom2alle(t.b)]) | t <- nxtuples ]));

RelationDef genDistanceRel (r: NaryRelation(str _, Class _, class(Class _), bool _), set[NXTuple] nxtuples, str prefix) 
  = genUpperBoundsRel(r, nxtuples, prefix);

RelationDef genDistanceRel (NaryRelation(str relName, Class dom, intType(), bool _), set[NXTuple] tups, str prefix) 
  = relation ("<prefix>_<relName>", [nxType2alleHeader(dom), header("delta", intDom())], 
               atMost([ tup([nxAtom2alle(t.a), nxAtom2alle(t.b)]) | t <- tups ]));

HeaderAttribute nxType2alleHeader (Class c)        = header("<c.name>Id", id());
HeaderAttribute nxType2alleHeader (class(Class c)) = header("<c.name>Id", id());
HeaderAttribute nxType2alleHeader (intType())      = header("val", intDom());

AlleValue nxAtom2alle (strAt(str a)) = idd(a);
AlleValue nxAtom2alle (intAt(int i)) = alleLit(translation::theories::integer::AST::intLit(i));  
AlleValue nxAtom2alle (intHole()) = hole();  

@memo
Class findDomain(set[NXBounds] runtime, str binRel) = dom when bounds(NaryRelation(str r, Class dom, _, _), _) <- runtime, r == binRel; 
@memo
RangeType findRange(set[NXBounds] runtime, str binRel) = range when bounds(NaryRelation(str r, _, range:class(_), _), _) <- runtime, r == binRel; 
@memo
bool findMultiplicity(set[NXBounds] runtime, str binRel) = isSet when bounds(NaryRelation(str r, _, _, bool isSet), _) <- runtime, r == binRel; 


// Generate NXRelations and NXBounds for the new run-time model
set[NXBounds] generateNX4NewRuntime(set[NXBounds] oldRuntime, set[NXBounds] oldStatic, set[NXBounds] newStatic) {  
  
  println("   debug (binary) input");
  println( {"<r>"| bounds(NaryRelation(str r, Class domain, RangeType range, bool isSet), _) <- oldRuntime} );
  //println( {"<c.name >"| bounds(UnaryRelation(Class c),  _) <- oldRuntime} );
  println("   debug (unary static) input");
  println( {"<c.name >"| bounds(UnaryRelation(Class c),  _) <- oldStatic + newStatic} );
  println();
  
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
  
  // debug: problem is between here and below 26.02.2019
  println("   debug 0");
  //println([b | b <- domain(classLookup)]);
  println(["<f>: <d.name> - <r.name>" | f <- classLookup, <Class d, Class r> := classLookup[f]]);
  println(["<c.name>" | <Class c, _> <- newRuntimeUnaries + absoluteStaticTups]); // <- no Variable here!
  println();
  
  
  set[NXTuple] lookup(Class c) = (newRuntimeUnaries + absoluteStaticTups)[c];
  // cartesian product binary(d,r)
  rel[str, NXTuple] newRuntimeBinaries = {<fieldName, binary(d,r)> | str fieldName <- classLookup, <Class dom, Class range> := classLookup[fieldName], single(NXAtom d) <- lookup(dom), single(NXAtom r) <- lookup(range)};
   
  // debug: problem shows up here 26.02.2019
  println("   debug 1");
  println([b<0> | b <- newRuntimeBinaries]);   
   
  // Now do the integer fields:
  rel[str, NXTuple] newRuntimeBinaryIntFields = {<fieldName, binary(d,intHole())> | bounds(NaryRelation(str fieldName, Class dom, intType(), _), _) <- oldRuntime, single(NXAtom d) <- lookup(dom)}; 
  
  // Last step, convert everything to NXBounds
  // and add empty relations (with empty bounds) <- new!!! 28.02.2018  
  set[NXBounds] newRuntime = {bounds(UnaryRelation(c), newRuntimeUnaries[c]) | Class c <- newRuntimeUnaries<0>}
                           + {bounds(NaryRelation(fieldName, findDomain(oldRuntime, fieldName), findRange(oldRuntime, fieldName), findMultiplicity(oldRuntime, fieldName)), newRuntimeBinaries[fieldName]) | str fieldName <- newRuntimeBinaries<0>}
                           + {bounds(NaryRelation(fieldName, findDomain(oldRuntime, fieldName), intType(), false), newRuntimeBinaryIntFields[fieldName]) | str fieldName <- newRuntimeBinaryIntFields<0>}
                           + {};

	// debug: here is a problem 26.02.2019
	println("   debug 2");
	println(["<name>" | b <- newRuntime, NaryRelation(str name, _, _, _) := b.r]);
	println(["<b.r.class.name>" | b <- newRuntime, UnaryRelation(_) := b.r]);

  return newRuntime;
}
