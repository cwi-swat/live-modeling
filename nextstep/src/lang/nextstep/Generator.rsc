/* Second step of the translation: 
 * translate the intermediate model into AlleAlle structures
 * 
 * contributors: ulyanatikhonova
 */

module lang::nextstep::Generator

import lang::nextstep::Extractor;
import lang::nextstep::Syntax;
import translation::AST;                    // AlleAlle
import translation::theories::integer::AST; // AlleAlle


list[RelationDef] generateAlleRelations (Models models) 
  = [nxRelation2alle(r, "po_") | r <- models[oldStatic()]]
  + [nxRelation2alle(r, "pn_") | r <- models[newStatic()]]
  + [nxRelation2alle(r, "xo_") | r <- models[oldRuntime()]];
  // + [nxRelation2alle(r, "xn_") | r <- generateNX4newruntime(models[oldRuntime()], models[newStatic()])]
  // the latter one also needs atMost() bounds instead of exact()

// Unary relation
RelationDef nxRelation2alle (NXBounds b : bounds(UnaryRelation(Class c), 
                                                  set[NXTuple] nxtuples), 
                              str prefix) 
  = relation ( prefix + "<c.name>", 
                [ header("<c.name>" + "Id", id()) ], 
                exact([tup([nxAtom2alle(t.a)]) | t <- nxtuples]) 
              );
              
// Nary relation
RelationDef nxRelation2alle (NXBounds b : bounds(NaryRelation(str relation, Class dom, RangeType ran, bool isSet), 
                                                  set[NXTuple] nxtuples), 
                              str prefix) 
  = relation ( prefix + relation, 
                [ nxType2alleHeader(dom), 
                  nxType2alleHeader(ran) ], 
                exact([ tup([nxAtom2alle(t.a), nxAtom2alle(t.b)]) | t <- nxtuples ]) 
              );

HeaderAttribute nxType2alleHeader (Class c) = header("<c.name>" + "Id", id());
HeaderAttribute nxType2alleHeader (intType c) = header(); // TODO: ???

AlleValue nxAtom2alle (NXAtom atom: strAt(str a)) = idd(toId(t.a));
// TODO: which constructor in Alle uses int ???
AlleValue nxAtom2alle (NXAtom atom: intAt(int i)) = idd(toId(t.a));  

// Generate NXRelations and NXBounds for the new run-time model
set[NXBounds] generateNX4newruntime(set[NXBounds] oldruntime, set[NXBounds] newstatic) {
  set[NXBounds] newruntime = {};
  
  return newruntime;
}
