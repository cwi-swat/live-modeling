/* Generation of constraints: 
 * - structure (from Nextep structure definition to AlleAlle formulas)
 * - semantic (from Nextep invariants to AlleAlle formulas)
 * - distance definition
 * - migration (from Nextep migration rules to AlleAlle formulas)
 * 
 * contributors: ulyanatikhonova, joukestoel
 */
module lang::nextstep::ConstraintsGenerator

import lang::nextstep::Extractor;
import lang::nextstep::Syntax;
import translation::AST;                    
import translation::theories::integer::AST; 
import lang::nextstep::RelationsGenerator;
import IO;
import List;

list[AlleFormula] generateAlleConstraints(Spec spec, NX2AlleMapping relations) 
  = [singletonMultiplicityConstraint(relName, dom, "xn") | <NaryRelation(relName, dom, ran, false), _, newRuntime()> <- relations]
  + [singletonMultiplicityConstraint(relName, dom, "d") | <NaryRelation(relName, dom, ran, false), _, distance()> <- relations]
  + [typeConstraint(relName, dom, ran, "xn", relations) | <NaryRelation(relName, dom, ran, _), _, newRuntime()> <- relations];

// Get an AlleAlle relation that corresponds to the Nextep class
RelationDef lookupAlleRelation(Class class, list[Model] models, NX2AlleMapping relations) {
  list[RelationDef] result
    = [r | <UnaryRelation(class), r, model> <- relations, model <- models];
  println(result);
  return head(result);
}

// structure constraints
AlleFormula singletonMultiplicityConstraint (str relName, Class dom, str prefix)
  = universal([varDecl("x<dom.name>", relvar("<prefix>_<dom.name>"))], 
              exactlyOne(naturalJoin(relvar("x<dom.name>"), relvar("<prefix>_<relName>"))));
  
AlleFormula typeConstraint(str relName, Class dom, ran: class(Class c), str prefix, NX2AlleMapping relations)
  = subset(relvar("<prefix>_<relName>"),
           product(relvar("<prefix>_<dom.name>"), 
                   relvar(lookupAlleRelation(c, [newStatic(), newRuntime()], relations).name)));                

AlleFormula typeConstraint(str relName, Class dom, ran: intType(), str prefix, NX2AlleMapping relations)
  = subset(project(relvar("<prefix>_<relName>"), ["<dom.name>Id"]),
           relvar("<prefix>_<dom.name>"));  

  
// semantic relations


// distance


// migration rules

  