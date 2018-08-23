/* Generation of constraints: 
 * - structure (from Nextep structure definition to AlleAlle formulas)
 * - semantic (from Nextep invariants to AlleAlle formulas)
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

list[AlleFormula] generateAlleConstraints(Spec spc, Models models) 
  = [singletonMultiplicityConstraint(relName, dom, ran, "xn") | bounds(NaryRelation(relName, dom, ran, false), _) <- models[newRuntime()]]
  + [singletonMultiplicityConstraint(relName, dom, ran, "d") | bounds(NaryRelation(relName, dom, ran, false), _) <- models[newRuntime()]];


AlleFormula singletonMultiplicityConstraint (str relName, Class dom, RangeType ran, str prefix)
  = universal([varDecl("x<dom.name>", relvar("<prefix>_<dom.name>"))], 
              exactlyOne(naturalJoin(relvar("x<dom.name>"), relvar("<prefix>_<relName>"))));
  

  