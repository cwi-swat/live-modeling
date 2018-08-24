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

list[AlleFormula] generateAlleConstraints(Spec spc, Models models) 
  = [singletonMultiplicityConstraint(relName, dom, "xn") | bounds(NaryRelation(relName, dom, ran, false), _) <- models[newRuntime()]]
  + [singletonMultiplicityConstraint(relName, dom, "d") | bounds(NaryRelation(relName, dom, ran, false), _) <- models[newRuntime()]]
  + [typeConstraint(relName, dom, ran, "xn", spc) | bounds(NaryRelation(relName, dom, ran, isSet), _) <- models[newRuntime()]];

// naming conventions
str getClassName(Class c, Spec spec) 
  = "pn_<c.name>"
  when c <- spec.static.classes;
  
str getClassName(Class c, Spec spec) 
  = "xn_<c.name>"
  when c <- spec.\dynamic.classes;
  
str getRelName(str relName)
  = "xn_<relName>";
  
str getAttrName() = "" ;

// structure
AlleFormula singletonMultiplicityConstraint (str relName, Class dom, str prefix)
  = universal([varDecl("x<dom.name>", relvar("<prefix>_<dom.name>"))], 
              exactlyOne(naturalJoin(relvar("x<dom.name>"), relvar("<prefix>_<relName>"))));
  
AlleFormula typeConstraint(str relName, Class dom, ran: class(Class c), str prefix, Spec spec)
  = subset(relvar("<prefix>_<relName>"),
           product(relvar("<prefix>_<dom.name>"), 
                   relvar("pn_<c.name>")))
    when c <- spec.static.classes; 
                    
AlleFormula typeConstraint(str relName, Class dom, ran: class(Class c), str prefix, Spec spec)
  = subset(relvar("<prefix>_<relName>"),
           product(relvar("<prefix>_<dom.name>"), 
                   relvar("<prefix>_<c.name>")))
    when c <- spec.\dynamic.classes;  

AlleFormula typeConstraint(str relName, Class dom, ran: intType(), str prefix, Spec spc)
  = subset(project(relvar("<prefix>_<relName>"), ["<dom.name>Id"]),
           relvar("<prefix>_<dom.name>"));  

  
// semantic relations


// distance


// migration rules

  