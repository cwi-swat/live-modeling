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
import lang::nextstep::Annotator;
import IO;
import List;
import Map;
import String;
import ParseTree;
import util::Maybe;

//anno str Expr@alleRel;
//anno str Class@alleRel;


list[AlleFormula] generateAlleConstraints(Spec spec, NX2AlleMapping relations) 
  = [singletonMultiplicityConstraint(relName, dom, "xn") | <NaryRelation(relName, dom, ran, false), _, newRuntime()> <- relations]
  //+ [singletonMultiplicityConstraint(relName, dom, "d") | <NaryRelation(relName, dom, ran, false), _, distance()> <- relations]
  + [typeConstraint(relName, dom, ran, "xn", relations) | <NaryRelation(relName, dom, ran, _), _, newRuntime()> <- relations]
  + [distanceDeclaration(nxDom, d, xo, xn) | 
      <NaryRelation(relName, _, nxDom, _), d, distance()> <- relations,
      <NaryRelation(relName, _, nxDom, _), xo, oldRuntime()> <- relations,
      <NaryRelation(relName, _, nxDom, _), xn, newRuntime()> <- relations]
  + [distanceDeclaration(class(nxDom), d, xo, xn) | 
      <UnaryRelation(nxDom), d, distance()> <- relations,
      <UnaryRelation(nxDom), xo, oldRuntime()> <- relations,
      <UnaryRelation(nxDom), xn, newRuntime()> <- relations]
  ;

// Get an AlleAlle relation that corresponds to the Nextep class
RelationDef lookupAlleRelation(Class class, list[Model] models, NX2AlleMapping relations) {
  list[RelationDef] result
    = [r | <UnaryRelation(class), r, model> <- relations, model <- models];
  println(result);
  return head(result);
}

// STRUCTURE CONSTRAINTS
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

  
// SEMANTIC RELATIONS

list[AlleFormula] translate(Spec spc) = translate(spc.\dynamic) + translate(spc.migration);
list[AlleFormula] translate((DynamicDef)`runtime { <Class* cs> }`) = [*translate(c) | Class c <- cs];
list[AlleFormula] translate((MigrationDef)`migration { <Formula* rules>}`) =  [translate(f) | Formula f <- rules];
list[AlleFormula] translate(c:(Class)`class <ClassName _> { <ClassBody body>}`) = translate(body);  
list[AlleFormula] translate((ClassBody)`<FieldDecl* _> <Invariant* inv>`) = [*translate(i) | Invariant i <- inv];
list[AlleFormula] translate((Invariant)`invariant: <Formula form>`) = [translate(form)];  
list[AlleFormula] translate((Invariant)`invariants { <Formula+ forms> }`) = [translate(f) | Formula f <- forms];
 
AlleFormula translate((Formula)`( <Formula form> )`) = translate(form);
AlleFormula translate((Formula)`not <Formula form>`) = negation(translate(form));
AlleFormula translate((Formula)`some <Expr expr>`) = nonEmpty(translate(expr));
AlleFormula translate((Formula)`no <Expr expr>`) = empty(translate(expr));
AlleFormula translate((Formula)`one <Expr expr>`) = exactlyOne(translate(expr));
AlleFormula translate((Formula)`<Expr lhs> in <Expr rhs>`) = subset(translate(lhs), translate(rhs)); 
AlleFormula translate((Formula)`<Expr lhs> = <Expr rhs>`) = equal(translate(lhs), translate(rhs)); 
AlleFormula translate((Formula)`<Expr lhs> != <Expr rhs>`) = inequal(translate(lhs), translate(rhs)); 
AlleFormula translate((Formula)`<Formula lhs> =\> <Formula rhs>`) = implication(translate(lhs), translate(rhs));  
AlleFormula translate((Formula)`<Formula lhs> \<=\> <Formula rhs>`) = equality(translate(lhs), translate(rhs));  
AlleFormula translate((Formula)`<Formula lhs> && <Formula rhs>`) = conjunction(translate(lhs), translate(rhs)); 
AlleFormula translate((Formula)`<Formula lhs> || <Formula rhs>`) = disjunction(translate(lhs), translate(rhs)); 
AlleFormula translate((Formula)`forall <{QuantDecl ","}+ decls> | <Formula form>`) 
  = universal([varDecl("<v>", translate(expr)) | (QuantDecl)`<VarName v> : <Expr expr>` <- decls], 
              translate(form));
AlleFormula translate(f:(Formula)`exists <{QuantDecl ","}+ decls> | <Formula form>`) 
  = existential([varDecl("<v>", translate(expr)) | (QuantDecl)`<VarName v> : <Expr expr>` <- decls], 
              translate(form));

AlleExpr translate((Expr)`( <Expr ex> )`) = translate(ex);
AlleExpr translate(ex:(Expr)`<VarName v>`) = relvar(ex@alleRel);  
AlleExpr translate((Expr)`<Literal l>`) = translate(l);
AlleExpr translate(ex:(Expr)`<Expr lhs>.<Expr rhs>`) 
  = project(naturalJoin(translate(lhs), translate(rhs)), [a.name| a <- ex@header]);

AlleExpr translate(ex:(Expr)`old[<Expr rhs>]`) = translate(rhs);
AlleExpr translate(ex:(Expr)`new[<Expr rhs>]`) = translate(rhs);

AlleExpr translate((Expr)`<Expr lhs> ++ <Expr rhs>`) = union(translate(lhs), translate(rhs));
AlleExpr translate((Expr)`<Expr lhs> & <Expr rhs>`) = intersection(translate(lhs), translate(rhs));
AlleExpr translate((Expr)`<Expr lhs> -- <Expr rhs>`) = difference(translate(lhs), translate(rhs));
//AlleExpr translate((Expr)`^<Expr ex>`) = closure(, translate(ex));
//AlleExpr translate((Expr)`*<Expr ex> `) = reflexClosure(, translate(ex));

AlleExpr translate((Expr)`<Expr expr> where (<RestrictExpr lhs> = <RestrictExpr rhs>)`) 
  = project( select( naturalJoin(translate(expr), 
                                  product(rename(translate(lhs), [rename(v1, head(lhs@header))]), 
                                          rename(translate(rhs), [rename(v2, head(rhs@header))]))),  
                     equal(att(v1), att(v2))),           
             [a.name| a <- expr@header])
    when v1 := "val<lhs@\loc.offset>", v2 := "val<rhs@\loc.offset>";

AlleLiteral translate((Literal)`<Int i>`) = intLit(toInt("<i>"));
CriteriaExpr translateConstraintExpr(Literal l) = litt(translate(l));

//	ARITHMETICS

//AlleFormula translate((Formula)`<Expr lhs> \>= <Literal rhs>`) =
//   nonEmpty(select(translate(lhs), 
//            gte(att("val"), translateConstraintExpr(rhs))));
//AlleFormula translate((Formula)`<Expr lhs> \>= <Expr rhs>`) =
//   nonEmpty(select(product(rename(translate(lhs), [rename(v1, "val")]), 
//                           rename(translate(rhs), [rename(v2, "val")])),
//            gte(att(v1), att(v2))))
//   when v1 := "val<lhs@\loc.offset>", v2 := "val<rhs@\loc.offset>";
//
//AlleFormula translate((Formula)`<Expr lhs> \> <Literal rhs>`) = 
//  nonEmpty(select(translate(lhs), 
//            gt(att("val"), translateConstraintExpr(rhs))));
//AlleFormula translate((Formula)`<Expr lhs> \> <Expr rhs>`) = 
//   nonEmpty(select(product(rename(translate(lhs), [rename(v1, "val")]), 
//                           rename(translate(rhs), [rename(v2, "val")])),
//            gt(att(v1), att(v2))))
//   when v1 := "val<lhs@\loc.offset>", v2 := "val<rhs@\loc.offset>";
//
//AlleFormula translate((Formula)`<Expr lhs> \<= <Literal rhs>`) = 
//  nonEmpty(select(translate(lhs), 
//            lte(att("val"), translateConstraintExpr(rhs))));
//AlleFormula translate((Formula)`<Expr lhs> \<= <Expr rhs>`) = 
//   nonEmpty(select(product(rename(translate(lhs), [rename(v1, "val")]), 
//                           rename(translate(rhs), [rename(v2, "val")])),
//            lte(att(v1), att(v2))))
//   when v1 := "val<lhs@\loc.offset>", v2 := "val<rhs@\loc.offset>";
//
//AlleFormula translate((Formula)`<Expr lhs> \< <Literal rhs>`) = 
//  nonEmpty(select(translate(lhs), 
//            lt(att("val"), translateConstraintExpr(rhs))));
//AlleFormula translate((Formula)`<Expr lhs> \< <Expr rhs>`) = 
//   nonEmpty(select(product(rename(translate(lhs), [rename(v1, "val")]), 
//                           rename(translate(rhs), [rename(v2, "val")])),
//            lt(att(v1), att(v2))))
//   when v1 := "val<lhs@\loc.offset>", v2 := "val<rhs@\loc.offset>";


// new ARITHMETICS 

// Data type for unfolding arithmetic expressions
data ArithmExpr = arithmExpr(map[str, AlleExpr] renaming, CriteriaExpr alleExpr);

// Translation of formulas
AlleFormula translate((Formula)`<Expr lhs> \>= <Expr rhs>`) {
	l = translateArithmeticExpr(lhs);
	r = translateArithmeticExpr(rhs);
		
	domainExpr = buildProduct([rename(operand, [rename(v, "val")]) | <v, operand> <- toList(l.renaming + r.renaming)]);
		
	return nonEmpty(select(domainExpr , gte(l.alleExpr, r.alleExpr)));
}

AlleFormula translate((Formula)`<Expr lhs> \> <Expr rhs>`) {
	l = translateArithmeticExpr(lhs);
	r = translateArithmeticExpr(rhs);
		
	domainExpr = buildProduct([rename(operand, [rename(v, "val")]) | <v, operand> <- toList(l.renaming + r.renaming)]);
		
	return nonEmpty(select(domainExpr , gt(l.alleExpr, r.alleExpr)));
}

AlleFormula translate((Formula)`<Expr lhs> \<= <Expr rhs>`) {
	l = translateArithmeticExpr(lhs);
	r = translateArithmeticExpr(rhs);
		
	domainExpr = buildProduct([rename(operand, [rename(v, "val")]) | <v, operand> <- toList(l.renaming + r.renaming)]);
		
	return nonEmpty(select(domainExpr , lte(l.alleExpr, r.alleExpr)));
}

AlleFormula translate((Formula)`<Expr lhs> \< <Expr rhs>`) {
	l = translateArithmeticExpr(lhs);
	r = translateArithmeticExpr(rhs);
		
	domainExpr = buildProduct([rename(operand, [rename(v, "val")]) | <v, operand> <- toList(l.renaming + r.renaming)]);
		
	return nonEmpty(select(domainExpr , lt(l.alleExpr, r.alleExpr)));
}

AlleExpr buildProduct(list[AlleExpr] operands)
	= product(head(operands), buildProduct(operands[1..]))
	when size(operands) > 1;
	
AlleExpr buildProduct(list[AlleExpr] operands)
	= head(operands)
	when size(operands) <= 1;	


// Translation of expressions: recursive descend along a tree with arithmetic expressions

// Nodes of a tree with arithmetic expressions: +, -, *, \\, ||, ()
ArithmExpr translateArithmeticExpr((Expr)`<Expr lhs> + <Expr rhs>`) {
	l = translateArithmeticExpr(lhs);
	r = translateArithmeticExpr(rhs);
	return arithmExpr(l.renaming + r.renaming, add(l.alleExpr, r.alleExpr));
}

ArithmExpr translateArithmeticExpr((Expr)`<Expr lhs> - <Expr rhs>`) {
	l = translateArithmeticExpr(lhs);
	r = translateArithmeticExpr(rhs);
	return arithmExpr(l.renaming + r.renaming, sub(l.alleExpr, r.alleExpr));
}

ArithmExpr translateArithmeticExpr((Expr)`<Expr lhs> * <Expr rhs>`) {
	l = translateArithmeticExpr(lhs);
	r = translateArithmeticExpr(rhs);
	return arithmExpr(l.renaming + r.renaming, mult(l.alleExpr, r.alleExpr));
}

ArithmExpr translateArithmeticExpr((Expr)`<Expr lhs> \\ <Expr rhs>`) {
	l = translateArithmeticExpr(lhs);
	r = translateArithmeticExpr(rhs);
	return arithmExpr(l.renaming + r.renaming, div(l.alleExpr, r.alleExpr));
}

ArithmExpr translateArithmeticExpr((Expr)`| <Expr ex> |`) {
	aex = translateArithmeticExpr(ex);
	return arithmExpr(aex.renaming, abs(aex.alleExpr));
}

ArithmExpr translateArithmeticExpr((Expr)`( <Expr ex> )`)
	= translateArithmeticExpr(ex);

// Leaves of a tree with arithmetic expressions: literals and 'normal' Nextep expressions
ArithmExpr translateArithmeticExpr((Expr)`<Literal l>`) 
	= arithmExpr( (), translateConstraintExpr(l) );

default ArithmExpr translateArithmeticExpr(Expr expr)
	= arithmExpr( (v1: translate(expr)), att(v1) )
		when v1 := "val<expr@\loc.offset>";

 //Expr
 // = count:      "count" "(" Expr ")"
 // | avg:        "avg" "(" Expr ")"
 // | min:        "min" "(" Expr ")"
 // | max:        "max" "(" Expr ")"
 // | abs:        "|" Expr "|"
 // > left ( div: Expr "\\" Expr
 //        | mul: Expr "*" Expr
 //        > add: Expr "+" Expr
 //        | sub: Expr "-" Expr
 //        )
 // ;


// DISTANCE

AlleFormula distanceDeclaration(class(Class _), RelationDef d, RelationDef xo, RelationDef xn)
  = equal(relvar(d.name), 
           union(difference(relvar(xo.name), relvar(xn.name)), 
                 difference(relvar(xn.name), relvar(xo.name))));

AlleFormula distanceDeclaration(intType(), RelationDef d, RelationDef xo, RelationDef xn)
  = conjunction(equal(project(relvar(d.name), attr), 
                      project(relvar(xn.name), attr)), 
      universal([varDecl("d", relvar(xn.name))], 
           conjunction( 
            implication(dinxo, f1),
            implication(negation(dinxo), f2)
                      )           
                ))
    when 
      list[str] attr := [a.name | a <- d.heading, a.name != "delta"],
      AlleFormula dinxo := subset(project(relvar("d"), attr), project(relvar(xo.name), attr)),
      AlleFormula f1 := nonEmpty(select(naturalJoin(naturalJoin(relvar("d"), relvar(d.name)), rename(relvar(xo.name), [rename("xo_val", "val")])), 
                          equal(att("delta"), abs(subtraction(att("val"), att("xo_val")))))),
      AlleFormula f2 := nonEmpty(select(naturalJoin(relvar("d"), relvar(d.name)), 
                          equal(att("delta"), att("val"))));

Maybe[ObjectiveSection] generateAlleObjectives(NX2AlleMapping rels) {
  list[Objective] criteria = 
    [minimize(generateMetric(nxDom, alleRel)) | <NaryRelation(_, _, nxDom, _), alleRel, distance()> <- rels]
  + [minimize(generateMetric(class(nxDom), alleRel)) | <UnaryRelation(nxDom), alleRel, distance()> <- rels];  
  
  return just(objectives(lex(), criteria)); 
}

AlleExpr generateMetric(class(Class _), RelationDef alleRel)
  = aggregate(relvar(alleRel.name), [aggFuncDef(count(), "c")]);
  
AlleExpr generateMetric(intType(), RelationDef alleRel)
  = aggregate(relvar(alleRel.name), [aggFuncDef(sum("delta"), "s")]);  


  