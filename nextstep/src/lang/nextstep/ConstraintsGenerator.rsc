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
import String;
import ParseTree;

//anno str Expr@alleRel;
//anno str Class@alleRel;

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

list[AlleFormula] translate(Spec spc) = translate(spc.\dynamic); // + translate(spc.migration);
list[AlleFormula] translate((DynamicDef)`runtime { <Class* cs> }`) = [*translate(c) | Class c <- cs];
list[AlleFormula] translate((MigrationDef)`migration { <Formula* rules>}`) =  [translate(f) | Formula f <- rules];
list[AlleFormula] translate(c:(Class)`class <ClassName _> { <ClassBody body>}`) = translate(body);  
list[AlleFormula] translate((ClassBody)`<FieldDecl* _> <Invariant* inv>`) = [*translate(i) | Invariant i <- inv];
list[AlleFormula] translate((Invariant)`invariant: <Formula form>`) = [translate(form)];  
list[AlleFormula] translate((Invariant)`invariants { <Formula+ forms> }`) = [translate(f) | Formula f <- forms];
 
AlleFormula translate((Formula)`( <Formula form> )`) = translate(form);
AlleFormula translate((Formula)`not <Formula form>`) = negation(translate(form));
AlleFormula translate((Formula)`some <Expr expr>`) = nonempty(translate(expr));
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


// !!!!!! arithmetics!!!
AlleFormula translate((Formula)`<Expr lhs> \>= <Expr rhs>`) =
   nonEmpty(select(translate(lhs), gte(att("val"),translateConstraintExpr(rhs))));

AlleFormula translate((Formula)`<Expr lhs> \> <Expr rhs>`) = \false;
AlleFormula translate((Formula)`<Expr lhs> \<= <Expr rhs>`) = \false;
AlleFormula translate((Formula)`<Expr lhs> \< <Expr rhs>`) = \false;

AlleExpr translate((Expr)`( <Expr ex> )`) = translate(ex);
AlleExpr translate(ex:(Expr)`<VarName v>`) = relvar(ex@alleRel);  
AlleExpr translate((Expr)`<Literal l>`) = translate(l);
AlleExpr translate(ex:(Expr)`<Expr lhs>.<Expr rhs>`) 
  = project(naturalJoin(translate(lhs), translate(rhs)), [a.name| a <- ex@header]);
//AlleExpr translate(ex:(Expr)`<Expr lhs>.<Expr rhs>`) 
//  = project(naturalJoin(project(naturalJoin(relvar(classBoundVar), translate(lhs)), [a.name| a <- lhs@header]), 
//            translate(rhs)), [a.name| a <- ex@header])
//  when lhs := (Expr)`<VarName v>`;
AlleExpr translate((Expr)`<Expr lhs> ++ <Expr rhs>`) = union(translate(lhs), translate(rhs));
AlleExpr translate((Expr)`<Expr lhs> & <Expr rhs>`) = intersection(translate(lhs), translate(rhs));
AlleExpr translate((Expr)`<Expr lhs> -- <Expr rhs>`) = difference(translate(lhs), translate(rhs));
//AlleExpr translate((Expr)`^<Expr ex>`) = closure(, translate(ex));
//AlleExpr translate((Expr)`*<Expr ex> `) = reflexClosure(, translate(ex));
AlleExpr translate(ex:(Expr)`<Expr lhs> where <RestrictStat rhs>`) 
  = select(translate(lhs), translateConstraint(rhs));

AlleLiteral translate((Literal)`<Int i>`) = intLit(toInt("<i>"));

Criteria translateConstraint((RestrictStat)`(<RestrictStat restr>)`) = translate(restr);
Criteria translateConstraint((RestrictStat)`<RestrictExpr lhs> = <RestrictExpr rhs>`) = equal(translate(lhs), translate(rhs));

CriteriaExpr translateConstraint((RestrictExpr)`<QualifiedName att>`) = translate(att);
CriteriaExpr translateConstraintExpr((Expr)`<Literal l>`) = litt(translate(l));

// ??????????
// qualified name is in fact our dot notation for the navigation of objects, 
// so we should be able to produce a proper attribute from relations join
CriteriaExpr translate((QualifiedName)`<VarName lhs> ("." <VarName rhs>)*`) = att("");


// !!!!!! arithmetics!!!
//AlleFormula translate((Formula)`<Expr lhs> \>= <Expr rhs>`) 
//  = nonEmpty(select(  ,  gte( , )));
//// We need a different treatment for the whole arithmetic expression 
//// (including what possibly follows next: +, -, *, etc.)
//AlleFormula translate((Formula)`<Expr lhs> \>= <Int rhs>`) 
//  = nonEmpty(select(  ,  ));
//  
AlleFormula translate((Formula)`<Expr lhs> \> <Expr rhs>`) = \false;
AlleFormula translate((Formula)`<Expr lhs> \<= <Expr rhs>`) = \false;
AlleFormula translate((Formula)`<Expr lhs> \< <Expr rhs>`) = \false;


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


// MIGRATION RULES


  