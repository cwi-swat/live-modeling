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

import ParseTree;

anno RelationDef Expr@alleRel;

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

list[AlleFormula] translate(Spec spc) = translate(spc.\dynamic) + translate(spc.migration);
list[AlleFormula] translate((DynamicDef)`runtime { <Class* cs> }`) = [*translate(c) | Class c <- cs];
list[AlleFormula] translate((MigrationDef)`migration { <Formula* rules>}`) =  [translate(f) | Formula f <- f];
list[AlleFormula] translate((Class)`class <ClassName _> { <ClassBody body>}`) = translate(body); 
list[AlleFormula] translate((ClassBody)`<FieldDecl* _> <Invariant* inv>`) = [*translate(i) | Invariant i <- inv];
list[AlleFormula] translate((Invariant)`invariant: <Formula form>`) = [translate(form)];  
list[AlleFormula] translate((Invariant)`invariants { Formula+ forms }`) = [translate(f) | Formula f <- forms];
 
AlleFormula translate((Formula)`( <Formula form> )`) = translate(form);
AlleFormula translate((Formula)`not <Formula form>`) = \neg(translate(form));
//RelLookup createLookup(f:(Formula)`some <Expr expr>`, Context ctx, NX2AlleMapping mp) = createLookup(expr, ctx, mp);
//RelLookup createLookup(f:(Formula)`no <Expr expr>`, Context ctx, NX2AlleMapping mp) = createLookup(expr, ctx, mp);
//RelLookup createLookup(f:(Formula)`one <Expr expr>`, Context ctx, NX2AlleMapping mp) = createLookup(expr, ctx, mp);
//RelLookup createLookup(f:(Formula)`<Expr lhs> in <Expr rhs>`, Context ctx, NX2AlleMapping mp) = createLookup(lhs, ctx, mp) + createLookup(rhs, ctx, mp); 
//RelLookup createLookup(f:(Formula)`<Expr lhs> = <Expr rhs>`, Context ctx, NX2AlleMapping mp) = createLookup(lhs, ctx, mp) + createLookup(rhs, ctx, mp); 
//RelLookup createLookup(f:(Formula)`<Expr lhs> != <Expr rhs>`, Context ctx, NX2AlleMapping mp) = createLookup(lhs, ctx, mp) + createLookup(rhs, ctx, mp); 
//RelLookup createLookup(f:(Formula)`<Formula lhs> =\> <Formula rhs>`, Context ctx, NX2AlleMapping mp) = createLookup(lhs, ctx, mp) + createLookup(rhs, ctx, mp); 
//RelLookup createLookup(f:(Formula)`<Formula lhs> \<=\> <Formula rhs>`, Context ctx, NX2AlleMapping mp) = createLookup(lhs, ctx, mp) + createLookup(rhs, ctx, mp); 
//RelLookup createLookup(f:(Formula)`<Formula lhs> && <Formula rhs>`, Context ctx, NX2AlleMapping mp) = createLookup(lhs, ctx, mp) + createLookup(rhs, ctx, mp); 
//RelLookup createLookup(f:(Formula)`<Formula lhs> || <Formula rhs>`, Context ctx, NX2AlleMapping mp) = createLookup(lhs, ctx, mp) + createLookup(rhs, ctx, mp); 
//RelLookup createLookup(f:(Formula)`forall <{QuantDecl ","}+ decls> | <Formula form>`, Context ctx, NX2AlleMapping mp) 
//  = (() | it + createLookup(d,ctx,mp) | QuantDecl d <- decls)
//  + createLookup(form, ctx, mp)
//  ;
//RelLookup createLookup(f:(Formula)`exists <{QuantDecl ","}+ decls> | <Formula form>`, Context ctx, NX2AlleMapping mp) 
//  = (() | it + createLookup(d,ctx,mp) | QuantDecl d <- decls)
//  + createLookup(form, ctx, mp)
//  ;


AlleExpr translate((Expr)`( <Expr ex> )`) = tranlsate(ex);
AlleExpr translate(ex:(Expr)`<VarName v>`) = relvar(ex@alleRel.name);  
//  | lit:          Literal
AlleExpr translate(ex:(Expr)`<Expr lhs>.<Expr rhs>`) = \false();



// distance


// migration rules

  