/* Second step of the translation: 
 * translate the intermediate model into AlleAlle structures
 * OPT stands for optimization (of the resulting output in the relation to the amount of the generated AlleAlle constructs)
 * contributors: ulyanatikhonova
 */

module lang::nextstep::Generator

import lang::nextstep::Extractor;
import translation::AST;                    // AlleAlle
import translation::theories::integer::AST; // AlleAlle


list[RelationDef] generateAlleRelations (Models models) 
  = [nxRelation2alle(r, "pn_") | r <- models[oldStatic()]];

RelationDef nxRelation2alle (NXBounds(UnaryRelation r, set[NXTuple] nxtuples), str prefix) 
  = relation ( prefix + "<r.class.name>", 
                [ header("<r.class.name>" + "Id", id()) ], 
                exact([tup([idd(toId(t.a))]) | t <- nxtuples]) 
              );



//
//list[RelationDef] translateRelations (list[NXRelation] relations)
//  = [ *nextep2alleRelation(r) | r <- relations ];
//
//// Generate structural constraints (types and multiplicity of associations)
//list[AlleFormula] restrictRelations (list[NXRelation] relations) = [];
//
//// Translate a unary (bounded class) relation into AlleAlle relation
//list[RelationDef] nextep2alleRelation (UnaryRelation(Class class))
//  = [relation ( unaryRelName(class), 
//                [ header(atomprefix(class) + "Id", id()) ], 
//                exact([ range( [id(atomprefix(class), low)], [id(atomprefix(class), up)]) ]) 
//              )] ;
//
//    
//
//// Translate an n-ary (field) relation into AlleAlle relation
//list[RelationDef] nextep2alleRelation (NaryRelation(Class class, nextepId field, str range, bool mult))
//  = [ relation (
//                ) ] 
//  when class.name != "Runtime";
//
//// All fields of the Runtime class become a unary relation in AlleAlle.
//list[RelationDef] nextep2alleRelation (NaryRelation(Class class, nextepId field, str range, bool mult))
//  = [ relation (
//                ) ] 
//  when class.name == "Runtime";
//
//// All fields of an unbounded class are matched together into one n-ary relation 
//list[RelationDef] nextep2alleRelation (NaryRelation(Class class, nextepId field, str range, bool mult))
//  = [ relation (
//                )] 
//  when class.name != "Runtime" && 
//    (Class)`class <ClassName _> <Super? _> {<ClassBody _>}` := class;
//
////list[NXRelation] class2relation(k:(Class)`class <ClassName x> extends <ClassName p> {<ClassBody cb>}`)
//// = [ UnaryRelation(k, lowerOf(b), upperOf(b)) ];
//
///* NAMING CONVENTIONS */
// A class-correspondent prefix for atoms          
str atomprefix(Class class) = toLowerCase("<class.name>");              

// A unary relation name
str unaryRelName(Class class) = "<class.name>";
