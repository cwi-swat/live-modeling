module lang::nextstep::Generator

import translation::AST;   // AlleAlle
import translation::theories::integer::AST;

// SECOND STEP: -----------------------------------------------------------------
// translate the intermediate model into AlleAlle structures
list[RelationDef] translateRelations (list[NXRelation] relations)
  = [ *nextep2alleRelation(r) | r <- relations ];

// Generate structural constraints (types and multiplicity of associations)
list[AlleFormula] restrictRelations (list[NXRelation] relations) = [];

// Translate a unary (bounded class) relation into AlleAlle relation
list[RelationDef] nextep2alleRelation (UnaryRelation(Class class, int low, int up))
  = [relation ( unaryRelName(class), 
                [ header(atomprefix(class) + "Id", id()) ], 
                exact([ range( [id(atomprefix(class), low)], [id(atomprefix(class), up)]) ]) 
              )] 
    when l >= 0 && u >= 0;

// Translate a unary (unbounded class) relation into AlleAlle relation: derive its bounds
list[RelationDef] nextep2alleRelation (UnaryRelation(Class c, int l, int u))
  = [] when l < 0 || u < 0;
    

// Translate an n-ary (field) relation into AlleAlle relation
list[RelationDef] nextep2alleRelation (NaryRelation(Class class, nextepId field, str range, bool mult))
  = [ relation (
                ) ] 
  when class.name != "Runtime";

// All fields of the Runtime class become a unary relation in AlleAlle.
list[RelationDef] nextep2alleRelation (NaryRelation(Class class, nextepId field, str range, bool mult))
  = [ relation (
                ) ] 
  when class.name == "Runtime";

// All fields of an unbounded class are matched together into one n-ary relation 
list[RelationDef] nextep2alleRelation (NaryRelation(Class class, nextepId field, str range, bool mult))
  = [ relation (
                )] 
  when class.name != "Runtime" && 
    (Class)`class <ClassName _> <Super? _> {<ClassBody _>}` := class;

//list[NXRelation] class2relation(k:(Class)`class <ClassName x> extends <ClassName p> {<ClassBody cb>}`)
// = [ UnaryRelation(k, lowerOf(b), upperOf(b)) ];

//-------------- NAMING CONVENTIONS -------------------------------------------
// A class-correspondent prefix for atoms          
str atomprefix(Class class) = toLowerCase("<class.name>");              

// A unary relation name
str unaryRelName(Class class) = "<class.name>";
