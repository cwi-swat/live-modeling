module lang::nextstep::Translator

import lang::nextstep::Syntax;
import translation::AST;   // AlleAlle
import translation::theories::integer::AST;
import String;
import List;
import IO;

alias nextepId = lang::nextstep::Syntax::Id;

// intermediate model
data NXRelation 
	= UnaryRelation (Class class, int lowbound, int upperbound)
	| NaryRelation (Class domain, nextepId relation, Type range, bool multiple)
	;
	
// alternative n-ary relation: (only for originally unbounded classes, not for the fields of the bounded classes)
// An n-ary relation connects all fields of the class
// NaryRelation (Class relation, rel[str attrname, Class attrtype, bool multiple]])

	
// print intermediate model
void printRels(list[NXRelation] rels) {
  for (r <- rels) {
    switch (r) {
      case UnaryRelation(c, l, u): 
        println("unary: <c.name>, <l>, <u>");
      case NaryRelation(Class d, nextepId re, Class r, bool m):
        println("nary: <d.name>, <re>, <r.name>, <m>");
      case NaryRelation(Class d, nextepId re, \int r, bool m):
        println("nary: <d.name>, <re>, int, <m>");
    }
  }
}	

// FIRST STEP: ------------------------------------------------------------------ 
// extract the intermediate model from the input file
list[NXRelation] extractRelations(start[Spec] spec) {
  list[NXRelation] intermModel = [];
  
  // A unary relation for the bounded class, except for the Runtime class (OPT)
  list[NXRelation] class2relation(c:(Class)`class <ClassName x> <Super? _> <Bounds b> {<ClassBody cb>}`)
    = [ UnaryRelation(c, lowerOf(b), upperOf(b)) ] when "<x>" != "Runtime";

  // A unary relation for the unbounded class: bounds should be derived from its fields
  list[NXRelation] class2relation(c:(Class)`class <ClassName x> <Super? _> {<ClassBody cb>}`) 
    = [ UnaryRelation(c, -1, -1) ] when "<x>" != "Runtime";

  // OPT: No separate (unary) relation for the Runtime class
  list[NXRelation] class2relation(c:(Class)`class <ClassName x> <Super? _> <Bounds? b> {<ClassBody cb>}`)
    = [ ] when "<x>" == "Runtime"; 
  
  
  // An n-ary relation for each field of the class
  NXRelation field2relation (Class class, (FieldDecl)`<Id f> : <ClassName t>*`)
    = NaryRelation (class, f, getOneFrom([r.class | r <- intermModel, [UnaryRelation] r, r.class.name == t]), true);
  NXRelation field2relation (Class class, (FieldDecl)`<Id f> : <ClassName t>`)
    = NaryRelation (class, f, getOneFrom([r.class | r <- intermModel, [UnaryRelation] r, r.class.name == t]), false);
  NXRelation field2relation (Class class, (FieldDecl)`<Id f> : int*`)
    = NaryRelation (class, f, \int, true); 
  NXRelation field2relation (Class class, (FieldDecl)`<Id f> : int`)  
    = NaryRelation (class, f, \int, true);
  
  // A relation for each field of the class 
  list[NXRelation] fields2relations (Class class)
    = [field2relation(class, f) | FieldDecl f <- class.body.fields];
  
  
  // Generate relations for the class and its fields
  list[NXRelation] class2relations(Class c)
    = class2relation(c) + fields2relations(c);
   
  // extract the intermediate model from all classes of the specification
  intermModel = [ *class2relations(c) | Class c <- spec.top.static.classes ] 
              + [ *class2relations(c) | Class c <- spec.top.\dynamic.classes ];

  return intermModel;              
}

// Determine lower and upper bounds
int lowerOf ((Bounds)`( <Int x>..<Int y> )`) = toInt("<x>");
int lowerOf ((Bounds)`( <Int y> )`) = 0;
int upperOf ((Bounds)`( <Int x>..<Int y> )`) = toInt("<y>");
int upperOf ((Bounds)`( <Int y> )`) = toInt("<y>");


//list[NXRelation] class2relation(k:(Class)`class <ClassName x> extends <ClassName p> {<ClassBody cb>}`)
// = [ UnaryRelation(k, lowerOf(b), upperOf(b)) ];


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

// 
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


//-------------- NAMING CONVENTIONS -------------------------------------------
// A class-correspondent prefix for atoms          
str atomprefix(Class class) = toLowerCase("<class.name>");              

// A unary relation name
str unaryRelName(Class class) = "<class.name>";

	