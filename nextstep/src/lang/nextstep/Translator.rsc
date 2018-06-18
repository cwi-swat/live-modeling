module lang::nextstep::Translator

import lang::nextstep::Syntax;
import translation::AST;   // AlleAlle
import translation::theories::integer::AST;
import String;
import IO;

alias nextepId = lang::nextstep::Syntax::Id;

// intermediate model
data NXRelation 
	= UnaryRelation (Class class, int lowbound, int upperbound)
	| NaryRelation (Class domain, nextepId relation, str range, bool multiple)
	;
	
// alternative n-ary relation: (only for originally unbounded classes, not for the fields of the bounded classes)
// An n-ary relation connects all fields of the class
// NaryRelation (Class relation, set[tuple[str attrname, Class attrtype, bool multiple]])

	
// print intermediate model
void printRels(list[NXRelation] rels) {
  for (r <- rels) {
    switch (r) {
      case UnaryRelation(c, l, u): 
        println("unary: <c.name>, <l>, <u>");
      case NaryRelation(Class d, nextepId re, str r, bool m):
        println("nary: <d.name>, <re>, <r>, <m>");
    }
  }
}
	

// FIRST STEP of the translation: extract the intermediate model from the input file
list[NXRelation] extractRelations(start[Spec] spec) 
  = [ *class2relations(c) | Class c <- spec.top.static.classes ] 
  + [ *class2relations(c) | Class c <- spec.top.\dynamic.classes ];

// Generate relations for the class and its fields
list[NXRelation] class2relations(Class c)
  = class2relation(c) + fields2relations(c);


// A unary relation for the bounded class
list[NXRelation] class2relation(c:(Class)`class <ClassName name> <Super? _> <Bounds b> {<ClassBody cb>}`)
  = [ UnaryRelation(c, lowerOf(b), upperOf(b)) ];

// No separate (unary) relation for the unbounded class
list[NXRelation] class2relation(c:(Class)`class <ClassName x> <Super? _> {<ClassBody cb>}`) 
  = [ ];

// OPT: No separate (unary) relation for the Runtime class
list[NXRelation] class2relation(c:(Class)`class Runtime <Super? _> <Bounds b> {<ClassBody cb>}`)
  = [ ];


// Determine lower and upper bounds
int lowerOf ((Bounds)`( <Int x>..<Int y> )`) = toInt("<x>");
int lowerOf ((Bounds)`( <Int y> )`) = 0;
int upperOf ((Bounds)`( <Int x>..<Int y> )`) = toInt("<y>");
int upperOf ((Bounds)`( <Int y> )`) = toInt("<y>");


//list[NXRelation] class2relation(k:(Class)`class <ClassName x> extends <ClassName p> {<ClassBody cb>}`)
// = [ UnaryRelation(k, lowerOf(b), upperOf(b)) ];

// A relation for each field of the class 
list[NXRelation] fields2relations (Class class)
  = [field2relation(class, f) | FieldDecl f <- class.body.fields];

// An n-ary relation for each field of the class
NXRelation field2relation (Class class, (FieldDecl)`<Id f> : <ClassName t>*`)
  = NaryRelation (class, f, "<t>", true);
NXRelation field2relation (Class class, (FieldDecl)`<Id f> : <ClassName t>`)
  = NaryRelation (class, f, "<t>", false);
NXRelation field2relation (Class class, (FieldDecl)`<Id f> : int*`)
  = NaryRelation (class, f, "int", true); 
NXRelation field2relation (Class class, (FieldDecl)`<Id f> : int`)	
  = NaryRelation (class, f, "int", true); 
	

// SECOND STEP of the translation: translate the intermediate model into AlleAlle structures
list[RelationDef] translateRelations (list[NXRelation] relations)
  = [ nextep2alleRelation(r) | r <- relations ];

// Generate structural constraints (types and multiplicity of associations)
list[AlleFormula] restrictRelations (list[NXRelation] relations) = [];

// Translate a unary (class) relation into AlleAlle relation
RelationDef nextep2alleRelation (UnaryRelation(Class c, int l, int u))
  = relation ( "<c.name>", 
              [ header(classprefix(c) + "Id", id()) ], 
              exact([ range( [id(classprefix(c), l)], [id(classprefix(c), u)]) ]) 
             );
              
// Get a class-correspondent prefix (first two letters of its name - does not work always!)          
str classprefix(Class class) = substring("<class.name>", 0, 2);              

// Translate an n-ary (field) relation into AlleAlle relation
RelationDef nextep2alleRelation (NaryRelation());
  //= relation();
	