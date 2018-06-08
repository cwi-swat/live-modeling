module lang::nextstep::Translator

import lang::nextstep::Syntax;
import translation::Syntax;
import String;
import IO;

// intermediate model
data Relation 
	= UnaryRelation (Class class, int lowbound, int upperbound)
	| NaryRelation (Id relation, Class domain, Class range, bool multiple)
	;
// alternative n-ary relation: 
// An n-ary relation connects all fields of the class
//NaryRelation (Class relation, set[tuple[str attrname, Class attrtype, bool multiple]])

	
// print intermediate model
void printRels(list[Relation] rels) {
  for (r <- rels) {
    switch (r) {
      case UnaryRelation(c, l, u): 
        println("unary: <c>, <l>, <u>");
      case NaryRelation(Id re, ClassName d, ClassName r, bool m):
        println("nary: <re>, <d>, <r>, <m>");
    }
  }
}
	

// First step of the translation: extract the intermediate model from the input file
list[Relation] extractRelations(start[Spec] spec) 
  = [ *class2relations(c) | Class c <- spec.top.static.classes ] 
  + [ *class2relations(c) | Class c <- spec.top.\dynamic.classes ];

// Generate relations for the class and its fields
list[Relation] class2relations(Class c)
  = class2relation(c) + fields2relations(c);


// A unary relation for the bounded class
list[Relation] class2relation(c:(Class)`class <ClassName name> <Super? _> <Bounds b> {<ClassBody cb>}`)
  = [ UnaryRelation(c, lowerOf(b), upperOf(b)) ];

// No separate (unary) relation for the unbounded class
list[Relation] class2relation(c:(Class)`class <ClassName x> <Super? _> {<ClassBody cb>}`) = [];

// Determine lower and upper bounds
int lowerOf ((Bounds)`( <Int x>..<Int y> )`) = toInt("<x>");
int lowerOf ((Bounds)`( <Int y> )`) = 0;
int upperOf ((Bounds)`( <Int x>..<Int y> )`) = toInt("<y>");
int upperOf ((Bounds)`( <Int y> )`) = toInt("<y>");


//list[Relation] class2relation(k:(Class)`class <ClassName x> extends <ClassName p> {<ClassBody cb>}`)
// = [ UnaryRelation(k, lowerOf(b), upperOf(b)) ];

// A relation for each field of the class 
list[Relation] fields2relations (Class class)
  = [field2relation(class, f) | FieldDecl f <- class.body.fields];

// A n-ary relation for each field of the class
Relation field2relation (Class class, (FieldDecl)`<Id f> : <ClassName t>*`)
  = NaryRelation (f, class, t, true);
Relation field2relation (Class class, (FieldDecl)`<Id f> : <ClassName t>`)
  = NaryRelation (f, class, t, false);

// TODO: how do we store a (n-ary) relation with int?
Relation field2relation (Class class, (FieldDecl)`<Id f> : int*`)
  = NaryRelation (f, class, class.name, true); 
Relation field2relation (Class class, (FieldDecl)`<Id f> : int`)	
  = NaryRelation (f, class, class.name, true); 
	
	
	