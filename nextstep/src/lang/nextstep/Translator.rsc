module nexstep::Translator

import nextstep::Syntax;
import allealle::translation::Syntax;

// intermediate model
data Relation 
	= UnaryRelation (Class relation, int lowbound, int upperbound)
	| NaryRelation (Class domain, Class range, bool multiple)
	;
	
alias RelationsList = list[Relation];


RelationsList extractRelations (Spec spec) 
	= [class2relation(c) | c <- (spec.static.classes + spec.dynamic.classes)];	// why is the parse error???

// A unary relation for the bounded class and a nary relation for each field in the class
UnaryRelation class2relation (Class(name, bounds, body) class);	// does this check that bounds is not null???
//	= UnaryRelation(class, class.bounds);

RelationsList class2relation (Class class)			// will both functions class2relation be invoked???
	= [classfield2relation(class, f) | f <- class.body.fields]; 

// A binary relation for each field
NaryRelation classfield2relation (Class class, FieldDecl field)
	= NaryRelation (class, field.type, ); 	// how to translate a piece of regular expression ("*"?) from the syntax???