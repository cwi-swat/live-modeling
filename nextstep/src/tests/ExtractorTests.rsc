module tests::ExtractorTests

import lang::nextstep::Syntax;
import lang::nextstep::Resolver;
import lang::nextstep::Extractor;
import Parser;
import Map;

import IO;

void testExtraction() = testExtraction(|project://nextstep/input/statemachine.nxst|);

void testExtraction(loc f) {
  Spec spc = parseFile(f);
  Models result = extract(spc, resolveTypes(spc));
 
  printModels(result);
  //printRels(result);
}

void printModels(Models models) {
  for (Model m <- domain(models)) {
    println("----- MODEL: <m>");
    for (NXBounds b <- models[m]) {
      println("Relation: <nxRelation2str(b.r)>");
      println("Tuples: <b.tup>");
    }
  }
}

void printRels(list[NXRelation] rels) {
  for (r <- rels) {
    switch (r) {
      case UnaryRelation(Class c):
        println("unary: <c.name>");
      case NaryRelation(str relation, Class domain, RangeType range, bool isSet):
        println("nary: <relation>, <domain.name>, <rangeType2str(range)>, <isSet>");
      default: println("Not defined: r");
    }
  }
} 

str rangeType2str(class(Class c)) = "<c.name>";
str rangeType2str(intType()) = "int";
str nxRelation2str(UnaryRelation(Class c)) = "<c.name>";
str nxRelation2str(NaryRelation(relation, _,_,_)) = "<relation>";
