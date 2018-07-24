module tests::GeneratorTests

import lang::nextstep::Syntax;
import lang::nextstep::Resolver;
import lang::nextstep::Extractor;
import lang::nextstep::Generator;
import translation::AST;                    // AlleAlle
import translation::theories::integer::AST; // AlleAlle
import Parser;
import Map;

import IO;

void testGeneration() = testGeneration(|project://nextstep/input/statemachine.nxst|);

void testGeneration(loc f) {
  Spec spc = parseFile(f);
  Models models = extract(spc, resolveTypes(spc));
 
  list[RelationDef] allerels = generateAlleRelations(models);
  println(allerels);
}


