module tests::GeneratorTests

import lang::nextstep::Syntax;
import lang::nextstep::Resolver;
import lang::nextstep::Extractor;
import lang::nextstep::RelationsGenerator;
import lang::nextstep::ConstraintsGenerator;

import translation::AST;                    // AlleAlle
import translation::theories::integer::AST; // AlleAlle

//import translation::Unparser;
import translation::theories::integer::Unparser;

import Parser;
import Map;
import IO;
import Set;
import util::Maybe;


void testGeneration() = testGeneration(|project://nextstep/input/statemachine.nxst|);

void testGeneration(loc f) {
  Spec spc = parseFile(f);
  Models models = addNewRuntime(extract(spc, resolveTypes(spc)));
 
  NX2AlleMapping rels = generateAlleRelations(models);
  list[AlleFormula] forms = generateAlleConstraints(spc, models);
  
  str alleSpec = unparse(problem(toList(rels.alle), forms, nothing(), nothing()));
  
  writeFile(|project://nextstep/output/<f[extension = "alle"].file>|, alleSpec);
}


