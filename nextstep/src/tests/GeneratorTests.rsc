module tests::GeneratorTests

import lang::nextstep::Syntax;
import lang::nextstep::Resolver;
import lang::nextstep::Extractor;
import lang::nextstep::RelationsGenerator;
import lang::nextstep::ConstraintsGenerator;
import lang::nextstep::Annotator;
import lang::nextstep::Normalizer;

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
void testGeneration2() = testGeneration(|project://nextstep/input/roboticarm.nxst|);
void testGeneration3() = testGeneration(|project://nextstep/output/normalized.nxst|);


void testGeneration(loc f) {
  Spec spc = parseFile(f);
  normalize(spc);
  spc = parseFile(|project://nextstep/output/normalized.nxst|); //"<normalize(spc)>");
  
  Models models = addNewRuntime(extract(spc, resolveTypes(spc)));
 
  NX2AlleMapping rels = generateAlleRelations(models);
  Spec annotatedSpc = annotate(spc,rels);
  
  list[AlleFormula] forms = generateAlleConstraints(annotatedSpc, rels) + translate(annotatedSpc);
  Maybe[ObjectiveSection] objectives = generateAlleObjectives(rels);
  
  str alleSpec = unparse(problem(toList(rels.alle), forms, objectives, nothing()));
  
  writeFile(|project://nextstep/output/<f[extension = "alle"].file>|, alleSpec);
}


