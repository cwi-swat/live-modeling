module Pipeline

import lang::nextstep::Syntax;
import lang::nextstep::Resolver;
import lang::nextstep::Extractor;
import lang::nextstep::RelationsGenerator;
import lang::nextstep::ConstraintsGenerator;
import lang::nextstep::Annotator;
import lang::nextstep::Normalizer;

import translation::AST;                    // AlleAlle
import translation::theories::integer::AST; // AlleAlle
import translation::theories::integer::Unparser;
import ide::vis::integrationtests::VisualizerTester;

import Parser;
import Checker;

import Map;
import IO;
import Set;
import util::Maybe;
import ParseTree;

void runNextepSM() = runNextep(|project://nextstep/input/statemachine.nxst|);
void runNextepRoboticArm() = runNextep(|project://nextstep/input/roboticarm.nxst|);

void runNextep(loc f) {
  // parse and normalize
  Spec spc = parseFile(f);
  runNextep(spc);
}

void runNextep(Spec spc) {
  spc = parseFile(normalize(spc));
  
  // extract (instance) models
  Models models = addNewRuntime(extract(spc, resolveTypes(spc)));
 
  // generate AlleAlle relations 
  NX2AlleMapping rels = generateAlleRelations(models);
  
  // type check (and resolve) nextep expressions using AlleAlle relations
  Spec annotatedSpc = annotate(spc,rels);
  
  // generate constraints and translate invariants
  list[AlleFormula] forms = generateAlleConstraints(annotatedSpc, rels) + translate(annotatedSpc);
  Maybe[ObjectiveSection] objectives = generateAlleObjectives(rels);
  
  // write AlleAlle file
  Problem alleProblem = problem(toList(rels.alle), forms, objectives, nothing());
  writeFile(|project://nextstep/output/<spc@\loc[extension = "alle"].file>|, unparse(alleProblem));
  
  // Run AlleAlle solver and visualize result
  check(alleProblem);
}


