module Pipeline

import lang::nextstep::Syntax;
import lang::nextstep::InstanceSyntax;
import lang::nextstep::OutputSyntax;
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

alias NxtpToAlleTransResult = tuple[Problem alleProblem, NX2AlleMapping mapping]; 

void runAndVisSM() = runAndVis(parseFile(|project://nextstep/input/statemachine.nxst|), parseInstanceFile(|project://nextstep/input/stmInstance1.nxstin|));

void runAndGetNextModelSM() = runNextep(|project://nextstep/input/statemachine.nxst|, |project://nextstep/input/stmInstance1.nxstin|);
void runAndGetNextModelRoboticArm() = runNextep(|project://nextstep/input/roboticarm.nxst|, |project://nextstep/input/rbaInstance1.nxstin|);

void runNextep(loc f1, loc f2) {
  // parse and normalize
  Spec spc = parseFile(f1);
  Instance inst = parseInstanceFile(f2);
  runAndWriteNextModelToFile(spc, inst);
}

void runAndVis(Spec spc, NextepInstance inst) {
  NxtpToAlleTransResult result = translateNxtpToAlle(spc, inst);
  // write AlleAlle file
  writeFile(|project://nextstep/output/<spc@\loc[extension = "alle"].file>|, unparse(result.alleProblem));
  
  checkAndVis(result.alleProblem);
}

loc runAndWriteNextModelToFile(Spec spc, NextepInstance inst) {
  OutputDef output = runAndGetNextModel(spc, inst);
  
  loc outputFile = |project://nextstep/output/<spc@\loc[extension = "nxstout"].file>|;
  writeFile(outputFile, "<output>");
  
  return outputFile;
}

OutputDef runAndGetNextModel(Spec spc, NextepInstance inst) {
  NxtpToAlleTransResult result = translateNxtpToAlle(spc, inst);
  // write AlleAlle file
  //writeFile(|project://nextstep/output/<spc@\loc[extension = "alle"].file>|, unparse(result.alleProblem));
  
  // Run AlleAlle solver and visualize result
  return checkAndGetNextModel(result.alleProblem, result.mapping);
}

NxtpToAlleTransResult translateNxtpToAlle(Spec spc, NextepInstance inst) {
  spc = parseFile(normalize(spc));
  
  // extract (instance) models
  Models models = addNewRuntime(extract(spc, resolveTypes(spc), inst));
 
  // generate AlleAlle relations 
  NX2AlleMapping rels = generateAlleRelations(models);
  
  // type check (and resolve) nextep expressions using AlleAlle relations
  Spec annotatedSpc = annotate(spc,rels);
  
  // generate constraints and translate invariants
  list[AlleFormula] forms = generateAlleConstraints(annotatedSpc, rels) + translate(annotatedSpc);
  Maybe[ObjectiveSection] objectives = generateAlleObjectives(rels);
  
  // write AlleAlle file
  return <problem(toList(rels.alle), forms, objectives, nothing()), rels>;
}


