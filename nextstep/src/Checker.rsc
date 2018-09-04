module Checker

import ide::CombinedAST;
import ide::CombinedModelFinder;

import ide::vis::ModelVisualizer; 

import translation::SMTInterface;

import smtlogic::Core;

import IO;

void check(Problem alleProblem) {
  ModelFinderResult result = checkInitialSolution(alleProblem);
  
  switch(result) {
    case sat(Model currentModel, Model (Domain) nextModel, void () stop): renderModel(currentModel, nextModel, stop);
    case unsat(set[Formula] unsatCore) : alert("Not satisfiable, can not visualize");
    case trivialSat(Model model) : alert("Trivially satisfiable");
    case trivialUnsat() : alert("Trivially not satisfiable");  
  } 

}
