module Checker

import ide::CombinedAST;
import ide::CombinedModelFinder;

import ide::vis::ModelVisualizer; 

import translation::SMTInterface;

import smtlogic::Core;

import lang::nextstep::OutputSyntax;
import lang::nextstep::RelationsGenerator;
import lang::nextstep::Extractor;

import IO;
import List;
import Map;
import String;
import Set;
import ParseTree;

void checkAndVis(Problem alleProblem) {
  ModelFinderResult result = checkInitialSolution(alleProblem);
  
  switch(result) {
    case sat(Model currentModel, Model (Domain) nextModel, void () stop): {
      renderModel(currentModel, nextModel, stop);
    }
    case unsat(set[Formula] unsatCore) : alert("Not satisfiable, can not visualize");
    case trivialSat(Model model) : alert("Trivially satisfiable");
    case trivialUnsat() : alert("Trivially not satisfiable");  
  } 
}

OutputDef checkAndGetNextModel(Problem alleProblem, NX2AlleMapping mapping) {
  ModelFinderResult result = checkInitialSolution(alleProblem);
  
  switch(result) {
    case sat(Model currentModel, Model (Domain) nextModel, void () stop): {
      stop();
      return interpretResult(currentModel, mapping);
    }
    case unsat(set[Formula] unsatCore) : println("Not satisfiable, can not visualize");
    case trivialSat(Model model) : println("Trivially satisfiable");
    case trivialUnsat() : println("Trivially not satisfiable");  
  } 
}

OutputDef interpretResult(Model alleModel, NX2AlleMapping mapping) {
  NXRelation find(str alleRelName) = nx when <NXRelation nx, RelationDef alleDef, Model _> <- mapping, alleDef.name == alleRelName;
  ModelRelation findModelRel(str nxRelName) = r when ModelRelation r <- alleModel.relations, r.name == "xn_<nxRelName>";
  
  bool isUnary(ModelRelation r) = size(r.heading) == 1;
  bool isBinary(ModelRelation r) = size(r.heading) == 2;
  
  set[NXRelation] getFields(Class dom) = {nx | <NXRelation nx, RelationDef _, Model _> <- mapping, NaryRelation(str relation, Class domain, RangeType range, bool isSet) := nx, domain == dom}; 
  
  list[Atom] interpretAtoms(list[ModelTuple] tuples, str domainClass, str domainAtom) = [[Atom]"<id>" | ModelTuple t <- tuples, /idAttribute(domainClass, domainAtom) := t.attributes, idAttribute(str name, str id) <- t.attributes, name != domainClass]; 
  list[int] interpretInts(list[ModelTuple] tuples, str domainClass, str domainAtom) = [i | ModelTuple t <- tuples, /idAttribute(domainClass, domainAtom) := t.attributes, ModelAttribute a <- t.attributes, a.name != domainClass, a has val, lit(\int(int i)) := a.val]; 
  
  str interpretField(ModelRelation r, NXRelation nxR, str domainAtom, str fieldName) = "<fieldName> = <onEmpty(intercalate(", ", interpretInts(r.tuples, "<nxR.domain.name>Id", domainAtom)))>" when intType() := nxR.range;
  str interpretField(ModelRelation r, NXRelation nxR, str domainAtom, str fieldName) = "<fieldName> = <onEmpty(intercalate(", ", interpretAtoms(r.tuples, "<nxR.domain.name>Id", domainAtom)))>" when class(_) := nxR.range;
  
  str onEmpty(str s) = s == "" ? "[]" : s; 
  
  str interpretInstance(ModelRelation r, NXRelation nxR, str domainAtom, set[NXRelation] fields) 
  = "<nxR.class.name> <domainAtom> <for (NXRelation nxField <- fields, /^.*[_]<fieldName:.*>$/ := nxField.relation) {> 
    '  <interpretField(findModelRel(nxField.relation), nxField, domainAtom, fieldName)> <}>
    '";                                                  
  
  list[str] interpretClass(ModelRelation r) = ["<nxR.class.name> <intercalate(", ", interpretAtoms(r.tuples))>"] when NXRelation nxR := find(r.name), size(getFields(nxR.class)) == 0;
  default list[str] interpretClass(ModelRelation r) = [interpretInstance(r, nxR, id, fields) | NXRelation nxR := find(r.name), set[NXRelation] fields := getFields(nxR.class), ModelTuple t <- r.tuples, idAttribute(str _, str id) <- t.attributes];
    
  list[str] objs = [*interpretClass(r) | ModelRelation r <- alleModel.relations, /^xn[_].*$/ := r.name, isUnary(r)];
  
  return [OutputDef]"output {
                    '  new runtime <for (str obj <- objs) {>
                    '    <obj> <}>
                    '}";                    
}

//syntax ObjectDef 
//  = Type type Atom objectName  FieldInstantiation+ fields 
//  | Type type {Atom ","}* objects 
//  ;  
//
//syntax FieldInstantiation 
//  = VarName fieldName "=" {Atom ","}* atoms
//  | VarName fieldName "=" {Int ","}* atoms
//  | VarName fieldName "=" "[" "]"




