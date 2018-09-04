module tests::NormalizerTests

import lang::nextstep::Syntax;
import lang::nextstep::Normalizer;

import Parser;
import Map;
import IO;
import Set;
import util::Maybe;


void testNormalization() = testNormalization(|project://nextstep/input/statemachine.nxst|);

void testNormalization(loc f) {
  Spec spc = parseFile(f);
  
  spc = normalize(spc);
  
  writeFile(|project://nextstep/output/<spc@\loc[extension = "norm"].file>.nxst|, spc);
  
 // Models models = addNewRuntime(extract(spc, resolveTypes(spc)));
 
 // NX2AlleMapping rels = generateAlleRelations(models);
 // list[AlleFormula] forms = generateAlleConstraints(spc, rels);
  
  //str alleSpec = unparse(problem(toList(rels.alle), forms, nothing(), nothing()));
  
  //writeFile(|project://nextstep/output/<f[extension = "alle"].file>|, alleSpec);
}


