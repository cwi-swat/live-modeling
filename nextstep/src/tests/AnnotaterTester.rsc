module tests::AnnotaterTester

import lang::nextstep::Syntax;
import lang::nextstep::Resolver;
import lang::nextstep::Extractor;
import lang::nextstep::RelationsGenerator;
import lang::nextstep::Annotator;

import Parser;
import Map;
import IO;
import Set;
import util::Maybe;

void testAnnotation() = testAnnotation(|project://nextstep/input/statemachine.nxst|);

void testAnnotation(loc f) {
  Spec spc = parseFile(f);
  
  Models models = addNewRuntime(extract(spc, resolveTypes(spc)));
  NX2AlleMapping rels = generateAlleRelations(models);

  Spec annotatedSpc = annotate(spc,rels);
}
