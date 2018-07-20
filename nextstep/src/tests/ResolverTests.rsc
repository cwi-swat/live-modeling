module tests::ResolverTests

import lang::nextstep::Resolver;
import lang::nextstep::Syntax;
import Parser;

import IO;

void testResolve() = testResolve(|project://nextstep/input/statemachine.nxst|);

void testResolve(loc f) {
  res = resolveTypes(parseFile(f));
  
  println(res);
}