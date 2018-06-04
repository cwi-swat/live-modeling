module Plugin

import util::IDE;
import ParseTree;

import Parser;
import lang::nextstep::Syntax;

void main(){
  str lang = "NextStep";

  registerLanguage(lang,"nxst", parseFile); 
  contribs = {
    syntaxProperties(#start[Spec])
  };
  
  registerContributions(lang, contribs);
} 
