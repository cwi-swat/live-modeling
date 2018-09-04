module Plugin

import util::IDE;
import ParseTree;

import Parser;

import Pipeline;
import lang::nextstep::Syntax;

void main(){
  str lang = "NextStep";

  registerLanguage(lang,"nxst", parseFile); 
  contribs = {
    popup(menu("NexStep", [
        action("Run and visualize", (Tree current, loc file) {
          if (/Spec spc := current) {
            runNextep(spc);
          }
        })
   ])),
    syntaxProperties(#start[Spec])
  };
  
  registerContributions(lang, contribs);
} 
