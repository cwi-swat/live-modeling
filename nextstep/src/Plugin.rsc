module Plugin

import util::IDE;
import util::Editors;
import ParseTree;

import Parser;

import Pipeline;
import lang::nextstep::Syntax;

void main(){
  str lang = "NextStep";

  registerLanguage(lang,"nxst", parseFile); 
  registerLanguage("NextStep output","nxstout", parseOutputFile);
   
  contribs = {
    popup(menu("NexStep", [
        action("Run and visualize", (Tree current, loc file) {
          if (/Spec spc := current) {
            edit(runAndGetNextModel(spc));
          }
        })
   ])),
    syntaxProperties(#start[Spec])
  };
  
  registerContributions(lang, contribs);
} 
