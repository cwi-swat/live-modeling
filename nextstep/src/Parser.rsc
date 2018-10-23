module Parser

import ParseTree;
import lang::nextstep::Syntax;
import lang::nextstep::OutputSyntax;

Spec parseFile(loc file)        = parse(#start[Spec], file).top;
Spec parseFile(str x, loc file) = parse(#start[Spec], x, file).top;
Spec parseString(str x)         = parse(#start[Spec], x).top;

OutputDef parseOutputFile(loc file)         = parse(#start[OutputDef], file).top;
OutputDef parseOutputFile(str x, loc file)  = parse(#start[OutputDef], x, file).top;