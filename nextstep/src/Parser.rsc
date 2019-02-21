module Parser

import ParseTree;
import lang::nextstep::Syntax;
import lang::nextstep::InstanceSyntax;
import lang::nextstep::OutputSyntax;

Spec parseFile(loc file)        = parse(#start[Spec], file).top;
Spec parseFile(str x, loc file) = parse(#start[Spec], x, file).top;
Spec parseString(str x)         = parse(#start[Spec], x).top;

NextepInstance parseInstanceFile(loc file)        = parse(#start[NextepInstance], file).top;
NextepInstance parseInstanceFile(str x, loc file) = parse(#start[NextepInstance], x, file).top;
NextepInstance parseInstanceString(str x)         = parse(#start[NextepInstance], x).top;

OutputDef parseOutputFile(loc file)         = parse(#start[OutputDef], file).top;
OutputDef parseOutputFile(str x, loc file)  = parse(#start[OutputDef], x, file).top;