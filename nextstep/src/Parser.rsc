module Parser

import ParseTree;
import lang::nextstep::Syntax;

Spec parseFile(loc file)        = parse(#start[Spec], file).top;
Spec parseFile(str x, loc file) = parse(#start[Spec], x, file).top;
Spec parseString(str x)         = parse(#start[Spec], x).top;