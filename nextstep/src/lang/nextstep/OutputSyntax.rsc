module lang::nextstep::OutputSyntax

extend lang::nextstep::Syntax;

start syntax OutputDef = "output" "{" "new" "runtime" ObjectDef* newRuntime "}";

keyword Keywords = "output";
