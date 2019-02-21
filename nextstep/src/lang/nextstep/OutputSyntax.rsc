module lang::nextstep::OutputSyntax

extend lang::nextstep::InstanceSyntax;

start syntax OutputDef = "output" "{" "new" "runtime" ObjectDef* newRuntime "}";

keyword Keywords = "output";
