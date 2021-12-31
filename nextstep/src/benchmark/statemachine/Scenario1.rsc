module benchmark::statemachine::Scenario1

extend benchmark::statemachine::Scenario;
import lang::nextstep::Syntax;

import List;
import ParseTree;

import IO;

Spec constructScenario1(int nrOfStates) {
  Spec spc = constructSpec();
  InstanceDef input = constructInput(nrOfStates);
  
  spc.instance = input;
  
  println(spc);
  
  return spc;
}
 
InstanceDef constructInput(int nrOfStates) {
  if (nrOfStates < 3) {
    throw "Will only work for statemachines with more than 2 states";
  }
  
  str genStateAndTrans(int nr) =
              "<for (int i <- [0..nr]) {>
              'State state_<i> <if (i == 0) {>
              '  transitions = t0 <} else {> <if (i == nr-1) {>
              '  transitions = t<i*2-1> <} else {>
              '  transitions = t<i*2-1>, t<i*2> <}><}>
              '<}><for (int i <- [0..nr]) {><if (i == 0) {>
              'Trans t0 
              '  target = state_1 <} else {><if (i == nr-1) {>
              'Trans t<i*2-1>
              '  target = state_<i-1><} else {>
              'Trans t<i*2-1>
              '  target = state_<i+1>
              '
              'Trans t<i*2>
              '  target = state_<i-1>
              '<}><}>
              '<}>";  
              
  str input = "input {
              '  old static
              '    Machine doors
              '      states = <intercalate(", ", ["state_<i>" | int i <- [0..nrOfStates-1]])>
              '      initial = state_0
              '
              '    <genStateAndTrans(nrOfStates-1)>
              '
              '  old runtime
              '    Runtime x
              '      machine = doors
              '      current = state_<nrOfStates-2>
              '      visited = <intercalate(", ", ["v<i>" | int i <- [0..nrOfStates-1]])>
              '    <for (int i <- [0..nrOfStates-1]) {>
              '    Visit v<i>
              '      state = state_<i><if (i != nrOfStates-2) {>
              '      nr = 1 <} else {>
              '      nr = 0 <}>
              '    <}>   
              '    
              '  new static
              '    Machine doors
              '      states = <intercalate(", ", ["state_<i>" | int i <- [0..nrOfStates]])>
              '      initial = state_0
              '
              '    <genStateAndTrans(nrOfStates)>              
              '}";
                      
  return parse(#InstanceDef, input);             
}


