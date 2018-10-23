module benchmark::statemachine::Scenario

import lang::nextstep::Syntax;

import Parser;

Spec constructSpec() {
  str constr = "static {
               '   class Machine {      
               '     states: State* 
               '     initial: State
               '     
               '     invariants {
               '       // initial must be a known state
               '       initial in states
               '       // all states that are targeted in the transitions must be part of the machine
               '       states.transitions.target in states
               '     }
               '   }
               '   
               '   class State {
               '     transitions: Trans*
               '   }
               ' 
               '   class Trans  {
               '     target: State
               '   }
               ' }
               ' 
               ' runtime {
               '   class Runtime  {
               '     machine: Machine
               '     current: State
               '     visited: Visit*
               '     
               '     invariants {
               '       // the current state must be part of the states connected to the machine
               '       current in machine.states
               ' 
               '       forall s:machine.states | one (visited.state & s)
               '       forall v1:visited, v2:visited | v1 != v2 =\> v1.state != v2.state
               '     }
               '   } 
               '   
               '   class Visit {
               '     state: State
               '     nr: int
               '     
               '     // Nr must be positive
               '     invariant: nr \>= 0
               '   }
               ' }
               '
               ' migration {
               '     not old[Runtime.current] in new[Runtime.machine.states] =\> (new[Runtime.current] = new[Runtime.machine.initial])
               ' }
               '
               ' input { old static old runtime new static }";
  
  return parseString(constr);
}