module benchmark::statemachine::Scenario

import ide::CombinedAST;
import ide::CombinedImploder;

import util::Maybe;
import List;  

list[AlleFormula] constructConstraints() {
  str constr = "// ------ types of associations --------------------------------------------
               'xx_current ⊆ p_Machine ⨯ p_State
               'xx_visited[sId] = pp_states[sId]
               '
               'd_current ⊆ p_Machine ⨯ p_State
               'd_visited[sId] = xx_visited[sId]
               '
               '// ===== Semantic constraints for an(any) execution state of a program: R(p, x) ===================================
               '// [1..1] for current state
               '∀ m ∈ p_Machine | one xx_current ⨝ m
               '
               '// Current state of a machine is one of its states
               '∀ c ∈ xx_current | one pp_states ⨝ c[mId] ⨝ c[sId]
               '
               '// Visited is bigger than zero 
               '∀ v ∈ xx_visited | some (v where val \>= 0)
               '
               '// Every tuple in the trace has a corresponding transition in the machine
               '//∀ t ∈ xx_Trace[sId,next] | t ⊆ (pp_transitions ⨝ pp_target[sId as next])[sId,next]
               '
               '// Every (next) state in the trace is reachable from the initial state (via the transitive closure of the trace)
               '//∀ t ∈ xx_Trace[next] | t ⊆ (pp_initial[sId] ⨝ ^\<sId,next\>xx_Trace[sId,next])[next]
               ' 
               '// Visited is equal to the number of appearences of the state in the execution trace (as a source of a transition)
               '//∀ s ∈ xx_visited | some (((s ⨝ xx_Trace)[count() as nr] ⨯ s) where nr = val)
               '
               '// Current state appears in the trace (as a next for some tuple), unless the trace is empty
               '//(some xx_Trace ⇒ xx_current[sId] ⊆ xx_Trace[next][next as sId]) ∧ 
               '//  (no xx_Trace ⇒ xx_current[sId] = pp_initial[sId])
               '//(xx_current[sId] ⊆ xx_Trace[next][next as sId]) ∨ (xx_current[sId] = pp_initial[sId] ∧ no xx_Trace)
               '
               '// ===== Migration instructions: M(p, s, x) ======================================================================
               '// Use initial state as the default current state if the current state has been removed from the program          
               '¬(x_current[sId] ⊆ pp_states[sId]) ⇒ xx_current[sId] = pp_initial[sId]
               '
               '// ===== Distance between execution states d(s, x) ===============================================================
               '// Set-based difference for the current state and the trace
               'd_current = (x_current ∖ xx_current) ∪ (xx_current ∖ x_current)
               '//d_Trace = (x_Trace ∖ xx_Trace) ∪ (xx_Trace ∖ x_Trace)
               '
               '// Distance between visited is a vector of differences |s-x|, united with plain values |x| for the newly added states
               '∀ s ∈ xx_visited[sId] ∩ x_visited[sId] | 
               '  some (s ⨝ d_visited ⨝ x_visited ⨝ xx_visited[val as xVal]) where (delta = |val - xVal|)
               '∀ s ∈ xx_visited[sId] ∖ x_visited[sId] |  
               '  some (s ⨝ d_visited ⨝ xx_visited) where (delta = val)";
  
  return implodeProblem(constr).constraints;
}

Maybe[ObjectiveSection] constructObjectives() {
  str objs = "// The goal is to minimize this distance
             'objectives (lex): minimize d_visited[sum(delta)], minimize d_current[count()]";
  
  return implodeProblem(objs).objectiveSec; 
}