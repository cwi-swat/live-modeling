module benchmark::statemachine::Scenario2

extend benchmark::statemachine::Scenario;

Problem constructScenario2Problem(int nrOfStates) = problem(constructRelationsForScenario2(nrOfStates), constructConstraints(), constructObjectives(), nothing());

list[RelationDef] constructRelationsForScenario2(int nrOfStates) {
  if (nrOfStates < 3) {
    throw "Will only work for statemachines with more than 2 states";
  }
  
  str rels = "// ------ classes and associations (instantiated) --------------------------
             'p_Machine (mId: id) = {\<m1\>}
             'p_State (sId: id) = {\<s1\> .. \<s<nrOfStates>\>}
             'p_Trans (tId: id) = {\<t1\> .. \<t<(nrOfStates * 2) - 2>\>}
             '
             '// (I)
             'pp_states (mId: id, sId: id) = {\<m1, s1\> .. \<m1, s<nrOfStates-1>\>}
             'pp_transitions (sId: id, tId: id) = {<intercalate(",", ["\<s<i>, t<(i*2)-1>\>,\<s<i+1>, t<i*2>\>" | int i <- [1..nrOfStates]])>}
             'pp_target (tId: id, sId: id) = {<intercalate(",", ["\<t<(i*2)-1>, s<i+1>\>,\<t<i*2>, s<i>\>" | int i <- [1..nrOfStates]])>}
             'pp_initial (mId: id, sId: id) = {\<m1, s1\>}
             '
             'x_current (mId: id, sId: id) = {\<m1,s<nrOfStates>\>}
             'x_visited (sId: id, val: int) = {<intercalate(",",["\<s<i>, <i == 1 || i == nrOfStates ? "1" : "2">\>" | int i <- [1..nrOfStates+1]])>}
             '
             '// ------ classes and associations (that we are searching for) -------------
             'xx_current (mId: id, sId: id) \<= {\<m1, s1\> .. \<m1, s<nrOfStates>\>}
             'xx_visited (sId: id, val: int) \<= {\<s1, ?\> .. \<s<nrOfStates>, ?\>}
             '
             'd_current (mId: id, sId: id) \<= {\<m1, s1\> .. \<m1, s<nrOfStates>\>}
             'd_visited (sId: id, delta: int) \<= {\<s1, ?\> .. \<s<nrOfStates>, ?\>}";

  return implodeProblem(rels).relations;             
}