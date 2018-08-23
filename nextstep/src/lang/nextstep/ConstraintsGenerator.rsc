/* Generation of constraints: 
 * - structure (from Nextep structure definition to AlleAlle formulas)
 * - semantic (from Nextep invariants to AlleAlle formulas)
 * - migration (from Nextep migration rules to AlleAlle formulas)
 * 
 * contributors: ulyanatikhonova, joukestoel
 */
module lang::nextstep::ConstraintsGenerator

import lang::nextstep::Extractor;
import lang::nextstep::Syntax;
import translation::AST;                    
import translation::theories::integer::AST; 

list[AlleFormula] generateAlleConstraints(Spec spc, Models models) {
  return [];
}

