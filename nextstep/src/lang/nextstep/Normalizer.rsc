/* Normalization of constraints: 
 * flattern the OO style by uncurrying expressions
 * 
 * contributors: ulyanatikhonova
 */

module lang::nextstep::Normalizer

import lang::nextstep::Syntax;
import ParseTree;

Spec normalize(Spec spec) {
  return visit (spec) {
    case c:(Class)`class <ClassName _> { <ClassBody _> }` => c_norm
      when c_norm := normalize(c)
  };
}

Class normalize(Class c) {
  className = c.name;
  
  Class result = top-down-break visit (c) {
    case (Formula)`<Formula form>` => 
         (Formula)`forall inst : <VarName className> | <Formula form>`    
  };
  
  result = visit (result) {
    case (Expr)`<VarName v>` => (Expr)`inst.<VarName v>`
      when any(f <- c.body.fields, v == f.fieldName)
     //case (Expr)`<VarName v>` : {
     //   if (f <- c.body.fields, v == f.fieldName) {
     //     insert (Expr)`classBoundVar.<VarName v>`;
     //   }     
     //} 
  };
  
  return result;
}