module et_al::Eval

import et_al::Relations;
import IO;
import Set;

alias Univ = rel[str class, str atom];
alias State = map[RExpr base, rel[str,str] rels];

alias World = tuple[Univ atoms, State state];
  
rel[str,str] eval(b:base(str name, str from, str to), World w) 
  = ( {} | w.state[b] | b <- w.state );

rel[str,str] eval(id(str class), World w) = { <x, x> | str x <- w.atoms[class] };

rel[str,str] eval(compose(args), World w) 
  = ( eval(args[0], w) | it o eval(a, w) | RExpr a <- args[1..] );

rel[str,str] eval(inv(arg), World w) = eval(arg, w)<1,0>;

rel[str,str] eval(union(args), World w) 
  = ( {} | it + eval(a, w) | RExpr a <- args );

rel[str,str] eval(isect(args), World w) 
  = ( eval(head, w) | it & eval(a, w) | RExpr a <- tail )
  when <RExpr head, set[RExpr] tail> := takeOneFrom(args);

rel[str,str] eval(diff(args), World w) 
  = ( eval(args[0], w) | it - eval(a, w) | RExpr a <- args[1..] );

rel[str,str] eval(empty(), World w) = {};

rel[str,str] eval(total(str class), World w) 
  = w.atoms[class] * w.atoms[class];

rel[str,str] eval(total(str class1, str class2), World w) 
  = w.atoms[class1] * w.atoms[class2];

// TODO: type safety, not all atoms but total(dom(x), ran(x))?
rel[str,str] eval(not(x), World w) 
  = (w.atoms<1> * w.atoms<1>) - eval(x, w);

rel[str, str] eval(implies(lhs, rhs), World w)
  = eval(union({not(lhs), rhs}), w);

rel[str, str] eval(equals(lhs, rhs), World w)
  = eval(isect({implies(lhs, rhs), implies(rhs, lhs)}), w);
  
  