module et_al::Eval

import et_al::Relations;

alias Univ = rel[str class, str atom];

alias World = tuple[Univ atoms, map[RExpr base, rel[str, str] rels] state];
  
rel[str,str] eval(b:base(str name, str from, str to), World w) 
  = ( {} | w.state[b] | b <- w.state );

rel[str,str] eval(id(str class), World w) = { <x, x> | str x <- world.atoms[class] };

rel[str,str] eval(compose(args), World w) 
  = ( eval(args[0], w) | it o eval(a, w) | RExpr a <- args[1..] );

rel[str,str] eval(inv(arg), World w) = eval(arg, w)<1,0>;

rel[str,str] eval(union(args), World w) 
  = ( {} | it + eval(a, w) | RExpr a <- args );

rel[str,str] eval(isect(args), World w) 
  = ( eval(args[0], w) | it & eval(a, w) | RExpr a <- args[1..] );

rel[str,str] eval(diff(argfs), World w) 
  = ( eval(args[0], w) | it - eval(a, w) | RExpr a <- args[1..] );

rel[str,str] eval(empty(), World w) = {};

rel[str,str] eval(total(str class), World w) 
  = w.atoms[class] * w.atoms[class];

rel[str,str] eval(not(x), World w) = eval(diff(total(), x), w);
