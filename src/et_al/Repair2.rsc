module et_al::Repair2

import et_al::Relations;
import et_al::Eval;
import et_al::Normalize;
import et_al::ToRules;

import List;

data Elt
  = var(str name)
  | val(str atom)
  ;

data Update
  = add(tuple[Elt, Elt] val, RExpr expr)
  | del(tuple[Elt, Elt] val, RExpr expr)
  | seqAll(Elt x, RExpr expr, Update update)
  | altAny(Elt x, RExpr expr, Update update)
  | seq(set[Update] updates)
  | alt(set[Update] updates)
  ;
  
// flattening alts
Update normalize(alt({u1*, alt(set[Update] us), u2*}))
  = normalize(alt(u1 + us + u2));

// flattening seqs
Update normalize(seq({u1*, seq(set[Update] us), u2*}))
  = normalize(seq(u1 + us + u2));

// delete/add pairs of same tuple on same exp lead to failure
// NB: do we require normalization of expressions? syntactic equiv = not real equiv.
// or is enough because e will always (eventually) be base()?
Update normalize(seq({u1*, add(tuple[Elt, Elt] t, RExpr e), u2*, del(t, e), u3*}))
  = alt({});

// alt of one is the thing itself.
Update normalize(alt({Update u})) = normalize(u);
  
// same for seq
Update normalize(seq({Update u})) = normalize(u);

// move alts outwards
Update normalize(seq({u1*, alt(set[Update] us), u2*}))
  = normalize(alt({ normalize(seq(u1 + {u} + u2)) | Update u <- us }));

Update normalize(seqAll(x, dom, seq({u1*, alt(set[Update] us), u2*})))
  = normalize(alt({ normalize(seqAll(x, dom, normalize(seq(u1 + {u} + u2)))) | Update u <- us }));

// Can't add to empty
Update normalize(add(tuple[Elt, Elt] t, empty())) = alt({});
  
// But remove is no-op
Update normalize(del(tuple[Elt, Elt] t, empty())) = seq({});

// Mut.mut. for total
Update normalize(add(tuple[Elt, Elt] t, total(_))) = seq({});
  
Update normalize(del(tuple[Elt, Elt] t, total(_))) = alt({});



// add to union/isect/diff not
Update normalize(add(tuple[Elt, Elt] t, union(args)))
  = normalize(alt({normalize(add(t, a)) | RExpr a <- args }));
  
Update normalize(add(tuple[Elt, Elt] t, isect(args)))
  = normalize(seq({normalize(add(t, a)) | RExpr a <- args }));

Update normalize(add(tuple[Elt, Elt] t, diff(args)))
  = normalize(seq({normalize(add(t, args[0]))} + { normalize(del(t, a)) | a <- args[1..] }));
  
Update normalize(add(tuple[Elt, Elt] t, not(arg)))
  = normalize(del(t, arg));
  

// del from union/isect, not
Update normalize(del(tuple[Elt, Elt] t, union(args)))
  = normalize(seq({normalize(del(t, a)) | a <- args }));
  
Update normalize(del(tuple[Elt, Elt] t, isect(args)))
  = normalize(alt({normalize(del(t, a)) | a <- args })); 
  
Update normalize(del(tuple[Elt, Elt] t, diff(args)))
  = normalize(alt({normalize(del(t, args[0]))} + {normalize(add(t, a)) | a <- args[1..] }));

Update normalize(del(tuple[Elt, Elt] t, not(arg)))
  = normalize(add(t, arg));
  

// from inverses
Update normalize(add(tuple[Elt, Elt] t, inv(arg)))
  = normalize(add(<t[1], t[0]>, arg));

Update normalize(del(tuple[Elt, Elt] t, inv(arg)))
  = normalize(del(<t[1], t[0]>, arg));


data RExpr
// for now...
  = compose(RExpr lhs, RExpr rhs)
  ;
  
RExpr normCompose(compose(args)) = ( args[-1] | compose(a, it) | a <- reverse(args[..-1]) ); 

Update normalize(add(tuple[Elt, Elt] t, c:compose(args))) 
  = normalize(add(t, normCompose(c)));

Update normalize(del(tuple[Elt, Elt] t, c:compose(args))) 
  = normalize(del(t, normCompose(c)));

// from compositions
Update normalize(add(tuple[Elt, Elt] t, c:compose(lhs, rhs))) 
  = altAny(x, c, seq({add(<t[0], x>, lhs), add(<x, t[1]>, rhs)}))
  when Elt x := newVar();

Update normalize(del(tuple[Elt, Elt] t, c:compose(lhs, rhs))) 
  = seqAll(x, c, seq({del(<t[0], x>, lhs), del(<x, t[1]>, rhs)}))
  when Elt x := newVar();


int varCount = -1;
Elt newVar() {
  varCount += 1;
  return var("x_<varCount>");
}

default Update normalize(Update u) = u;

// todo: separate generating of updates (symbolically)
// from evaluating not(rule.expr):
// script = normalize(add(<var("x"), val("y")>, rule.expr))
// then when change, t <- eval(not(rule.expr), w)
// instantiate script for each t ??? 
Update repair(Rule rule, World w) {
  updates = { normalize(add(<val(t[0]), val(t[1])>, normalize(rule.expr))) | t <- eval(not(rule.expr), w) };
  return normalize(seq(updates));
}



