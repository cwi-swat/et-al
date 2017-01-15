module et_al::Repair

import et_al::Relations;
import et_al::Eval;
import et_al::ToRules;

import List;

data Update
  = add(tuple[str, str] val, Expr expr)
  | del(tuple[str, str] val, Expr expr)
  | seq(set[Update] updates)
  | alt(set[Update] updates)
  ;
  
// flattening alts
Update normalize(alt({u1*, alt(set[Update] us), u2*}), World w)
  = normalize(alt(u1 + us + u2), w);

// flattening seqs
Update normalize(seq({u1*, seq(set[Update] us), u2*}), World w)
  = normalize(seq(u1 + us + u2), w);

// delete/add pairs of same tuple on same exp lead to failure
// NB: do we require normalization of expressions? syntactic equiv = not real equiv.
// or is enough because e will always (eventually) be base()?
Update normalize(seq({u1*, add(tuple[str, str] t, Expr e), u2*, del(t, e), u3*}), World w)
  = alt({});

// alt of one is the thing itself.
Update normalize(alt({Update u}), World w) = normalize(u, w);
  
// same for seq
Update normalize(seq({Update u}), World w) = normalize(u, w);

// move alts outwards
Update normalize(seq({u1*, alt(set[Update] us), u2*}), World w)
  = normalize(alt({ normalize(seq(u1 + {u} + u2), w) | Update u <- us }), w);

// eliminate things that are already compatible with the world
Update normalize(add(tuple[str, str] t, b:base(_, _, _)), World w)
  = seq({}) 
  when b in w.state, t in w.state[r];

Update normalize(del(tuple[str, str] t, b:base(_, _, _)), World w)
  = seq({}) 
  when b in w.state ==> t notin w.state[b];
  
// Can't add to empty
Update normalize(add(tuple[str, str] t, empty()), World w) = alt({});
  
// But remove is no-op
Update normalize(del(tuple[str, str] t, empty()), World w) = seq({});

// Mut.mut. for total
Update normalize(add(tuple[str, str] t, total(_)), World w) = seq({});
  
Update normalize(del(tuple[str, str] t, total(_)), World w) = alt({});



// add to union/isect/diff not
Update normalize(add(tuple[str, str] t, union(args)), World w)
  = normalize(alt({normalize(add(t, a), w) | RExpr a <- args }), w);
  
Update normalize(add(tuple[str, str] t, isect(args)), World w)
  = normalize(seq({normalize(add(t, a), w) | RExpr a <- args }), w);

Update normalize(add(tuple[str, str] t, diff(args)), World w)
  = normalize(seq({normalize(add(t, args[0]), w)} + { normalize(del(t, a), w) | a <- args[1..] }), w);
  
Update normalize(add(tuple[str, str] t, not(arg)), World w)
  = normalize(del(t, arg), w);
  

// del from union/isect, not
Update normalize(del(tuple[str, str] t, union(args)), World w)
  = normalize(seq({normalize(del(t, a), w) | a <- args }), w);
  
Update normalize(del(tuple[str, str] t, isect(args)), World w)
  = normalize(alt({normalize(del(t, a), w) | a <- args }), w); 
  
Update normalize(del(tuple[str, str] t, diff(args)), World w)
  = normalize(alt({normalize(del(t, args[0]), w)} + {normalize(add(t, a), w) | a <- args[1..] }), w);

Update normalize(del(tuple[str, str] t, not(arg)), World w)
  = normalize(add(t, arg), w);
  

// from inverses
Update normalize(add(tuple[str, str] t, inv(arg)), World w)
  = normalize(add(<t[1], t[0]>, arg), w);

Update normalize(del(tuple[str, str] t, inv(arg)), World w)
  = normalize(del(<t[1], t[0]>, arg), w);


data RExpr
// for now...
  = compose(RExpr lhs, RExpr rhs)
  ;
  
RExpr normCompose(compose(args)) = ( args[-1] | compose(a, it) | a <- reverse(args[..-1]) ); 

Update normalize(add(tuple[str, str] t, c:compose(args)), World w) 
  = normalize(add(t, normCompose(c)), w);

Update normalize(del(tuple[str, str] t, c:compose(args)), World w) 
  = normalize(del(t, normCompose(c)), w);

// from compositions
Update normalize(add(tuple[str, str] t, c:compose(lhs, rhs)), World w) {
  set[Update] subs = {};
  // how to express this without iterating over the sub args?
  // because this will explode big time (alts in the order of the database)
  // altAny("x", isect(ran(lhs), dom(rhs)), seq({add(<t[0], var("x")>, lhs), add(<var("x"), t[1]>, rhs)}));
  
  l = eval(lhs, w);
  r = eval(rhs, w);
  for (j <- l<1> & r<0>) {
    subs += {seq({normalize(add(<t[0], j>, lhs), w), 
            normalize(add(<j, t[1]>, rhs), w)})};
  }
  return normalize(alt(subs), w);
}

Update normalize(del(tuple[str, str] t, c:compose(lhs, rhs)), World w) {
  // seqAll("x", isect(ran(lhs), dom(rhs)), seq({del(<t[0], var("x")>, lhs), del(<var("x"), t[1]>, rhs)}));
  set[Update] subs = {};
  l = eval(lhs, w);
  r = eval(rhs, w);
  for (j <- l<1> & r<0>) {
    subs += {seq({normalize(del(<t[0], j>, lhs), w), 
            normalize(del(<j, t[1]>, rhs), w)})};
  }
  return normalize(seq(subs), w);
}

default Update normalize(Update u, World _) = u;

Update repair(Rule rule, World w) {
  updates = { normalize(add(t, exp), w) | t <- eval(not(rule.expr), w) };
  return normalize(seq(updates), w);
}

