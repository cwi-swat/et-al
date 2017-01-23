module et_al::Repair3

import et_al::Relations;
import et_al::Eval;
import et_al::Normalize;
import et_al::ToRules;

import List;
import Set;
import IO;

data Update
  = add(tuple[str, str] val, RExpr expr)
  | del(tuple[str, str] val, RExpr expr)
  | seq(set[Update] updates)
  | alt(set[Update] updates)
  ;
  
// flattening alts
Update alt({*u1, alt(set[Update] us), *u2})
  = alt(u1 + us + u2);

// flattening seqs
Update seq({*u1, seq(set[Update] us), *u2})
  = seq(u1 + us + u2);

// delete/add pairs of same tuple on same exp lead to failure
// NB: do we require normalization of expressions? syntactic equiv = not real equiv.
// or is enough because e will always (eventually) be base()?
Update seq({add(tuple[str, str] t, RExpr e), del(t, e), *_})
  = alt({});

// alt of one is the thing itself.
//Update alt({Update u}) = u;
  
// same for seq
//Update seq({Update u}) = u;

// move alts outwards
Update seq({alt(set[Update] us), *rest})
  = alt({ seq({u} + rest) | Update u <- us });

// Can't add to empty
Update add(tuple[str, str] t, empty()) = alt({});
  
// But remove is no-op
Update del(tuple[str, str] t, empty()) = seq({});

// Mut.mut. for total
Update add(tuple[str, str] t, total(_)) = seq({});
  
Update del(tuple[str, str] t, total(_)) = alt({});

// Can't add to id if tuple components differ
Update add(<str x, str y>, id(_)) = alt({})
  when x != y;

// add to union/isect/diff not
Update repair(add(tuple[str, str] t, union(args)), World w)
  = alt({repair(add(t, a), w) | RExpr a <- args });
  
Update repair(add(tuple[str, str] t, isect(args)), World w)
  = seq({repair(add(t, a), w) | RExpr a <- args });

Update repair(add(tuple[str, str] t, diff(args)), World w)
  = seq({repair(add(t, args[0]), w)} + { repair(del(t, a), w) | a <- args[1..] });
  
Update repair(add(tuple[str, str] t, not(arg)), World w)
  = repair(del(t, arg), w);
  

// del from union/isect, not
Update repair(del(tuple[str, str] t, union(args)), World w)
  = seq({repair(del(t, a), w) | a <- args });
  
Update repair(del(tuple[str, str] t, isect(args)), World w)
  = alt({repair(del(t, a), w) | a <- args }); 
  
Update repair(del(tuple[str, str] t, diff(args)), World w)
  = alt({repair(del(t, args[0]), w)} + {repair(add(t, a), w) | a <- args[1..] });

Update repair(del(tuple[str, str] t, not(arg)), World w)
  = repair(add(t, arg), w);
  

// from inverses
Update repair(add(tuple[str, str] t, inv(arg)), World w)
  = repair(add(<t[1], t[0]>, arg), w);

Update repair(del(tuple[str, str] t, inv(arg)), World w)
  = repair(del(<t[1], t[0]>, arg), w);


data RExpr
// for now...
  = compose(RExpr lhs, RExpr rhs)
  ;
  
RExpr normCompose(compose(args)) = ( args[-1] | compose(a, it) | a <- reverse(args[..-1]) ); 

Update repair(add(tuple[str, str] t, c:compose(args)), World w) 
  = repair(add(t, normCompose(c)), w);

Update repair(del(tuple[str, str] t, c:compose(args)), World w) 
  = repair(del(t, normCompose(c)), w);

// from compositions
Update repair(add(tuple[str, str] t, c:compose(lhs, rhs)), World w) {
  set[Update] subs = {};
  l = eval(lhs, w); // todo: the world here does not reflect additions in the current repair...
  r = eval(rhs, w);
  for (j <- l<1> & r<0>) {
    subs += {seq({repair(add(<t[0], j>, lhs), w), 
            repair(add(<j, t[1]>, rhs), w)})};
  }
  return alt(subs);
}

Update repair(del(tuple[str, str] t, c:compose(lhs, rhs)), World w) {
  set[Update] subs = {};
  l = eval(lhs, w);
  r = eval(rhs, w);
  for (j <- l<1> & r<0>) {
    subs += {alt({repair(del(<t[0], j>, lhs), w), 
            repair(del(<j, t[1]>, rhs), w)})};
  }
  return seq(subs);
}


Update repair(add(tuple[str, str] t, implies(lhs, rhs)), World w)
  = repair(add(t, union({not(lhs), rhs})), w);

Update repair(del(tuple[str, str] t, implies(lhs, rhs)), World w)
  = repair(del(t, union({not(lhs), rhs})), w);

Update repair(add(tuple[str, str] t, equals(lhs, rhs)), World w)
  = repair(add(t, isect({implies(lhs, rhs), implies(rhs, lhs)})), w);

Update repair(del(tuple[str, str] t, implies(lhs, rhs)), World w)
  = repair(del(t, isect({implies(lhs, rhs), implies(rhs, lhs)})), w);



default Update repair(Update u, World _) = u;



rel[str, str] violations(Rule rule, World w) = eval(not(rule.expr), w);

Update repair(Rule rule, World w) {
  updates = { repair(add(t, rule.expr), w) | t <- eval(not(rule.expr), w) };
  return seq(updates);
}



Update fix(Rule rule, World w) {
  newAlt = alt({});
  for (Update a <- repair(rule, w).updates) {
    println("REPAIRING again: <a>");
    World w2 = w;
    solve (a) {
      for (add(tuple[str,str] t, b:base(_, _, _)) <- a.updates) {
        w2.state[b] += t;
      }
      for (del(tuple[str,str] t, b:base(_, _, _)) <- a.updates) {
        w2.state[b] -= t;
      }
      a = repair(rule, w2);
      println("World:");
      iprintln(w2);
    }
    if (a != alt({})) {
      // non fail
      newAlt.updates += {a};
    }
  }
  return newAlt;
}


set[Update] least(Update u) {
  // assumes disjunctive normal form for u;
  if (u is add || u is del || u is seq) {
    return {u};
  }
  
  int smallest = -1;
  set[Update] result = {};
   
  for (Update a <- u.updates) {
    if (a is add || a is del) {
      smallest = 1;
      result += {a};
      continue;  
    }
    
    assert a is seq;
    int mySize = size(a.updates);

    if (mySize < smallest || smallest == -1) {
      smallest = mySize;
      result = {a};
    }
    if (mySize == smallest) {
      result += {a};
    }
  }
  
  return result;
}

set[Update] preferAdds(set[Update] us) {
  set[Update] result = {};
  
  int mostAdds = -1;
  
  for (Update u <- us) {
    if (u is add, mostAdds <= 1) {
      mostAdds = 1;
      result += {u};
      continue;
    }
    
    if (u is del, mostAdds <= 0) {
      mostAdds = 0;
      result += {u};
      continue;
    }
    
    if (u is del || u is add) {
      continue;
    }
    
    int numOfAdds = size({ a | a:add(_, _) <- u.updates });
    if (numOfAdds > mostAdds || mostAdds == -1) {
      mostAdds = numOfAdds;
      result = {u};
    }
    if (numOfAdds == mostAdds) {
      result += {u};
    }
  }
  
  return result;
} 


RExpr tautology() = implies(base("R", "X", "X"), base("R", "X", "X"));

RExpr transRule()
  = implies(compose([base("R", "X", "X"), base("R", "X", "X")]), base("R", "X", "X"));

RExpr reflRule()
  = implies(id("X"), base("R", "X", "X"));
  
RExpr uniRule()
  = implies(compose([inv(base("R", "X", "X")), base("R", "X", "X")]), id("X"));
   
RExpr symRule()
  = implies(inv(base("R", "X", "X")), base("R", "X", "X"));
   


/*
r = rule(|file:///|, isect({reflRule(), transRule(), uniRule()}));
repair(r, <{<"X", "1">, <"X", "2">, <"X", "3">}, (base("R", "X", "X"): {<"1", "2">, <"2", "3">})>);
*/


