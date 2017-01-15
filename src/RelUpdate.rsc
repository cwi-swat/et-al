module RelUpdate

import List;
import IO;

data Expr
  = base(str name)
  | union(Expr lhs, Expr rhs)
  | isect(Expr lhs, Expr rhs)
  | diff(Expr lhs, Expr rhs)
  | not(Expr arg)
  | inv(Expr arg)
  | compose(Expr lhs, Expr rhs)
  | idRan(Expr arg)
  | idDom(Expr arg)
  | total()
  | empty()
  ;
  
  
// NB: don't distribute over intersection :-(
Expr ran(union(lhs, rhs)) = union(ran(lhs), ran(rhs));
Expr dom(union(lhs, rhs)) = union(dom(lhs), dom(rhs));

// complement does not change type of relation
Expr ran(not(arg)) = ran(arg);
Expr dom(not(arg)) = dom(arg);

Expr ran(compose(lhs, rhs)) = ran(rhs);
Expr dom(compose(lhs, rhs)) = dom(lhs);

Expr ran(inv(arg)) = dom(arg);
Expr dom(inv(arg)) = ran(arg);

Expr ran(idRan(arg)) = ran(arg);
Expr dom(idRan(arg)) = ran(arg);

Expr ran(idDom(arg)) = dom(arg);
Expr dom(idDom(arg)) = dom(arg);



data Rule
  = implies(Expr ante, Expr cons);

Rule transitive(Expr e) = implies(compose(e, e), e);
Rule reflexive(Expr e) = implies(union(idDom(e), idRan(e)), e);
Rule symmetric(Expr e) = implies(inv(e), e);
Rule univalent(Expr e) = implies(compose(inv(e), e), idRan(e));
Rule total(Expr e) = implies(idDom(e), compose(e, inv(e)));
Rule injective(Expr e) = implies(compose(e, inv(e)), idDom(e));
Rule surjective(Expr e) = implies(idRan(e), compose(inv(e), e));



 
alias World
  = tuple[set[str] atoms, map[str name, rel[str, str] rels] state];
  

void eval(base(str name), World w, void(tuple[str, str]) out) {
  for (name in w.state, tuple[str, str] t <- w.state[name]) {
    out(t);
  }
}

void eval(idDom(arg), World w, void(tuple[str, str]) out) {
  eval(arg, w, void(tuple[str, str] t) {
    out(<t[0], t[0]>);
  });
}

void eval(idRan(arg), World w, void(tuple[str, str]) out) {
  eval(arg, w, void(tuple[str, str] t) {
    out(<t[1], t[1]>);
  });
}


void eval(compose(lhs, rhs), World w, void(tuple[str, str]) out) {
 eval(lhs, w, void(tuple[str, str] t1) {
     eval(rhs, w, void(tuple[str, str] t2) {
       if (t1[1] == t2[0]) {
         out(<t1[0], t2[1]>);
       }
     });
  });
}

void eval(inv(arg), World w, void(tuple[str, str]) out) {
  eval(arg, w, void(tuple[str, str] t) {
    out(<t[1], t[0]>);
  });
}


void eval(union(lhs, rhs), World w, void(tuple[str, str]) out) {
  eval(lhs, w, out);
  eval(rhs, w, out);
}

void eval(isect(lhs, rhs), World w, void(tuple[str, str]) out) {
  eval(lhs, w, void(tuple[str, str] t1) {
     eval(rhs, w, void(tuple[str, str] t2) {
       if (t1 == t2) {
         out(t1);
       }
     });
  });
}

void eval(diff(lhs, rhs), World w, void(tuple[str, str]) out) {
  rel[str,str] rights = {};
  eval(rhs, w, void(tuple[str, str] t1) {
    rights += {t1};
  });

  eval(lhs, w, void(tuple[str, str] t2) {
     if (t2 notin rights) {
       out(t2);
     }
   });
}

void eval(empty(), World w, void(tuple[str, str]) out) {
}

void eval(total(), World w, void(tuple[str, str]) out) {
  for (str x <- w.atoms, str y <- w.atoms) {
    out(<x, y>);
  }  
}

void eval(not(x), World w, void(tuple[str,str]) out) 
  = eval(diff(total(), x), w, out);


data Update
  = add(tuple[str, str] val, Expr expr)
  | del(tuple[str, str] val, Expr expr)
  | seq(set[Update] updates)
  | alt(set[Update] updates)
  ;
  
/*
 * TODO for optimize:
 * - avoid set matching
 * - do something about "not"
 * - figure if this can be done symbolically (i.e., without the world.)
 * - propagate actual adds through the expressions of the rules.
 * - store complements and maintain them.
 *   basically: for every base("r") not(base("r")) -> base("not_r");
 *   additions to base("r") -> also del("not_r"); etc.
 *   adding to idRan/idDom  means adding to not_r
 * but do we need to do this for all intermediate terms???
 */  
  
// flattening alts
Update normalize(alt({u1*, alt(set[Update] us), u2*}), World w)
  = normalize(alt(u1 + us + u2), w);

// flattening seqs
Update normalize(seq({u1*, seq(set[Update] us), u2*}), World w)
  = normalize(seq(u1 + us + u2), w);

// delete/add pairs of same tuple on same exp cancel out
// NB: requires normalization of expressions; syntactic equiv = not real equiv.
Update normalize(seq({u1*, add(tuple[str, str] t, Expr e), u2*, del(t, e), u3*}), World w)
  = normalize(seq(u1 + u2 + u3), w);

// alt of one is the thing itself.
Update normalize(alt({Update u}), World w) = normalize(u, w);
  
// same for seq
Update normalize(seq({Update u}), World w) = normalize(u, w);

// move alts outwards
Update normalize(seq({u1*, alt(set[Update] us), u2*}), World w)
  = normalize(alt({ normalize(seq(u1 + {u} + u2), w) | Update u <- us }), w);

// eliminate things that are already compatible with the world
Update normalize(add(tuple[str, str] t, base(str r)), World w)
  = seq({}) 
  when r in w.state, t in w.state[r];

Update normalize(del(tuple[str, str] t, base(str r)), World w)
  = seq({}) 
  when r in w.state ==> t notin w.state[r];
  
// Can't add to empty
Update normalize(add(tuple[str, str] t, empty()), World w) = alt({});
  
// But remove is no-op
Update normalize(del(tuple[str, str] t, empty()), World w) = seq({});

// Mut.mut. for total
Update normalize(add(tuple[str, str] t, total()), World w) = seq({});
  
Update normalize(del(tuple[str, str] t, total()), World w) = alt({});



// add to union/isect/diff not
Update normalize(add(tuple[str, str] t, union(lhs, rhs)), World w)
  = normalize(alt({normalize(add(t, lhs), w), normalize(add(t, rhs), w)}), w);
  
Update normalize(add(tuple[str, str] t, isect(lhs, rhs)), World w)
  = normalize(seq({normalize(add(t, lhs), w), normalize(add(t, rhs), w)}), w);

Update normalize(add(tuple[str, str] t, diff(lhs, rhs)), World w)
  = normalize(seq({normalize(add(t, lhs), w), normalize(del(t, rhs), w)}), w);
  
Update normalize(add(tuple[str, str] t, not(arg)), World w)
  = normalize(del(t, arg), w);
  

// del from union/isect, not
Update normalize(del(tuple[str, str] t, union(lhs, rhs)), World w)
  = normalize(seq({normalize(del(t, lhs), w), normalize(del(t, rhs), w)}), w);
  
Update normalize(del(tuple[str, str] t, isect(lhs, rhs)), World w)
  = normalize(alt({normalize(del(t, lhs), w), normalize(del(t, rhs), w)}), w);
  
Update normalize(del(tuple[str, str] t, diff(lhs, rhs)), World w)
  = normalize(alt({normalize(del(t, lhs), w), normalize(add(t, rhs), w)}), w);

Update normalize(del(tuple[str, str] t, not(arg)), World w)
  = normalize(add(t, arg), w);
  

// from inverses
Update normalize(add(tuple[str, str] t, inv(arg)), World w)
  = normalize(add(<t[1], t[0]>, arg), w);

Update normalize(del(tuple[str, str] t, inv(arg)), World w)
  = normalize(del(<t[1], t[0]>, arg), w);


// from compositions
Update normalize(add(tuple[str, str] t, c:compose(lhs, rhs)), World w) {
  set[Update] subs = {};
  // how to express this without iterating over the sub args?
  // because this will explode big time (alts in the order of the database)
  // altAny("x", isect(ran(lhs), dom(rhs)), seq({add(<t[0], var("x")>, lhs), add(<var("x"), t[1]>, rhs)}));
  
  eval(lhs, w, void(tuple[str, str] t1) {
    eval(rhs, w, void(tuple[str, str] t2) {
       if (t1[1] == t2[0]) {
         subs += {seq({normalize(add(<t[0], t1[1]>, lhs), w), 
                  normalize(add(<t2[0], t[1]>, rhs), w)})};
       }
    });
  });
  return normalize(alt(subs), w);
}

Update normalize(del(tuple[str, str] t, c:compose(lhs, rhs)), World w) {
  // seqAll("x", isect(ran(lhs), dom(rhs)), seq({del(<t[0], var("x")>, lhs), del(<var("x"), t[1]>, rhs)}));
  set[Update] subs = {};
  eval(lhs, w, void(tuple[str, str] t1) {
    eval(rhs, w, void(tuple[str, str] t2) {
       if (t1[1] == t2[0]) {
         subs += {seq({normalize(del(<t[0], t1[1]>, lhs), w), 
                  normalize(del(<t2[0], t[1]>, rhs), w)})};
       }
    });
  });
  return normalize(seq(subs), w);
}


default Update normalize(Update u, World _) = u;



//(1) addressedTo ⊢ accepted
Rule r1() = implies(base("addressedTo"), base("accepted"));

//(2) accepted ⊢ addressedTo
Rule r2() = implies(base("accepted"), base("addressedTo"));

//(3) provider ⊢ of . accepted
Rule r3() = implies(base("provider"), compose(base("of"), base("accepted")));


//(4) of . accepted ⊢ provider
Rule r4() = implies(compose(base("of"), base("accepted")), base("provider"));

//(5) of . from ⊢ deliveredTo
Rule r5() = implies(compose(base("of"), base("from")), base("deliveredTo"));


//(6) ~delivery . to ⊢ deliveredTo
Rule r6() = implies(compose(inv(base("delivery")), base("to")), base("deliveredTo"));

 
//(7) sentBy = delivery . provider 
Rule r7() = implies(base("sentBy"), compose(base("delivery"), base("provider")));


//(8) provider = ~delivery;from 
Rule r8() = implies(base("provider"), compose(inv(base("delivery")), base("from")));


//(9) paidBy ⊢ to
Rule r9() = implies(base("paidBy"), base("to"));


//(10) to ⊢ paidBy
Rule r10() = implies(base("to"), base("paidBy"));

list[Rule] myRules() = [r1(), r2(), r3(), r4(), r5(), r6(), r7(), r8(), r9(), r10()];


int size(add(_, _)) = 1;
int size(del(_, _)) = 1;
int size(seq(list[Update] us)) = ( 0 | it + size(u) | Update u <- us );


// if contradiction: should return alt([])
// if already consistent: should return seq([])
 
Expr rule2expr(implies(Expr a, Expr c))
  = union(not(a), c); 
 
Expr rules2expr(list[Rule] rules) 
  = ( rule2expr(rules[0]) | isect(rule2expr(rules[i]), it) | int i <- [1..size(rules)] );
 
rel[str,str] eval(Expr e, World w) {
  rel[str, str] result = {};
  eval(e, w, void(tuple[str, str] t) {
    result += {t};
  });
  return result;
} 

// this is wrong: eval only ever looks in the old state, not the new
// one where certain additions/removals have already taken place.
// -> along a branch, provide the current set of updates to eval
// to allow it to correct.

Update repair(Rule rule, World w) {
  Expr exp = rule2expr(rule);
  updates = {};
  eval(not(exp), w, void(tuple[str, str] t) {
     updates += {normalize(add(t, exp), w)};
  });
  return normalize(seq(updates), w);
}

 
Update repair(list[Rule] rules, World w) {
  conj = rules2expr(rules);
  updates = {};
  eval(not(conj), w, void(tuple[str, str] t) {
     updates += {normalize(add(t, conj), w)};
  });
  result = normalize(seq(updates), w);
  return result;
}

// TODO: turn into tree corresponding to subset partial order on args of seqs.
// also: take "minimal" first (i.e., prefer adds over dels)

/*
 * consistent world, leads to seq([])
 * cannot make consistent, leads to alt([])
 * for all World w
 *   for all f <- repair(rule, world) // probaby needs all rules
 *       consistent(apply(f, world)) == true
*/

test bool notRSubRMakesTotal() =
  repair(implies(not(base("r")), base("r")), <{"x", "y"}, ()>) == seq({
    add(
      <"y","y">,
      base("r")),
    add(
      <"x","y">,
      base("r")),
    add(
      <"x","x">,
      base("r")),
    add(
      <"y","x">,
      base("r"))
  });

test bool rSubEmptyMakesEmpty()
  = repair(implies(base("r"),empty()), <{"x", "y"}, ()>) == seq({});

test bool notRSubEmptyMakesTotal() =
  repair(implies(not(base("r")), empty()), <{"x", "y"}, ()>) == seq({
    add(
      <"y","y">,
      base("r")),
    add(
      <"x","y">,
      base("r")),
    add(
      <"x","x">,
      base("r")),
    add(
      <"y","x">,
      base("r"))
  });



  
