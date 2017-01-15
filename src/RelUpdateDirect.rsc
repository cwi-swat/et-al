module RelUpdateDirect

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
  = implies(Expr ante, Expr cons)
  | equals(Expr lhs, Expr rhs)
  ;


Rule transitive(Expr e) = implies(compose(e, e), e);
Rule reflexive(Expr e) = implies(union(idDom(e), idRan(e)), e);
Rule symmetric(Expr e) = implies(inv(e), e);
Rule univalent(Expr e) = implies(compose(inv(e), e), idRan(e));
Rule total(Expr e) = implies(idDom(e), compose(e, inv(e)));
Rule injective(Expr e) = implies(compose(e, inv(e)), idDom(e));
Rule surjective(Expr e) = implies(idRan(e), compose(inv(e), e));

 
alias World
  = tuple[set[str] atoms, map[str name, rel[str, str] rels] state];
  

rel[str,str] eval(base(str name), World w) = ( {} | w.state[name] | name <- w.state );

rel[str,str] eval(idDom(arg), World w) = { <x, x> | str x <- eval(arg, w)<0> };

rel[str,str] eval(idRan(arg), World w) = {  <x, x> | str x <- eval(arg, w)<1> };

rel[str,str] eval(compose(lhs, rhs), World w) = eval(lhs, w) o eval(rhs, w);

rel[str,str] eval(inv(arg), World w) = eval(arg, w)<1,0>;

rel[str,str] eval(union(lhs, rhs), World w) = eval(lhs, w) + eval(rhs, w);

rel[str,str] eval(isect(lhs, rhs), World w) = eval(lhs, w) & eval(rhs, w);

rel[str,str] eval(diff(lhs, rhs), World w) = eval(lhs, w) - eval(rhs, w);

rel[str,str] eval(empty(), World w) = {};

rel[str,str] eval(total(), World w) = w.atoms * w.atoms;

rel[str,str] eval(not(x), World w) = eval(diff(total(), x), w);

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
Rule r7() = equals(base("sentBy"), compose(base("delivery"), base("provider")));


//(8) provider = ~delivery;from 
Rule r8() = equals(base("provider"), compose(inv(base("delivery")), base("from")));


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

Expr rule2expr(equals(Expr a, Expr b))
  = isect(rule2expr(implies(a, b)), rule2expr(implies(b, a))); 
 
Expr rules2expr(list[Rule] rules) 
  = ( rule2expr(rules[0]) | isect(rule2expr(rules[i]), it) | int i <- [1..size(rules)] );
 

// this is wrong: eval only ever looks in the old state, not the new
// one where certain additions/removals have already taken place.
// -> along a branch, provide the current set of updates to eval
// to allow it to correct.

Update repair(Rule rule, World w) {
  Expr exp = rule2expr(rule);
  updates = { normalize(add(t, exp), w) | t <- eval(not(exp), w) };
  return normalize(seq(updates), w);
}

 
map[Rule, Update] repair(list[Rule] rules, World w) {
  fix = ();
  for (Rule r <- rules) {
    println("Rule: <r>");
    exp = rule2expr(r);
    updates = { normalize(add(t, exp), w) | t <- eval(not(exp), w) };
    result = normalize(seq(updates), w);
    println("repair: ");
    iprintln(result);
    fix[r] = result;
  }
  return ();
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



  
