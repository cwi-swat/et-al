module RelAlg


//(1) addressedTo ⊢ accepted
Expr r1() = implies(base("addressedTo"), base("accepted"));
//(2) accepted ⊢ addressedTo
Expr r2() = implies(base("accepted"), base("addressedTo"));

//(3) provider ⊢ of . accepted
Expr r3() = implies(base("provider"), compose([base("of"), base("accepted")]));


//(4) of . accepted ⊢ provider
Expr r4() = implies(compose([base("of"), base("accepted")]), base("provider"));

//(5) of . from ⊢ deliveredTo
Expr r5() = implies(compose([base("of"), base("from")]), base("deliveredTo"));


//(6) ~delivery . to ⊢ deliveredTo
Expr r6() = implies(compose([inv(base("delivery")), base("to")]), base("deliveredTo"));

 
//(7) sentBy = delivery . provider 
Expr r7() = implies(base("sentBy"), compose([base("delivery"), base("provider")]));


//(8) provider = ~delivery;from 
Expr r8() = implies(base("provider"), compose([inv(base("delivery")), base("from")]));


//(9) paidBy ⊢ to
Expr r9() = implies(base("paidBy"), base("to"));


//(10) to ⊢ paidBy
Expr r10() = implies(base("to"), base("paidBy"));

Expr mySpec() = isect({r1(), r2(), r3(), r4(), r5(), r6(), r7(), r8(), r9(), r10()});


data Clause
  = clause(set[Expr] neg, set[Expr] pos);
  
set[Clause] toClauses(isect(args)) 
  = { toClause(c) | c <- args };
  
Clause toClause(union(args))
  = clause({ n | n:not(_) <- args}, { p | p <- args, not(_) !:= p });

Expr normalizeDeep(Expr e) {
  solve (e) {
    e = visit (e) {
      case Expr x => normalize(x)
    }
  }
  return e;
}
  
default Expr normalize(Expr e) = e;

Expr normalize(inv(inv(r))) = r;

Expr normalize(inv(union(args))) = union({ inv(a) | a <- args });
Expr normalize(inv(isect(args))) = isect({ inv(a) | a <- args });
Expr normalize(inv(compose(args))) = compose([ inv(a) | a <- reverse(args) ]);
Expr normalize(inv(dagger(args))) = dagger([ inv(a) | a <- reverse(args) ]);
Expr normalize(inv(not(r))) = not(inv(r));

Expr normalize(compose([qs1*, union(args), qs2*])) 
  = union({ compose([qs1*, a, qs2*]) | a <- args })
  when size(qs1) > 0 || size(qs2) > 0;

// How to prove an arb relational expression is functional?
// Depends on the rules.
//
//Expr normalize(compose([qs1*, isect(args), qs2*])) 
//  = isect({ compose([qs1*, a, qs2*]) | a <- args })
//  when isFunction(qs1[-1]), isFunction(inv(qs2[0]));

  
Expr normalize(union({qs1*, isect(args), qs2*})) 
  = isect({ union({qs1*, a, qs2*}) | a <- args });
  
Expr normalize(union({x})) = x;
Expr normalize(isect({x})) = x;
Expr normalize(compose([x])) = x;
Expr normalize(dagger([x])) = x;

Expr normalize(not(union(args))) = isect({ not(a) | a <- args });
Expr normalize(not(isect(args))) = union({ not(a) | a <- args });

Expr normalize(union({qs*, q, q})) = union({qs*, q});
Expr normalize(isect({qs*, q, q})) = isect({qs*, q});

Expr normalize(union({qs*, q, not(q)})) = total();
Expr normalize(isect({qs*, q, not(q)})) = empty();

Expr normalize(isect({rs*, r, union({qs*, not(r)})})) = isect({rs*, r, union(qs)});
Expr normalize(union({rs*, r, isect({qs*, not(r)})})) = union({rs*, r, isect(qs)});

Expr normalize(isect({rs*, r, union({qs*, r})})) = isect({rs*, r});
Expr normalize(union({rs*, r, isect({qs*, r})})) = union({rs*, r});

Expr normalize(union({rs*, total()})) = total();
Expr normalize(union({rs*, empty()})) = union(rs);

Expr normalize(isect({rs*, total()})) = isect(rs);
Expr normalize(isect({rs*, empty()})) = empty();



//  
//Expr normalize(union(isect(q, r), s)) = isect(union(q, s), union(r, s));
//
//Expr normalize(not(union(r, w))) = isect(not(r), not(s));
//Expr normalize(not(isect(r, w))) = union(not(r), not(s));
//
//// NB: this requires comm. matching... (sets as arguments?)
//
//// union({r, not(r), _*}) = total();
//Expr normalize(union(r, not(r))) = total();
//Expr normalize(isect(r, not(r))) = empty();
//
//Expr normalize(isect(r, union(not(r), s))) = isect(r, s);
//Expr normalize(union(r, isect(not(r), s))) = union(r, s);
//Expr normalize(isect(r, union(r, s))) = r;
//Expr normalize(union(r, isect(r, s))) = r;
//
//Expr normalize(union(r, total())) = total();
//Expr normalize(union(r, empty())) = r;
//
//Expr normalize(isect(r, total())) = r;
//Expr normalize(isect(r, empty())) = empty();
//
