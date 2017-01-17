module et_al::Normalize

import et_al::Relations;

RExpr normalize(RExpr e) {
  solve (e) {
    e = visit (e) {
      case RExpr x => normalizeStep(x)
    }
  }
  return e;
}
  
default RExpr normalizeStep(RExpr e) = e;

RExpr normalizeStep(inv(inv(r))) = r;

RExpr normalizeStep(inv(union(args))) = union({ inv(a) | a <- args });
RExpr normalizeStep(inv(isect(args))) = isect({ inv(a) | a <- args });
RExpr normalizeStep(inv(compose(args))) = compose([ inv(a) | a <- reverse(args) ]);
RExpr normalizeStep(inv(dagger(args))) = dagger([ inv(a) | a <- reverse(args) ]);
RExpr normalizeStep(inv(not(r))) = not(inv(r));

RExpr normalizeStep(compose([qs1*, union(args), qs2*])) 
  = union({ compose(qs1 + [a] + qs2) | a <- args })
  when size(qs1) > 0 || size(qs2) > 0;

// How to prove an arb relational expression is functional?
// Depends on the rules.
//
//RExpr normalizeStep(compose([qs1*, isect(args), qs2*])) 
//  = isect({ compose([qs1*, a, qs2*]) | a <- args })
//  when isFunction(qs1[-1]), isFunction(inv(qs2[0]));

  
RExpr normalizeStep(union({qs1*, isect(args), qs2*})) 
  = isect({ union(qs1 + {a} + qs2) | a <- args });
  
RExpr normalizeStep(union({x})) = x;
RExpr normalizeStep(isect({x})) = x;
RExpr normalizeStep(compose([x])) = x;
RExpr normalizeStep(dagger([x])) = x;

RExpr normalizeStep(not(union(args))) = isect({ not(a) | a <- args });
RExpr normalizeStep(not(isect(args))) = union({ not(a) | a <- args });

RExpr normalizeStep(union({qs*, q, q})) = union({*qs, q});
RExpr normalizeStep(isect({qs*, q, q})) = isect({*qs, q});

RExpr normalizeStep(union({qs*, q, not(q)})) = total();
RExpr normalizeStep(isect({qs*, q, not(q)})) = empty();

RExpr normalizeStep(isect({rs*, r, union({qs*, not(r)})})) = isect({*rs, r, union(qs)});
RExpr normalizeStep(union({rs*, r, isect({qs*, not(r)})})) = union({*rs, r, isect(qs)});

RExpr normalizeStep(isect({rs*, r, union({qs*, r})})) = isect({*rs, r});
RExpr normalizeStep(union({rs*, r, isect({qs*, r})})) = union({*rs, r});

RExpr normalizeStep(union({rs*, total()})) = total();
RExpr normalizeStep(union({rs*, empty()})) = union(rs);

RExpr normalizeStep(isect({rs*, total()})) = isect(rs);
RExpr normalizeStep(isect({rs*, empty()})) = empty();

RExpr normalizeStep(equals(lhs, rhs)) 
  = isect({implies(lhs, rhs), implies(rhs, lhs)});
  
RExpr normalizeStep(implies(lhs, rhs)) 
  = union({not(lhs), rhs});