module et_al::Tableau

import et_al::Relations;

data Signed
  = F(RExpr expr)
  | T(RExpr expr)
  ;

data Tableau
 = alt(set[Tableau] args)
 
 | seq(set[Tableau] args)
 
 // for all var, chose one of args
 | seq(Var var, set[Tableau] args)

 // for any var, do all of args
 | alt(Var var, set[Tableau] args)

 | del(Var a, Var b, RExpr arg)
 | add(Var a, Var b, RExpr arg)
 | equal(Var a, Var b)
 | nonEqual(Var a, Var b)
 ;
 
data Var
  = var(str name, str class);

// flattening alts
Tableau alt({u1*, alt(set[Tableau] us), u2*})
  = alt(u1 + us + u2);

//Tableau alt({u1*, alt(Var v, set[Tableau] us), u2*})
//  = alt(v, u1 + us + u2);

//Tableau alt(Var v, {u1*, alt(set[Tableau] us), u2*})
//  = alt(v, u1 + us + u2);

// flattening seqs
Tableau seq({u1*, seq(set[Tableau] us), u2*})
  = seq(u1 + us + u2);

//Tableau seq({u1*, seq(Var v, set[Tableau] us), u2*})
//  = seq(v, u1 + us + u2);

//Tableau seq(Var v, {u1*, seq(set[Tableau] us), u2*})
//  = seq(v, u1 + us + u2);


// alt of one is the thing itself.
Tableau alt({Tableau u}) = u;
  
// same for seq
Tableau seq({Tableau u}) = u;

// move alts outwards
Tableau seq({u1*, alt(set[Tableau] us), u2*})
  = alt({ seq(u1 + {u} + u2) | Tableau u <- us });

//Tableau seq({u1*, alt(Var v, set[Tableau] us), u2*})
//  = alt(v, { seq(u1 + {u} + u2) | Tableau u <- us });


// opposites in seq become failure ("cannot be done")
Tableau seq({add(Var a, Var b, RExpr r), del(a, b, r), *_}) 
  = alt({});
 
// opposites in alt become no-op ("doesn't matter what")
Tableau alt({add(Var a, Var b, RExpr r), del(a, b, r), *us}) 
  = alt({seq({}), *us});


Tableau derive(F(union(set[RExpr] xs)), Var a, Var b)
  = seq({ derive(F(x), a, b) | RExpr x <- xs });

Tableau derive(T(union(set[RExpr] xs)), Var a, Var b)
  = alt({ derive(T(x), a, b) | RExpr x <- xs });

Tableau derive(F(isect(set[RExpr] xs)), Var a, Var b)
  = alt({ derive(F(x), a, b) | RExpr x <- xs });

Tableau derive(T(isect(set[RExpr] xs)), Var a, Var b)
  = seq({ derive(T(x), a, b) | RExpr x <- xs });

Tableau derive(F(diff([x0, *xs])), Var a, Var b)
  = alt({ derive(F(x0), a, b), *{ derive(T(x), a, b) | RExpr x <- xs }});

Tableau derive(T(diff([x0, *xs])), Var a, Var b)
  = seq({ derive(T(x0), a, b), *{ derive(F(x), a, b) | RExpr x <- xs }});

Tableau derive(T(not(RExpr x)), Var a, Var b)
  = derive(F(x), a, b);

Tableau derive(F(not(RExpr x)), Var a, Var b)
  = derive(T(x), a, b);

Tableau derive(F(inv(RExpr x)), Var a, Var b)
  = derive(F(x), b, a);

Tableau derive(T(inv(RExpr x)), Var a, Var b)
  = derive(T(x), b, a);
  
Tableau derive(T(r:base(_, _, _)), Var a, Var b)
  = add(a, b, r);

Tableau derive(F(r:base(_, _, _)), Var a, Var b)
  = del(a, b, r);
  
Tableau derive(T(empty()), Var a, Var b)
  = alt({});

Tableau derive(F(empty()), Var a, Var b)
  = seq({});

Tableau derive(T(total(str class)), Var a, Var b)
  = derive(T(total(class, class)), a, b);

Tableau derive(F(total(str class)), Var a, Var b)
  = derive(F(total(class, class)), a, b);

Tableau derive(T(total(str f, str t)), Var a, Var b)
  = seq({})
  when a.class == f, b.class == t;

Tableau derive(T(total(str f, str t)), Var a, Var b)
  = alt({})
  when a.class != f, b.class != t;

Tableau derive(F(total(str f, str t)), Var a, Var b)
  = seq({})
  when a.class != f || b.class != t;

Tableau derive(F(total(str f, str t)), Var a, Var b)
  = alt({})
  when a.class == f, b.class == t;


Tableau derive(T(i:id(_)), Var a, Var b)
  = add(a, b, i);

Tableau derive(F(i:id(_)), Var a, Var b)
  = del(a, b, i);

//Tableau derive(T(id(str class)), Var a, Var b)
//  = add 
//
//Tableau derive(F(id(str class)), Var a, Var b)
//  = nonEqual(a, b);

Tableau derive(T(compose([x, y])), Var a, Var b)
  // for at least one c in ran(x) ∩ dom(y),
  //   add <a, c> to x, and <c, b> to y
  = alt(c, {derive(T(x), a, c), derive(T(y), c, b)})
  when Var c := newVar(ran(x)); // assume ran(x) == dom(y)
  
Tableau derive(F(compose([x, y])), Var a, Var b)
  // for all c in ran(x)  ∩ dom(y)
  //   either remove <a, c> from x, or remove <c, b> from y
  = seq(c, {derive(F(x), a, c), derive(F(y), c, b)})
  when Var c := newVar(ran(x)); // assume ran(x) == dom(y)

Tableau derive(T(compose([x, y, z, *xs])), Var a, Var b)
  = derive(T(compose([x, compose([y, z, *xs])])), a, b);
  
Tableau derive(F(compose([x, y, z, *xs])), Var a, Var b)
  = derive(F(compose([x, compose([y, z, *xs])])), a, b);

Tableau derive(T(implies(x, y)), Var a, Var b)
  = derive(T(union({not(x), y})), a, b); 
 
Tableau derive(F(implies(x, y)), Var a, Var b)
  = derive(F(union({not(x), y})), a, b); 

Tableau derive(T(equals(x, y)), Var a, Var b)
  = derive(T(isect({implies(x, y), implies(y, x)})), a, b);

Tableau derive(F(equals(x, y)), Var a, Var b)
  = derive(F(isect({implies(x, y), implies(y, x)})), a, b);
 
 
 
private int varId = -1;

Var newVar(str class) {
  varId += 1;
  return var("x_<varId>", class);
}

RExpr tautology() = implies(base("R", "X", "X"), base("R", "X", "X"));

RExpr transRule()
  = implies(compose([base("R", "X", "X"), base("R", "X", "X")]), base("R", "X", "X"));

RExpr reflRule()
  = implies(id("X"), base("R", "X", "X"));


/*
 * This assumes all expressions are well-typed
 */
 
str dom(union({x, *_})) = dom(x);
str dom(isect({x, *_})) = dom(x);
str dom(diff([x, *_])) = dom(x);
str dom(compose([x, *_])) = dom(x);
str dom(inv(x)) = ran(x);
str dom(not(x)) = dom(x);
str dom(id(c)) = c;
str dom(total(c)) = c;
str dom(total(c1, c2)) = c1;
str dom(base(_, c, _)) = c;

str ran(union({x, *_})) = ran(x);
str ran(isect({x, *_})) = ran(x);
str ran(diff([x, *_])) = ran(x);
str ran(compose([*_, x])) = ran(x);
str ran(inv(x)) = dom(x);
str ran(not(x)) = ran(x);
str ran(id(c)) = c;
str ran(total(c)) = c;
str ran(total(c1, c2)) = c2;
str ran(base(_, _, c)) = c;

// what about empty? need lub anyway?





