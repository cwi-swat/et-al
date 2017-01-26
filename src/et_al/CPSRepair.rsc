module et_al::CPSRepair

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
  ;

alias K = void(set[Update]);

alias Delta
  = tuple[rel[str, str] added, rel[str, str] deleted];

alias Trail
  = map[str relation, Delta delta];
 
/* How would we do this in a mutable Object Model setting
  e.g., when concepts are classes, and tuples are pointers?

  
*/
 
 
World updateWithTrail(World w, set[Update] trail) {
  for (add(tuple[str, str] t, b:base(_, _, _)) <- trail) {
    w.state[b] += t;
  }
  for (del(tuple[str, str] t, b:base(_, _, _)) <- trail) {
    w.state[b] -= t;
  }
  return w;
} 
 
/// Base relations 
  
void repair(a:add(tuple[str,str] t, b:base(_, _, _)), World w, set[Update] trail, K k) {
  if (del(t, b) notin trail) {
    k(trail + {a});
  }
}

void repair(d:del(tuple[str,str] t, b:base(_, _, _)), World w, set[Update] trail, K k) {
  if (add(t, b) notin trail) {
    k(trail + {d});
  }
}

// Intersection

void repair(add(tuple[str, str] t, isect({x, y})), World w, set[Update] trail, K k) {
  repair(add(t, x), w, trail, (set[Update] trail2) {
    repair(add(t, y), w, trail2, k);
  });
}

void repair(add(tuple[str, str] t, isect({x, y, z, *rest})), World w, set[Update] trail, K k) 
  = repair(add(t, isect({x, isect({y, z, *rest})})), w, trail, k);

void repair(del(tuple[str, str] t, isect({x, y})), World w, set[Update] trail, K k) {
  repair(del(t, x), w, trail, k);
  repair(del(t, y), w, trail, k);
}

void repair(del(tuple[str, str] t, isect({x, y, z, *rest})), World w, set[Update] trail, K k) 
  = repair(del(t, isect({x, isect({y, z, *rest})})), w, trail, k);

// Union

void repair(add(tuple[str, str] t, union({x, y})), World w, set[Update] trail, K k) {
  repair(add(t, x), w, trail, k);
  repair(add(t, y), w, trail, k);
}

void repair(add(tuple[str, str] t, union({x, y, z, *rest})), World w, set[Update] trail, K k) 
  = repair(add(t, union({x, union({y, z, *rest})})), w, trail, k);

void repair(del(tuple[str, str] t, union({x, y})), World w, set[Update] trail, K k) {
  repair(del(t, x), w, trail, (set[Update] trail2) {
    repair(del(t, y), w, trail2, k);
  });
}

void repair(del(tuple[str, str] t, union({x, y, z, *rest})), World w, set[Update] trail, K k) 
  = repair(del(t, union({x, union({y, z, *rest})})), w, trail, k);

// Not

void repair(add(tuple[str, str] t, not(x)), World w, set[Update] trail, K k) 
  = repair(del(t, x), w, trail, k);

void repair(del(tuple[str, str] t, not(x)), World w, set[Update] trail, K k) 
  = repair(add(t, x), w, trail, k);

// Inv

void repair(add(tuple[str, str] t, inv(x)), World w, set[Update] trail, K k) 
  = repair(add(<t[1], t[0]>, x), w, trail, k);

void repair(del(tuple[str, str] t, inv(x)), World w, set[Update] trail, K k) 
  = repair(del(<t[1], t[0]>, x), w, trail, k);

// Implies

void repair(add(tuple[str, str] t, implies(x, y)), World w, set[Update] trail, K k) 
  = repair(add(t, union({not(x), y})), w, trail, k);  
  
// Equals

void repair(add(tuple[str, str] t, equals(x, y)), World w, set[Update] trail, K k) 
  = repair(add(t, isect({implies(x, y), implies(y, x)})), w, trail, k);
  
// Compose

void repair(add(tuple[str, str] t, compose([x, y])), World w, set[Update] trail, K k) {
  w2 = updateWithTrail(w, trail);
  l = eval(x, w2); 
  r = eval(y, w2);
  for (j <- l<1> & r<0>) {
    // for any j, remove from both sides.
    repair(add(<t[0], j>, x), w, trail, (set[Update] trail2) {
      repair(add(<j, t[1]>, y), w, trail, k);
    });
  }
}

void repair(del(tuple[str, str] t, compose([x, y])), World w, set[Update] trail, K k) {
  w2 = updateWithTrail(w, trail);
  l = eval(x, w2); 
  r = eval(y, w2);
  
  
  K make(str j, K k) {
    return (set[Update] tr) {
      repair(del(<t[0], j>, x), w, tr, k);
      repair(del(<j, t[1]>, y), w, tr, k);
    };
  }
  
  // for all j, remove either left, or right
  k = ( k | make(j, it) | j <- l<1> & r<0> ); 
  k(trail);  
}

void repair(add(tuple[str, str] t, compose([x, y, z, *rest])), World w, set[Update] trail, K k) 
  = repair(add(t, compose([x, compose([y, z, *rest])])), w, trail, k);

void repair(del(tuple[str, str] t, compose([x, y, z, *rest])), World w, set[Update] trail, K k) 
  = repair(del(t, compose([x, compose([y, z, *rest])])), w, trail, k);

// Id

void repair(add(tuple[str, str] t, id(str class)), World w, set[Update] trail, K k) {
  if (t[0] == t[1]) {
    k(trail + {add(t, id(class))});
  }
}

void repair(del(tuple[str, str] t, id(str class)), World w, set[Update] trail, K k) {
  if (t[0] == t[1]) {
    k(trail + {del(t, id(class))});
  }
}

default void repair(Update u, World w, set[Update] trail, K k) {
  println("missed a case: <u>");
} 

//// Total
//void repair(add(tuple[str, str] t, id(str class)), World w, set[Update] trail, K k) {
//  if (t[0] == t[1]) {
//    k(trail + {add(t, id(class))});
//  }
//}



RExpr tautology() = implies(base("R", "X", "X"), base("R", "X", "X"));

RExpr transRule()
  = implies(compose([base("R", "X", "X"), base("R", "X", "X")]), base("R", "X", "X"));

RExpr reflRule()
  = implies(id("X"), base("R", "X", "X"));
  
RExpr uniRule()
  = implies(compose([inv(base("R", "X", "X")), base("R", "X", "X")]), id("X"));
   
RExpr symRule()
  = implies(inv(base("R", "X", "X")), base("R", "X", "X"));
 
RExpr surRule() 
  = implies(id("Y"), compose([inv(base("R", "X", "Y")), base("R", "X", "Y")])); 
  
RExpr injRule()
  = implies(compose([base("R", "X", "Y"), inv(base("R", "X", "Y"))]), id("X"));  


bool leq(set[Update] x, set[Update] y) {
  if (numOfAdds(x) > numOfAdds(y)) {
    return true;
  }
  if (numOfAdds(x) == numOfAdds(y)) {
    return size(x) <= size(y);
  }
}
  
set[set[Update]] least(set[set[Update]] u) {
  int smallest = -1;
  set[set[Update]] result = {};
   
  for (set[Update] a <- u) {
    int mySize = size(a);

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
  
set[set[Update]] repair(Rule rule, World w) {
  result = repair(rule, w, {});
  
  // ok, this works, but obviously seems extremely slow.
  // irl we would of course do it per rule, and only if a 
  // rule is affected by an update to a base relation.
  
  solve (result) {
    newResult = {};
    for (set[Update] tr <- result) {
      newResult += repair(rule, w, tr);
    }    
    result = newResult;
  } 
  
  return result;
}  
  
set[set[Update]] repair(Rule rule, World w, set[Update] theTrail) {
  alts = {};
  K k = (set[Update] trail) {
    //println(trail);
    alts += {trail};
  };

  K make(tuple[str, str] t, K k0) {
    return (set[Update] tr) {
      repair(add(t, rule.expr), w, tr, k0);
    };
  }

  k = ( k | make(t, it) | t <- eval(not(rule.expr), updateWithTrail(w, theTrail)) );
  
  k(theTrail);
  
  return alts;
}

  
