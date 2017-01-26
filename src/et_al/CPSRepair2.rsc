module et_al::CPSRepair2


import et_al::Relations;
import et_al::Eval;
import et_al::Normalize;
import et_al::ToRules;

import List;
import Set;
import Map;
import IO;


alias K = void(Trail);

alias RelDelta
  = tuple[map[RExpr, rel[str, str]] added, map[RExpr, rel[str, str]] deleted];

alias AtomDelta
  = tuple[map[str, set[str]] added, map[str, set[str]] deleted];

alias Trail
  = tuple[AtomDelta atoms,  RelDelta rels];
 
 
void printTrail(Trail t) {
  println("TRAIL: ");
  if (t == <<(), ()>, <(), ()>>) {
    println("no change");
    return;
  }
  for (str class <- t.atoms.added) {
    println("New atoms added to class <class>:");
    for (str a <- t.atoms.added[class]) {
      println("  <a>");
    }
  }
  for (str class <- t.atoms.deleted) {
    println("Deleted atoms from class <class>:");
    for (str a <- t.atoms.deleted[class]) {
      println("  <a>");
    }
  }
  for (RExpr b <- t.rels.added) {
    if (t.rels.added[b] != {}) { 
      println("New tuples added to <b.name>: <b.from> × <b.to>");
      for (tuple[str, str] tu <- t.rels.added[b]) {
        println("  <tu>");
      }
    }
  }
  for (RExpr b <- t.rels.deleted) {
    if (t.rels.deleted[b] != {}) { 
      println("Removed tuples from <b.name>: <b.from> × <b.to>");
      for (tuple[str, str] tu <- t.rels.deleted[b]) {
        println("  <tu>");
      }
    }
  }
  
} 
 
/* How would we do this in a mutable Object Model setting
  e.g., when concepts are classes, and tuples are pointers?  
*/
 
data Update
  = add(tuple[str, str] val, RExpr expr)
  | del(tuple[str, str] val, RExpr expr)
  ;


World updateWithTrail(World w, Trail trail) {
  //println("UPDATE: <trail>");
  for (RExpr b <- trail.rels.added) {
    w.state[b] = w.state[b] + trail.rels.added[b];
  }
  for (RExpr b <- trail.rels.deleted) {
    w.state[b] = w.state[b] - trail.rels.deleted[b];
  }
  for (str c <- trail.atoms.added) {
    w.atoms += { <c, a> | str a <- trail.atoms.added[c] };
  }
  for (str c <- trail.atoms.deleted) {
    w.atoms -= { <c, a> | str a <- trail.atoms.deleted[c] };
  }
  return w;
} 

void repair(Update u, World w, Trail trail, K k) {
  println("Repairing: <u>");
  _repair(u, w, trail, k);
}
 
/// Base relations 
  
void _repair(add(tuple[str,str] t, b:base(_, _, _)), World w, Trail trail, K k) {
  println("ADD <trail>");
  if (b notin trail.rels.added) {
    trail.rels.added[b] = {};
  }
  if (b notin trail.rels.deleted) {
    trail.rels.deleted[b] = {};
  }
  if (t notin trail.rels.deleted[b]) {
    trail.rels.added[b] += {t};
    println("  continuing with <trail>");
    k(trail);
  }
}

void _repair(d:del(tuple[str,str] t, b:base(_, _, _)), World w, Trail trail, K k) {
  println("DEL: <trail>");
  if (b notin trail.rels.added) {
    trail.rels.added[b] = {};
  }
  if (b notin trail.rels.deleted) {
    trail.rels.deleted[b] = {};
  }
  if (t notin trail.rels.added[b]) {
    trail.rels.deleted[b] += {t};
    println("  continuing with <trail>");
    k(trail);
  }
}

// Intersection

void _repair(add(tuple[str, str] t, isect({x, y})), World w, Trail trail, K k) {
  repair(add(t, x), w, trail, (Trail trail2) {
    repair(add(t, y), w, trail2, k);
  });
}

void _repair(add(tuple[str, str] t, isect({x, y, z, *rest})), World w, Trail trail, K k) 
  = repair(add(t, isect({x, isect({y, z, *rest})})), w, trail, k);

void _repair(del(tuple[str, str] t, isect({x, y})), World w, Trail trail, K k) {
  repair(del(t, x), w, trail, k);
  repair(del(t, y), w, trail, k);
}

void _repair(del(tuple[str, str] t, isect({x, y, z, *rest})), World w, Trail trail, K k) 
  = repair(del(t, isect({x, isect({y, z, *rest})})), w, trail, k);

// Union

void _repair(add(tuple[str, str] t, union({x, y})), World w, Trail trail, K k) {
  repair(add(t, x), w, trail, k);
  repair(add(t, y), w, trail, k);
}

void _repair(add(tuple[str, str] t, union({x, y, z, *rest})), World w, Trail trail, K k) 
  = repair(add(t, union({x, union({y, z, *rest})})), w, trail, k);

void _repair(del(tuple[str, str] t, union({x, y})), World w, Trail trail, K k) {
  repair(del(t, x), w, trail, (Trail trail2) {
    repair(del(t, y), w, trail2, k);
  });
}

void _repair(del(tuple[str, str] t, union({x, y, z, *rest})), World w, Trail trail, K k) 
  = repair(del(t, union({x, union({y, z, *rest})})), w, trail, k);

// Diff

void _repair(add(tuple[str, str] t, diff([x, y, z, *rest])), World w, Trail trail, K k) 
  = repair(add(t, diff([x, union({y, z, *rest})])), w, trail, k);

void _repair(del(tuple[str, str] t, diff([x, y, z, *rest])), World w, Trail trail, K k) 
  = repair(del(t, diff([x, union({y, z, *rest})])), w, trail, k);

void _repair(add(tuple[str, str] t, diff([x, y])), World w, Trail trail, K k) {
  repair(add(t, x), w, trail, void(Trail trail2) {
    repair(del(t, y), w, trail2, k);
  });
} 

void _repair(del(tuple[str, str] t, diff([x, y])), World w, Trail trail, K k) {
  repair(del(t, x), w, trail, k);
  repair(add(t, y), w, trail, k);
} 

// Not

void _repair(add(tuple[str, str] t, not(x)), World w, Trail trail, K k) 
  = repair(del(t, x), w, trail, k);

void _repair(del(tuple[str, str] t, not(x)), World w, Trail trail, K k) 
  = repair(add(t, x), w, trail, k);

// Inv

void _repair(add(tuple[str, str] t, inv(x)), World w, Trail trail, K k) 
  = repair(add(<t[1], t[0]>, x), w, trail, k);

void _repair(del(tuple[str, str] t, inv(x)), World w, Trail trail, K k) 
  = repair(del(<t[1], t[0]>, x), w, trail, k);

// Implies

void _repair(add(tuple[str, str] t, implies(x, y)), World w, Trail trail, K k) 
  = repair(add(t, union({not(x), y})), w, trail, k);  

void _repair(del(tuple[str, str] t, implies(x, y)), World w, Trail trail, K k) 
  = repair(del(t, union({not(x), y})), w, trail, k);  
  
// Equals

void _repair(add(tuple[str, str] t, equals(x, y)), World w, Trail trail, K k) 
  = repair(add(t, isect({implies(x, y), implies(y, x)})), w, trail, k);

void _repair(del(tuple[str, str] t, equals(x, y)), World w, Trail trail, K k) 
  = repair(del(t, isect({implies(x, y), implies(y, x)})), w, trail, k);
  
// Compose

void _repair(add(tuple[str, str] t, compose([x, y])), World w, Trail trail, K k) {
  w2 = updateWithTrail(w, trail);
  l = eval(x, w2); 
  r = eval(y, w2);
  for (j <- l<1> & r<0>) {
    // for any j, remove from both sides.
    repair(add(<t[0], j>, x), w, trail, (Trail trail2) {
      repair(add(<j, t[1]>, y), w, trail, k);
    });
  }
}

void _repair(del(tuple[str, str] t, compose([x, y])), World w, Trail trail, K k) {
  w2 = updateWithTrail(w, trail);
  l = eval(x, w2); 
  r = eval(y, w2);
  
  
  K make(str j, K k) {
    return (Trail tr) {
      repair(del(<t[0], j>, x), w, tr, k);
      repair(del(<j, t[1]>, y), w, tr, k);
    };
  }
  
  // for all j, remove either left, or right
  k = ( k | make(j, it) | j <- l<1> & r<0> ); 
  k(trail);  
}

void _repair(add(tuple[str, str] t, compose([x, y, z, *rest])), World w, Trail trail, K k) 
  = repair(add(t, compose([x, compose([y, z, *rest])])), w, trail, k);

void _repair(del(tuple[str, str] t, compose([x, y, z, *rest])), World w, Trail trail, K k) 
  = repair(del(t, compose([x, compose([y, z, *rest])])), w, trail, k);

// Id

// is this correct?
void _repair(add(tuple[str, str] t, id(str class)), World w, Trail trail, K k) {
  if (t[0] == t[1], t[0] in w.atoms[class]) {
    k(trail); 
  }
  return;
  
  //if (t[0] == t[1]) {
  //  if (class notin trail.atoms.added) {
  //    trail.atoms.added[class] = {};
  //  }
  //  if (class notin trail.atoms.deleted) {
  //    trail.atoms.deleted[class] = {};
  //  }
  //  if (t[0] notin trail.atoms.deleted[class]) {
  //    trail.atoms.added[class] += {t[0]};
  //    k(trail);
  //  }
  //}
}

void _repair(del(tuple[str, str] t, id(str class)), World w, Trail trail, K k) {
  if (t[0] == t[1], t[0] notin w.atoms[class]) {
    k(trail); 
  }
  if (t[0] != t[1]) {
    k(trail);
  }
  return;
  
  //if (t[0] == t[1]) {
  //  if (class notin trail.atoms.added) {
  //    trail.atoms.added[class] = {};
  //  }
  //  if (class notin trail.atoms.deleted) {
  //    trail.atoms.deleted[class] = {};
  //  }
  //  if (t[0] notin trail.atoms.added[class]) {
  //    trail.atoms.deleted[class] += {t[0]};
  //    k(trail);
  //  }
  //}
}

// empty

void _repair(del(tuple[str, str] t, empty()), World w, Trail trail, K k) {
  k(trail); // ???
}

void _repair(add(tuple[str, str] t, empty()), World w, Trail trail, K k) {
}


default void _repair(Update u, World w, Trail trail, K k) {
  println("missed a case: <u>");
} 

//// Total
//void _repair(add(tuple[str, str] t, id(str class)), World w, Trail trail, K k) {
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
  = implies(id("Y"), compose([inv(base("R", "X", "X")), base("R", "X", "X")])); 
  
RExpr injRule()
  = implies(compose([base("R", "X", "X"), inv(base("R", "X", "X"))]), id("X"));  

RExpr weirdRule()
  = equals(base("R", "X", "X"), id("X"));


list[set[Trail]] order(set[Trail] trails) {
  
  int numOfAdds(Trail t) {
    return ( 0 | it + size(t.rels.added[b]) | b <- t.rels.added );
  }
  
  map[int, set[Trail]] part = ();
  
  for (Trail t <- trails) {
    int n = numOfAdds(t);
    if (n notin part) {
      part[n] = {};
    }
    part[n] += {t};
  }
  
  return [ part[i] | int i <- reverse(sort(toList(domain(part)))) ];
}

set[Trail] least(set[Trail] trails) {

  int trailSize(Trail t) {
    return ( 0 | it + size(t.rels.added[b]) | b <- t.rels.added )
       + ( 0 | it + size(t.rels.deleted[b]) | b <- t.rels.deleted );
  }

  result = {};
  int n = -1;
  lst = order(trails);
  for (Trail t <- lst[0]) {
    int ts = trailSize(t);
    if (ts < n || n == -1) {
      n = ts;
      result = {t};
    }
    else if (ts == n) {
      result += {t};
    } 
  }
  return result;
}
  
  
set[Trail] repair(Rule rule, World w) {
  result = repair(rule, w, <<(), ()>, <(), ()>>);
  
  // ok, this works, but obviously seems extremely slow.
  // irl we would of course do it per rule, and only if a 
  // rule is affected by an update to a base relation.
  
  int i = 0;
  solve (result) {
    println("ROUND <i>");
    i += 1;
    newResult = {};
    for (Trail tr <- result) {
      newResult += repair(rule, w, tr);
    }    
    result = newResult;
  } 
  
  return result;
}  
  
set[Trail] repair(Rule rule, World w, Trail theTrail) {
  alts = {};
  K k = (Trail trail) {
    println("Getting trail: <trail>");
    alts += {trail};
  };

  K make(tuple[str, str] t, K k0) {
    return (Trail tr) {
      repair(add(t, rule.expr), w, tr, k0);
    };
  }

  k = ( k | make(t, it) | t <- eval(not(rule.expr), updateWithTrail(w, theTrail)), bprintln("Tuple in not(rule): <t>"));
  
  k(theTrail);
  
  return alts;
}

  
