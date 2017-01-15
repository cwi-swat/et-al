module et_al::Relations

import util::Maybe;
import List;
import Node;

data RExpr
  = union(set[RExpr] xs)
  | isect(set[RExpr] xs)
  | diff(list[RExpr] args)
  | compose(list[RExpr] args)
  | dagger(list[RExpr] args)
  | inv(RExpr arg)
  | not(RExpr arg)
  | id(str class)  
  | total(str class)
  | empty()
  | implies(RExpr lhs, RExpr rhs)
  | equals(RExpr lhs, RExpr rhs)
  | base(str name, str from, str to)
  ;
  
str pp(RExpr e) = pp(e, nothing());

str parens(RExpr current, nothing(), str txt) = txt;
str parens(RExpr current, just(RExpr parent), str txt) 
  = notNest(current, parent) ? "(<txt>)" : txt;

bool notNest(RExpr a, RExpr b) {
  rel[str, str] precedence = {<"implies", "union">, <"equals", "union">, <"union", "isect">, 
    <"isect", "compose">, <"compose", "inv">, <"compose", "not">};
  return <getName(a), getName(b)> in precedence+;
}



str pp(e:union(xs), parent) = parens(e, parent, intercalate(" ∪ ", [ pp(x, just(e)) | x <- xs ]));
str pp(e:isect(xs), parent) = parens(e, parent, intercalate(" ∩ ", [ pp(x, just(e)) | x <- xs ]));
str pp(e:compose(xs), parent) = parens(e, parent, intercalate(" ∘ ", [ pp(x, just(e)) | x <- xs ]));
str pp(e:inv(x), parent) = parens(e, parent, "~<pp(x, just(e))>");
str pp(e:not(x), parent) = parens(e, parent, "!<pp(x, just(e))>");
str pp(e:id(c), parent) = parens(e, parent, "𝕀(<c>)");
str pp(e:total(c), parent) = "𝕍(<c>)";
str pp(e:empty(), parent) = "∅";
str pp(e:implies(lhs, rhs), parent) = parens(e, parent, "<pp(lhs, just(e))> ⊢ <pp(rhs, just(e))>");
str pp(e:equals(lhs, rhs), parent) = parens(e, parent, "<pp(lhs, just(e))> = <pp(rhs, just(e))>");
str pp(e:base(n, f, t), parent) = "<n>(<f>, <t>)";

