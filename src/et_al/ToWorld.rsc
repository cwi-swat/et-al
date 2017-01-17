module et_al::ToWorld

import et_al::World;
import et_al::Eval;
import et_al::Relations;

World toWorld(start[EtAlWorld] src) {
  Univ u = univ(src);
  State s = state(src, u);
  return <u, s>;
}

Univ univ(start[EtAlWorld] src)
  = { <"<class>", "<atom>"> | /(Instance)`obj <Id atom>: <EId class> <Rel* _>` := src };
  
alias State = map[RExpr base, rel[str,str] rels];

State state(start[EtAlWorld] src, Univ univ) {
  State state = ();
  for (/(Instance)`obj <Id atom>: <EId class> <Rel* rels>` := src) {
    for (Rel r <- rels) {
      <key, ts> = tuplesFor(r, atom, class, univ);
      if (key notin state) {
        state[key] = {};
      }
      state[key] += ts;
    }
  }
  return state;
}
  
str target({Id ","}+ atoms, Univ univ) = to
  when Id a <- atoms, <str to, "<a>"> <- univ;  
  
tuple[RExpr, rel[str,str]] tuplesFor((Rel)`<Id r> -\> <{Id ","}+ atoms>`, Id from, EId class, Univ univ)
  = <base("<r>", "<class>", target(atoms, univ)), { <"<from>", "<a>"> | a <- atoms } >; 