module Plugin

import ParseTree;
import util::IDE;
import et_al::EtAl;
import et_al::World;
import et_al::ToRules;
import et_al::Relations;
import et_al::Check;
import et_al::Resolve;
import et_al::Normalize;

anno rel[loc, loc, str] Tree@hyperlinks;

node outlineRules(start[Entities] pt) {
  list[Rule] rules = [ r[expr=normalize(r.expr)] | r <- toRules(pt) ];
  
  list[EId] concepts = [ c | /(Entity)`class <EId c> <Decl* _>` := pt ];
  
  bool refersTo(Rule r, EId c) = from == "<c>" || to == "<c>"
    when /base(_, str from, str to) := r;
  
  list[node] rulesFor(EId c) 
    = [ "rule"()[@label=pp(r.expr)][@\loc=r.origin] | r <- rules, refersTo(r, c) ];

  list[node] cs = [ "class"(rulesFor(c))[@\loc=c@\loc][@label="<c>"] | c <- concepts ];
  
  return "outline"(cs);
}


void main() {
  registerLanguage("EtAl", "ea", start[Entities](str src, loc l) {
    return parse(#start[Entities], src, l);
  });

  registerLanguage("EtAlWorld", "eaw", start[EtAlWorld](str src, loc l) {
    return parse(#start[EtAlWorld], src, l);
  });
  
  registerContributions("EtAl", {
    outliner(outlineRules),
    annotator(Tree(Tree pt) {
      if (start[Entities] es := pt) {
        <env, msgs> = relEnvWithMessages(es);
        return es[@messages=check(es, env) + msgs][@hyperlinks=resolve(es, env)];
      }
      return pt[@messages={error("Not an entities tree", pt@\loc)}];
    })
  });
}