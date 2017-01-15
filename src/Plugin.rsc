module Plugin

import ParseTree;
import util::IDE;
import et_al::EtAl;
import et_al::ToRules;
import et_al::Relations;

node outlineRules(start[Entities] pt) {
  list[Rule] rules = toRules(pt);
  
  list[EId] concepts = [ c | /(Entity)`class <EId c> <Decl* _>` := pt ];
  
  bool refersTo(Rule r, EId c) = from == "<c>" || to == "<c>"
    when /base(_, str from, str to) := r;
  
  list[node] rulesFor(EId c) 
    = [ "rule"()[@label=pp(r.expr)][@\loc=r.origin] | r <- rules, refersTo(r, c) ];

  cs = [ "class"(rulesFor(c))[@\loc=c@\loc][@label="<c>"] | c <- concepts ];
  
  return "outline"(cs);
}


void main() {
  registerLanguage("EtAl", "ea", start[Entities](str src, loc l) {
    return parse(#start[Entities], src, l);
  });
  
  registerContributions("EtAl", {
    outliner(outlineRules)
  });
}