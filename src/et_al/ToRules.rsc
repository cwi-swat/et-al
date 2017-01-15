module et_al::ToRules

import et_al::EtAl;
import et_al::Relations;

import ParseTree;
import IO;

RExpr base(Id relation, EId from, EId to) = base("<relation>", "<from>", "<to>");
RExpr id(EId c) = id("<c>");
RExpr total(EId c) = total("<c>");

data Rule
  = rule(loc origin, RExpr expr, str label = "")
  ;

alias Env = map[EId class, map[Id relation, EId target] rels];

Env relEnv(start[Entities] es) {
  env = ();
  visit (es) {
    case (Entity)`class <EId c> <Decl* ds>`: 
      env[c] = ( d.name: d.target | Decl d <- ds, d is relation );
  }
  return env;
}

list[Rule] toRules(start[Entities] entities) {
  env = relEnv(entities);
  rules = [];
  for (Entity e <- entities.top.entities) {
    rules += toRules(e, env);
  }
  return rules;
}

list[Rule] toRules((Entity)`class <EId class> <Decl* decls>`, Env env)
  = ( [] | it + toRules(d, class, env) | d <- decls );

list[Rule] toRules((Decl)`<Id attr>: <Type _>`, EId owner, Env env) = []; // todo

list[Rule] toRules((Decl)`<Id relation>: <EId target>`, EId owner, Env env) = [];

list[Rule] toRules((Decl)`<Id relation>: <EId target> [<{Modifier ","}+ mods>]`, EId owner, Env env) 
  = [ rule(m@\loc, mod2rexpr(m, relation, owner, target)) | m <- mods ];

list[Rule] toRules((Decl)`rule <Id name>: <Invariant invariant>`, EId owner, Env env)
  = [rule(name@\loc, invariant2rexpr(invariant, owner, env), label="<name>")]; 

RExpr invariant2rexpr((Invariant)`<Expr a> ⊢ <Expr c>`, EId owner, Env env)
  = implies(rexpr(a, owner, env), rexpr(c, owner, env));

RExpr invariant2rexpr((Invariant)`<Expr a> = <Expr c>`, EId owner, Env env)
  = equals(rexpr(a, owner, env), rexpr(c, owner, env));

RExpr rexpr((Expr)`<EId c>.<Id r>`, EId owner, Env env)
  = base(r, c, env[c][r]); 

RExpr rexpr((Expr)`<Id r>`, EId owner, Env env)
  = base(r, owner, env[owner][r]);
  
RExpr rexpr((Expr)`<EId c>.id`, EId owner, Env env)
  = id(c); 

RExpr rexpr((Expr)`id`, EId owner, Env env)
  = id(owner); 

RExpr rexpr((Expr)`{}`, EId owner, Env env)
  = empty(); 
 
RExpr rexpr((Expr)`<EId c>.id`, EId owner, Env env)
  = id(c); 

RExpr rexpr((Expr)`~<Expr e>`, EId owner, Env env)
  = inv(rexpr(e, owner, env)); 

RExpr rexpr((Expr)`!<Expr e>`, EId owner, Env env)
  = not(rexpr(e, owner, env)); 

RExpr rexpr((Expr)`<Expr x>.<Expr y>`, EId owner, Env env)
  = compose([rexpr(x, owner, env), rexpr(y, range(x, owner, env), env)]); 

RExpr rexpr((Expr)`<Expr x> + <Expr y>`, EId owner, Env env)
  = union({rexpr(x, owner, env), rexpr(y, owner, env)}); 

RExpr rexpr((Expr)`<Expr x> & <Expr y>`, EId owner, Env env)
  = isect({rexpr(x, owner, env), rexpr(y, owner, env)}); 

EId range((Expr)`<EId c>.id`, EId owner, Env env) = c;
EId range((Expr)`id`, EId owner, Env env) = owner;
EId range((Expr)`<EId c>.<Id r>`, EId owner, Env env) = env[c][r];
EId range((Expr)`<Id r>`, EId owner, Env env) = env[owner][r];
EId range((Expr)`~<Expr e>`, EId owner, Env env) = domain(e, owner, env);
EId range((Expr)`!<Expr e>`, EId owner, Env env) = range(e, owner, env);
EId range((Expr)`<Expr x>.<Expr y>`, EId owner, Env env) = range(y, owner, env);
EId range((Expr)`<Expr x> + <Expr y>`, EId owner, Env env) = range(x);
EId range((Expr)`<Expr x> & <Expr y>`, EId owner, Env env) = range(x);

EId domain((Expr)`<EId c>.id`, EId owner, Env env) = c;
EId domain((Expr)`id`, EId owner, Env env) = owner;
EId domain((Expr)`<EId c>.<Id r>`, EId owner, Env env) = c;
EId domain((Expr)`<Id r>`, EId owner, Env env) = owner;
EId domain((Expr)`~<Expr e>`, EId owner, Env env) = range(e, owner, env);
EId domain((Expr)`!<Expr e>`, EId owner, Env env) = domain(e, owner, env);
EId domain((Expr)`<Expr x>.<Expr y>`, EId owner, Env env) = domain(x, owner, env);
EId domain((Expr)`<Expr x> + <Expr y>`, EId owner, Env env) = domain(x);
EId domain((Expr)`<Expr x> & <Expr y>`, EId owner, Env env) = domain(x);


RExpr mod2rexpr(m:(Modifier)`inj`, Id name, EId owner, EId target)
  = implies(compose([base(name, owner, target), inv(base(name, owner, target))]), id(owner));
  
RExpr mod2rexpr(m:(Modifier)`sur`, Id name, EId owner, EId target)
  = implies(id(target), compose([inv(base(name, owner, target)), base(name, owner, target)]));
  
RExpr mod2rexpr(m:(Modifier)`ref`, Id name, EId owner, EId target)
  = implies(union({id(owner), id(target)}), base(name, owner, target));
  
RExpr mod2rexpr(m:(Modifier)`trans`, Id name, EId owner, EId target)
  = implies(compose([base(name, owner, target), base(name, owner, target)]), base(name, owner, target));
  
RExpr mod2rexpr(m:(Modifier)`uni`, Id name, EId owner, EId target)
  = implies(compose([inv(base(name, owner, target)), base(name, owner, target)]), id(target));
  
RExpr mod2rexpr(m:(Modifier)`sym`, Id name, EId owner, EId target)
  = implies(inv(base(name, owner, target)), base(name, owner, target));
  
RExpr mod2rexpr(m:(Modifier)`inv(<Id other>)`, Id name, EId owner, EId target)
  = equals(base(name, owner, target), inv(base(other, target, owner)));
  