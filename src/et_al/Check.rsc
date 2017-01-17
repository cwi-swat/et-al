module et_al::Check

import et_al::EtAl;
import et_al::Resolve;

import Message;

lexical EId = "$unknown";

set[Message] check(start[Entities] es) = check(es, relEnv(es));

set[Message] check(start[Entities] es, Env env) 
  = ( {} | it + check(e, env) | Entity e <- es.top.entities );

set[Message] check(Entity e, Env env)
  = ( {} | it + check(d, e.name, env) | Decl d <- e.decls );
  
set[Message] check((Decl)`rule <Id _>: <Invariant inv>`, EId owner, Env env)
  = checkInvariant(inv, owner, env);

set[Message] check((Decl)`<Id r>: <Type _>`, EId owner, Env env)
  = { /* todo */ };
  
set[Message] check((Decl)`<Id r>: <EId target>`, EId owner, Env env)
  = { error("Undeclared class", target@\loc) | target notin env };

set[Message] check((Decl)`<Id r>: <EId target> [<{Modifier ","}+ mods>]`, EId owner, Env env)
  = { error("Undeclared class", target@\loc) | target notin env }
  + checkModifiers(r, owner, target, mods, env);
  
set[Message] checkModifiers(Id r, EId owner, EId target, {Modifier ","}+ mods, Env env)
  = ( {} | it + checkModifier(m, r, owner, target, env) | m <- mods );

set[Message] checkModifier(m:(Modifier)`ref`, Id r, EId owner, EId target, Env env)
  = { error("Reflexive relation must have equal domain and range", m@\loc) | owner != target };   

set[Message] checkModifier(m:(Modifier)`trans`, Id r, EId owner, EId target, Env env)
  = { error("Transitive relation must have equal domain and range", m@\loc) | owner != target };   

set[Message] checkModifier(m:(Modifier)`sym`, Id r, EId owner, EId target, Env env)
  = { error("Transitive relation must have equal domain and range", m@\loc) | owner != target };   

set[Message] checkModifier(m:(Modifier)`inv(<Id i>)`, Id r, EId owner, EId target, Env env)
  = { error("Undeclared relation", i@\loc) | target <- env, i notin env[target] }
  + { error("Incompatible inverse: <env[target][i]>", i@\loc) | target <- env, i in env[target], env[target][i] != owner };
  
set[Message] checkModifier(Modifier _, Id _, EId _, EId target, Env _) = {};

set[Message] checkInvariant(i:(Invariant)`<Expr lhs> ⊢ <Expr rhs>`, EId owner, Env env)
  = { error("Incompatible types: <pp(t1)>, <pp(t2)>", i@\loc) | t1 := typeOf(lhs, owner, env), t2 := typeOf(rhs, owner, env), t1 != t2 }
  + checkExpr(lhs, owner, env) + checkExpr(rhs, owner, env);  

set[Message] checkInvariant(i:(Invariant)`<Expr lhs> = <Expr rhs>`, EId owner, Env env)
  = { error("Incompatible types", i@\loc) | typeOf(lhs, owner, env) != typeOf(rhs, owner, env) }
  + checkExpr(lhs, owner, env) + checkExpr(rhs, owner, env);  

set[Message] checkExpr((Expr)`<EId c>.id`, EId owner, Env env) = {};

set[Message] checkExpr((Expr)`id`, EId owner, Env env) = {};

set[Message] checkExpr((Expr)`<EId c>.<Id r>`, EId owner, Env env) 
  = { error("Undeclared class", c@\loc) | c notin env }
  + { error("Undeclared relation", r@\loc) | c <- env, r notin env[c] };
  
set[Message] checkExpr((Expr)`<Id r>`, EId owner, Env env) 
  = { error("Undeclared relation", r@\loc) | r notin env[owner] };

set[Message] checkExpr((Expr)`~<Expr e>`, EId owner, Env env) 
  = checkExpr(e, owner, env);
  
set[Message] checkExpr((Expr)`!<Expr e>`, EId owner, Env env) 
  = checkExpr(e, owner, env);
  
set[Message] checkExpr(e:(Expr)`<Expr x>.<Expr y>`, EId owner, Env env) 
  = { error("Incompatible range/domain: <t1>, <t2>", e@\loc) | 
       t1 := range(x, owner, env), t2 := domain(y, range(x, owner, env), env), t1 != t2 };
  
set[Message] checkExpr(e:(Expr)`<Expr x> + <Expr y>`, EId owner, Env env) 
  = { error("Incompatible types: <pp(t1)>, <pp(t2)>", e@\loc) | t1 := typeOf(x, owner, env), t2 := typeOf(y, owner, env), t1 != t2 };

set[Message] checkExpr((Expr)`<Expr x> & <Expr y>`, EId owner, Env env) 
  = { error("Incompatible types: <pp(t1)>, <pp(t2)>", e@\loc) | t1 := typeOf(x, owner, env), t2 := typeOf(y, owner, env), t1 != t2 };

str pp(tuple[EId, EId] typ) = "(<typ[0]>, <typ[1]>)";

tuple[EId, EId] typeOf(Expr arg, EId owner, Env env)
  = <domain(arg, owner, env), range(arg, owner, env)>; 

EId range((Expr)`<EId c>.id`, EId owner, Env env) = c;
EId range((Expr)`id`, EId owner, Env env) = owner;
EId range((Expr)`<EId c>.<Id r>`, EId owner, Env env)  
  = ( (EId)`$unknown` | env[c][r] | c <- env, r <- env[c] );
  
EId range((Expr)`<Id r>`, EId owner, Env env)
  = ( (EId)`$unknown` | env[owner][r] | owner <- env, r <- env[owner] );

EId range((Expr)`~<Expr e>`, EId owner, Env env) = domain(e, owner, env);
EId range((Expr)`!<Expr e>`, EId owner, Env env) = range(e, owner, env);
EId range((Expr)`<Expr x>.<Expr y>`, EId owner, Env env) = range(y, range(x, owner, env), env);
EId range((Expr)`<Expr x> + <Expr y>`, EId owner, Env env) = range(x, owner, env);
EId range((Expr)`<Expr x> & <Expr y>`, EId owner, Env env) = range(x, owner, env);

EId domain((Expr)`<EId c>.id`, EId owner, Env env) = c;
EId domain((Expr)`id`, EId owner, Env env) = owner;
EId domain((Expr)`<EId c>.<Id r>`, EId owner, Env env) = c;
EId domain((Expr)`<Id r>`, EId owner, Env env) = owner;
EId domain((Expr)`~<Expr e>`, EId owner, Env env) = range(e, owner, env);
EId domain((Expr)`!<Expr e>`, EId owner, Env env) = domain(e, owner, env);
EId domain((Expr)`<Expr x>.<Expr y>`, EId owner, Env env) = domain(x, owner, env);
EId domain((Expr)`<Expr x> + <Expr y>`, EId owner, Env env) = domain(x, owner, env);
EId domain((Expr)`<Expr x> & <Expr y>`, EId owner, Env env) = domain(x, owner, env);

