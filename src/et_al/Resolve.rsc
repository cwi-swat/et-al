module et_al::Resolve

import et_al::EtAl;

import ParseTree;
import Message;

lexical EId = "$unknown";

alias Env = map[EId class, map[Id relation, EId target] rels];

Env relEnv(start[Entities] es) = relEnvWithMessages(es)[0];

tuple[Env, set[Message]] relEnvWithMessages(start[Entities] es) {
  Env env = ();
  set[Message] msgs = {};
  visit (es) {
    case (Entity)`class <EId c> <Decl* ds>`: {
      if (c in env) {
        msgs += {error("Duplicate class", c@\loc)};
      } 
      else {
        env[c] = ();
      }
      for (Decl d <- ds, d is relation) {
        if (d.name in env[c], env[c][d.name] == d.target) {
          msgs += {error("Redeclared relation", d.name@\loc)};
        }
        else if (d.name in env[c]) {
          msgs += {warning("Duplicate relation with different type", d.name@\loc)};
          env[c][d.name] = d.target;
        }
        else {
         env[c][d.name] = d.target;  
        }
      }
    }
  }
  return <env, msgs>;
}

alias Refs = rel[loc use, loc def, str label];

Refs resolve(start[Entities] es) = resolve(es, relEnv(es));

Refs resolve(start[Entities] es, Env env) 
  = ( {} | it + resolve(e, env) | Entity e <- es.top.entities );

Refs resolve(Entity e, Env env)
  = ( {} | it + resolve(d, e.name, env) | Decl d <- e.decls );
  
Refs resolve((Decl)`rule <Id _>: <Invariant inv>`, EId owner, Env env)
  = resolveInvariant(inv, owner, env);

Refs resolve((Decl)`<Id r>: <Type _>`, EId owner, Env env)
  = { /* todo */ };
  
Refs resolve((Decl)`<Id r>: <EId target>`, EId owner, Env env)
  = { <target@\loc, def@\loc, "<target>"> | def <- env, def == target };

Refs resolve((Decl)`<Id r>: <EId target> [<{Modifier ","}+ mods>]`, EId owner, Env env)
  = { <target@\loc, def@\loc, "<target>"> | def <- env, def == target }
  + resolveModifiers(r, owner, target, mods, env);
  
Refs resolveModifiers(Id r, EId owner, EId target, {Modifier ","}+ mods, Env env)
  = ( {} | it + resolveModifier(m, r, owner, target, env) | m <- mods );


Refs resolveModifier(m:(Modifier)`inv(<Id i>)`, Id r, EId owner, EId target, Env env)
  = { <i@\loc, def@\loc, "<i>">  | target <- env, def <- env[target], def == i }
  ;
  
default Refs resolveModifier(Modifier _, Id _, EId _, EId target, Env _) = {};

Refs resolveInvariant(i:(Invariant)`<Expr lhs> ⊢ <Expr rhs>`, EId owner, Env env)
  = resolveExpr(lhs, owner, env) + resolveExpr(rhs, owner, env);  

Refs resolveInvariant(i:(Invariant)`<Expr lhs> = <Expr rhs>`, EId owner, Env env)
  = resolveExpr(lhs, owner, env) + resolveExpr(rhs, owner, env);
  
Refs resolveExpr((Expr)`<EId c>.id`, EId owner, Env env) 
  = {<c@\loc, def@\loc, "<c>"> | def <- env, def == c };

Refs resolveExpr((Expr)`id`, EId owner, Env env) = {};

Refs resolveExpr((Expr)`<EId c>.<Id r>`, EId owner, Env env) 
  = {<c@\loc, def@\loc, "<c>"> | def <- env, def == c }
  + {<r@\loc, def@\loc, "<r>"> | c <- env, def <- env[c], def == r };
  
Refs resolveExpr((Expr)`<Id r>`, EId owner, Env env) 
  = { <r@\loc, def@\loc, "<r>"> | owner <- env, def <- env[owner], def == r };

Refs resolveExpr((Expr)`~<Expr e>`, EId owner, Env env) 
  = resolveExpr(e, owner, env);
  
Refs resolveExpr((Expr)`!<Expr e>`, EId owner, Env env) 
  = resolveExpr(e, owner, env);
  
Refs resolveExpr(e:(Expr)`<Expr x>.<Expr y>`, EId owner, Env env) 
  = resolveExpr(x, owner, env) + resolveExpr(y, range(x, owner, env), env);
  
Refs resolveExpr(e:(Expr)`<Expr x> + <Expr y>`, EId owner, Env env) 
  = resolveExpr(x, owner, env) + resolveExpr(y, owner, env);

Refs resolveExpr((Expr)`<Expr x> & <Expr y>`, EId owner, Env env) 
  = resolveExpr(x, owner, env) + resolveExpr(y, owner, env);

default Refs resolveExpr(Expr _, EId _, Env _) = {};

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

