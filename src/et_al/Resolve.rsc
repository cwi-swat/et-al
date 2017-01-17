module et_al::Resolve

import et_al::EtAl;

import ParseTree;
import Message;

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


Refs resolve(start[Entities] es) {
  env = relEnv(es);
  refs = {};
  
  // TODO: this is wrong: composition changes context
  // and inv requires decl context.
  for (/(Entity)`class <EId owner> <Decl* decls>` := es ) {
    visit (decls) {

      case (Decl)`<Id r>: <EId target>`: 
        refs += { <target@\loc, def@\loc, "<target>"> | EId def <- env, def == target };

      case (Decl)`<Id r>: <EId target> [<{Modifier ","}+ _>]`: 
        refs += { <target@\loc, def@\loc, "<target>"> | EId def <- env, def == target };

      case (Expr)`<EId class>.<Id r>`: 
        refs += { <class@\loc, def@\loc, "<class>"> | EId def <- env, def == class }
          + { <r@\loc, def@\loc, "<r>"> | class <- env, def <- env[class], def == r };
  
      case (Expr)`<EId class>.id`:
         refs += { <class@\loc, def@\loc, "<class>"> | EId def <- env, def == class };
         
      case (Expr)`<Id r>`:
         refs += { <r@\loc, def@\loc, "<r>"> | owner <- env, def <- env[owner], def == r };
         
    }
  }
  
  return refs;
  
  
}