module et_al::Resolve

import et_al::EtAl;

import ParseTree;

alias Env = map[EId class, map[Id relation, EId target] rels];

Env relEnv(start[Entities] es) {
  env = ();
  visit (es) {
    case (Entity)`class <EId c> <Decl* ds>`: 
      env[c] = ( d.name: d.target | Decl d <- ds, d is relation );
  }
  return env;
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