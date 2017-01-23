module et_al::App

import et_al::Expr;
import et_al::ToDiagram;
import et_al::Eval;

import salix::App;
import salix::HTML;
import salix::Core;
import salix::Node;
import salix::lib::UML;

import Node;
import IO;
import ParseTree;
import util::Maybe;


/*

univalent: one
total: required
injective: unique
surjective: contains ("cascade")

rel on prim: univalent, total, surjective
if unique: it's a primary key.

relation to primitive = 
int = set[Prim[int]];
data Prim[&T]
  = prim(str from, &T val);
  // this makes prims local to "owner";
  // they're always "contains", but never cascade 

*/

alias Model = tuple[
  str newClass,
  int id,
  Spec spec
  //set[Object] objects, 
  //rel[Object from, str name, Object to] rels
];

data Object
  = obj(str \type, int id)
  | prim(str \type, value val)
  ;


data Spec
  = spec(list[Class] classes)
  ;
  
data Class
  = class(int id, str name, list[Rel] relations, list[Rule] rules, str newRel = "", bool editingName = false)
  ;
  
data Rel
  = relation(int id, str name, str target, set[Mod] modifiers, bool editingName = false)
  ;
  
data Rule
  = implies(Expr lhs, Expr rhs)
  | equals(Expr lhs, Expr rhs)
  ;
  
data Mod
  = surjective()
  | injective()
  | total()
  | univalent()
  | inverse(str relation)
  ;

Graph spec2graph(Spec s) = { <f, l, t> | class(_, str f, /relation(_, str l, str t, _), _) <- s.classes, t != "" };

App[Model] etAlApp()
  = app(init, view, update, |http://localhost:9900|, |project://EtAl/src/et_al|);
  
data Msg
  = addNewClass()
  | deleteClass(int class)
  | updateNewClass(str name)
  | updateClassName(int id, str newName)
  | addNewRel(int class)
  | deleteRel(int class, int rid)
  | startEditing(int class)
  | stopEditing(int class)
  | startEditing(int class, int rid)
  | stopEditing(int class, int rid)
  | updateNewRel(int class, str newRel)
  | updateRelName(int class, int relation, str newName)
  | updateRelTarget(int class, int relation, str newTarget)
  | setRelInverse(int class, int relation, str inverseRel)
  | setModifier(int class, int relation, Mod modifier, bool enabled)
  ;

Model init() = <"", 10, spec([
  class(0, "File", [
    relation(2, "parent", "Dir", {univalent()})
  ], []),
  class(1, "Dir", [
    relation(3, "contents", "File", {inverse("parent")})
  ], [])
])>;

Model update(Msg msg, Model m) {
  list[Class] updateClass(list[Class] classes, Class class)
    = [ c.id == class.id ? class : c | Class c <- classes ]; 

  list[Rel] updateRel(list[Rel] rels, Rel relation)
    = [ r.id == relation.id ? relation : r | Rel r <- rels ]; 
    
  Class findClass(int id) = [ c | Class c <- m.spec.classes, c.id == id ][0];
  Rel findRel(Class class, int id) = [ r | Rel r <- class.relations, r.id == id ][0];

  switch (msg) {
    // todo: merge these two messages into one with a bool arg.
    case startEditing(int c): 
      m.spec.classes = updateClass(m.spec.classes, findClass(c)[editingName=true]);

    case stopEditing(int c): 
      m.spec.classes = updateClass(m.spec.classes, findClass(c)[editingName=false]);

    case startEditing(int c, int rid): {
      Class class = findClass(c);
      Rel r = findRel(class, rid);
      class.relations = updateRel(class.relations, r[editingName=true]);
      m.spec.classes = updateClass(m.spec.classes, class);
    }

    case stopEditing(int c, int rid): {
      Class class = findClass(c);
      Rel r = findRel(class, rid);
      class.relations = updateRel(class.relations, r[editingName=false]);
      m.spec.classes = updateClass(m.spec.classes, class);
    }
    
    case addNewClass(): {
      m.spec.classes += [class(m.id, "newClass<m.id>", [], [])];
      m.id += 1;
      m.newClass = "";
    }
    
    case deleteClass(int id): {
      m.spec.classes = ( [] | it + (c.id == id ? [] : [c]) | Class c <- m.spec.classes );
    }
    
    case updateNewClass(str n):
      m.newClass = n;
    
    case updateClassName(int id, str n): {
      if (n != "") {
        Class class = findClass(id);
        m.spec.classes = updateClass(m.spec.classes, class[name=n]);
        m.spec.classes = visit (m.spec.classes) {
          case r:relation(_, _, str target, _) => r[target=n] when target == class.name
        }
      }  
    }
    
    case addNewRel(int id): {
      Class class = findClass(id);
      class.relations += [relation(m.id, "newRelation<m.id>", "", {})];
      m.id += 1;
      m.spec.classes = updateClass(m.spec.classes, class[newRel=""]);
    }
    
    case deleteRel(int id, int rid): {
      Class class = findClass(id);
      Rel theRel = findRel(class, rid);
      
      class.relations = ( [] | it + (r.id == rid ? [] : [r]) | Rel r <- class.relations );
      m.spec.classes = updateClass(m.spec.classes, class);
      
      // remove any inverses on this rel.
      m.spec.classes = visit (m.spec.classes) {
          case r: relation(_, _, str target, {inverse(str invName), *mods}) => r[modifiers=mods]
            when target == class.name, invName == theRel.name
        }
    }
    
    case updateRelName(int id, int old, str newName): {
      if (newName != "") {
        Class class = findClass(id);
        Rel oldRel = findRel(class, old);
        class.relations = [ r.id == old ? r[name=newName] : r | Rel r <- class.relations ];
        m.spec.classes = updateClass(m.spec.classes, class);
        m.spec.classes = visit (m.spec.classes) {
          case r: relation(_, _, str target, {inverse(str invName), *mods}) => r[modifiers=mods + {inverse(newName)}]
            when target == class.name, invName == oldRel.name
        }
      }
    }
    
    case updateRelTarget(int id, int rid, str newTarget): { 
      Class class = findClass(id);
      Rel relation = findRel(class, rid);
      set[Mod] mods = { modi | Mod modi <- relation.modifiers, inverse(_) !:= modi };
      class.relations = updateRel(class.relations, relation[target = newTarget][modifiers=mods]);
      m.spec.classes = updateClass(m.spec.classes, class);
    }

    case setRelInverse(int id, int rid, str inverseRel): {
      Class class = findClass(id);
      Rel relation = findRel(class, rid);
      relation.modifiers = { modi | modi <- relation.modifiers, inverse(_) !:= modi };
      relation.modifiers += {inverse(inverseRel)};
      class.relations = updateRel(class.relations, relation);
      m.spec.classes = updateClass(m.spec.classes, class);       
    }

    case setModifier(int id, int rid, Mod modi, bool enabled): {
      Class class = findClass(id);
      Rel relation = findRel(class, rid);
      relation.modifiers = ( relation.modifiers - {modi} | it + {modi} | enabled );
      class.relations = updateRel(class.relations, relation);
      m.spec.classes = updateClass(m.spec.classes, class);
    }
  } 
  
  return m;
}

Attr onEnter(Msg msg) 
  = event("keydown", handler("theKeyCode", encode(msg), args = ("keyCode": 13)));


void view(Model m) {
  div(() {
    div(class("row"), () {
      div(class("col-md-12"), () {
        h2("Et Al Modeling");
        button(onClick(addNewClass()), "New");
      });
    });
    div(class("row"), () {
      div(class("col-md-6"), () {
        for (Class c <- m.spec.classes) {
          viewClass(c, m);
        }
      });
      div(class("col-md-6"), () {
        //div(uml2svgNode(graph2uml(spec2graph(m.spec))));
        for (Class c <- m.spec.classes) {
          ;
        }
      });
    });
  });
}

str relKey(Rel r, Class ctx, str suffix) = "<ctx.name>_<r.name>_<suffix>";

void editable(bool editing, str text, Msg(str) msg, Msg startEditing, Msg stopEditing) {
   if (editing) {
     input(\type("text"), \value(text), onInput(msg), onEnter(stopEditing));
   }
   else {
     span(onClick(startEditing), text);
   }
}

void viewClass(Class c, Model model) {
  h3(() {
    text("Class: ");
    editable(c.editingName, c.name, partial(updateClassName, c.id), startEditing(c.id), stopEditing(c.id));
  });
  button(onClick(deleteClass(c.id)), " - ");
  //input(\type("text"), placeholder("A relation..."), \value(c.newRel), onInput(partial(updateNewRel, c.id)));
  viewRels(c, model);
  button(\type("button"), onClick(addNewRel(c.id)), " + "); 
}

void viewRels(Class class, Model model) {
  if (size(class.relations) > 0) {
    table(style(<"padding", "5px">), () {
      thead(() {
        tr(() {
          th("Relation");
          th("Target");
          th("One");
          th("Required");
          th("Unique");
          th("Contains");
          th("Inverse");
        });
      });
      tbody(() {
        for (Rel r <- class.relations) {
          tr(() {
            viewRel(r, class, model);
          });
        }
      });
    });
  }
}

Attr onEnter(Msg msg) 
  = event("keydown", handler("theKeyCode", encode(msg), args = ("keyCode": 13)));


//editable(bool editing, str text, Msg(str) msg, Msg startEditing, Msg stopEditing) {

list[str] primitives() = ["int", "str", "bool"];
bool isPrimitive(Rel r) = r.target in primitives();

void viewRel(Rel r, Class ctx, Model model) {
  td(() {
    editable(r.editingName, r.name, partial(updateRelName, ctx.id, r.id), 
      startEditing(ctx.id, r.id), stopEditing(ctx.id, r.id));
  });
  td(() {
    list[str] types = [  c.name | Class c <- model.spec.classes ] + primitives();
    dropDown(types, r.target, "Select class...", true, partial(updateRelTarget, ctx.id, r.id));
  });
  
  viewModifiers(r.modifiers, r, ctx, model);
  
  td(() {
    button(onClick(deleteRel(ctx.id, r.id)), " - ");
  });
}

void viewModifiers(set[Mod] mods, Rel r, Class ctx, Model model) {
  Attr checked(Mod m) = checked(m in mods);
  
  void checkBox(Mod m) {
    input(\type("checkbox"), onCheck(partial(setModifier, ctx.id, r.id, m)), checked(m));
  }

  td(() { checkBox(univalent()); });  
  td(() { checkBox(total()); });  
  td(() { checkBox(injective()); }); 
  td(() { checkBox(surjective()); }); 
  
  str myInverse() {
    if (inverse(str i) <- mods) {
       return i;
    }
    return "";
  }
  
  list[str] inverses = [ i.name | Class c <- model.spec.classes, c.name == r.target, Rel i <- c.relations];
  
  td(() {
    if (!isPrimitive(r)) {
      dropDown(inverses, myInverse(), "None", false, partial(setRelInverse, ctx.id, r.id));
    }
  });
}

void dropDown(list[str] options, str sel, str hint, bool hintDisabled, Msg(str) message) {
  select(onInput(message), () {
    option(\value(""), disabled(hintDisabled), selected(sel == ""), hint);
    for (str opt <- options) {
      option(\value(opt), selected(opt == sel), opt);
    }
  });
}
