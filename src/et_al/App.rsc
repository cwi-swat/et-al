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

alias Model = tuple[
  str newClass,
  int id,
  Spec spec
];

data Spec
  = spec(list[Class] classes)
  ;
  
data Class
  = class(int id, str name, list[Rel] relations, list[Rule] rules, str newRel = "", bool editingName = false)
  ;
  
data Rel
  = relation(int id, str name, str target, set[Mod] modifiers)
  ;
  
data Rule
  = implies(Expr lhs, Expr rhs)
  | equals(Expr lhs, Expr rhs)
  ;
  
data Mod
  = surjective()
  | injective()
  | reflexive()
  | transitive()
  | symmetric()
  | univalent()
  | inverse(str relation)
  ;

Graph spec2graph(Spec s) = { <f, l, t> | class(_, str f, /relation(_, str l, str t, _), _) <- s.classes, t != "" };

App[Model] etAlApp()
  = app(init, view, update, |http://localhost:9900|, |project://EtAl/src/et_al|);
  
data Msg
  = addNewClass()
  | updateNewClass(str name)
  | updateClassName(int id, str newName)
  | addNewRel(int class)
  | startEditing(int class)
  | stopEditing(int class)
  | updateNewRel(int class, str newRel)
  | updateRelName(int class, int relation, str newName)
  | updateRelTarget(int class, int relation, str newTarget)
  | setRelInverse(int class, int relation, str inverseRel)
  | setModifier(int class, int relation, Mod modifier, bool enabled)
  ;

Model init() = <"", 0, spec([])>;

Model update(Msg msg, Model m) {
  list[Class] updateClass(list[Class] classes, Class class)
    = [ c.id == class.id ? class : c | Class c <- classes ]; 

  list[Rel] updateRel(list[Rel] rels, Rel relation)
    = [ r.id == relation.id ? relation : r | Rel r <- rels ]; 
    
  Class findClass(int id) = [ c | Class c <- m.spec.classes, c.id == id ][0];
  Rel findRel(Class class, int id) = [ r | Rel r <- class.relations, r.id == id ][0];

  switch (msg) {
    case startEditing(int c): 
      m.spec.classes = updateClass(m.spec.classes, findClass(c)[editingName=true]);

    case stopEditing(int c): 
      m.spec.classes = updateClass(m.spec.classes, findClass(c)[editingName=false]);
       
    case addNewClass(): {
      if (m.newClass != "", m.newClass notin { c.name | Class c <- m.spec.classes }) {
        m.spec.classes += [class(m.id, m.newClass, [], [])];
        m.id += 1;
        m.newClass = "";
      }
    }
    
    case updateNewClass(str n):
      m.newClass = n;
    
    case updateClassName(int id, str n): {
      if (n != "") {
        Class class = findClass(id);
        m.spec.classes = updateClass(m.spec.classes, class[name=n]);
        m.spec.classes = visit (m.spec.classes) {
          case r:relation(_, str target, _) => r[target=n] when target == class.name
        }
      }  
    }
    
    case addNewRel(int id): {
      Class class = findClass(id);
      if (class.newRel != "", class.newRel notin { r.name | Rel r <- class.relations }) {
        class.relations += [relation(m.id, class.newRel, "", {})];
        m.id += 1;
        m.spec.classes = updateClass(m.spec.classes, class[newRel=""]);
      }
    }
    
    case updateNewRel(int class, str n):
      m.spec.classes = updateClass(m.spec.classes, findClass(class)[newRel=n]); 
    
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
    
    case updateRelTarget(int id, int relation, str newTarget): { 
      // todo: remove inverse
      Class class = findClass(id);
      class.relations = updateRel(class.relations, findRel(class, relation)[target = newTarget]);
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
      });
    });
    div(class("row"), () {
      div(class("col-md-6"), () {
        for (Class c <- m.spec.classes) {
          viewClass(c, m);
        }
        input(\type("text"), \value(m.newClass), onInput(updateNewClass));
        button(onClick(addNewClass()), "Add");
      });
      div(class("col-md-6"), () {
        //div(uml2svgNode(graph2uml(spec2graph(m.spec))));
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

void viewClass(Class class, Model model) {
  h3(() {
    editable(class.editingName, class.name, partial(updateClassName, class.id), startEditing(class.id), stopEditing(class.id));
  }); 
  fieldset(() {
    viewRels(class, model);
    input(\type("text"), \value(class.newRel), onInput(partial(updateNewRel, class.id)));
    button(onClick(addNewRel(class.id)), "Add relation");
  });
}

void viewRels(Class class, Model model) {
  table(style(<"padding", "5px">), () {
    thead(() {
      tr(() {
        th(style(<"width", "40%">), "Relation");
        th(style(<"width", "25%">), "Target");
        th(style(<"width", "5%">), "Sur");
        th(style(<"width", "5%">), "Inj");
        th(style(<"width", "5%">), "Ref");
        th(style(<"width", "5%">), "Trans");
        th(style(<"width", "5%">), "Sym");
        th(style(<"width", "5%">), "Uni");
        th(style(<"width", "5%">), "Inverse");
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

Attr onEnter(Msg msg) 
  = event("keydown", handler("theKeyCode", encode(msg), args = ("keyCode": 13)));


void viewRel(Rel r, Class ctx, Model model) {
  td(() {
    input(\type("text"), \value(r.name), onInput(partial(updateRelName, ctx.id, r.id)));
  });
  td(() {
    dropDown([ c.name | Class c <- model.spec.classes ], r.target, "Select class...", partial(updateRelTarget, ctx.id, r.id));
  });
  
  viewModifiers(r.modifiers, r, ctx, model);
}

void viewModifiers(set[Mod] mods, Rel r, Class ctx, Model model) {
  Attr checked(Mod m) = checked(m in mods);
  
  void checkBox(Mod m) {
    input(\type("checkbox"), onCheck(partial(setModifier, ctx.id, r.id, m)), checked(m));
  }


  td(() { checkBox(surjective()); });  
  td(() { checkBox(injective()); });  
  td(() { checkBox(reflexive()); }); 
  td(() { checkBox(transitive()); });
  td(() { checkBox(symmetric()); }); 
  td(() { checkBox(univalent()); }); 
  
  str myInverse() = (inv(str r) <- mods) ? r : "";
  
  list[str] inverses = [ i.name | Class c <- model.spec.classes, c.name == r.target, Rel i <- c.relations];
  
  td(() {
    dropDown(inverses, myInverse(), "Inverse...", partial(setRelInverse, ctx.id, r.id));
  });
}

void dropDown(list[str] options, str sel, str hint, Msg(str) message) {
  select(onInput(message), () {
    option(\value(""), disabled(true), selected(true), hint);
    for (str opt <- options) {
      option(\value(opt), selected(opt == sel), opt);
    }
  });
}
