module et_al::App

import et_al::Expr;
import et_al::ToDiagram;
import et_al::Eval;

import salix::App;
import salix::HTML;
import salix::Core;
import salix::lib::UML;

import Node;
import IO;
import ParseTree;
import util::Maybe;

alias Model = tuple[
  str newClass,
  Spec spec
];

data Spec
  = spec(lrel[str, Class] classes)
  ;
  
data Class
  = class(str name, lrel[str, Rel] relations, list[Rule] rules, str newRel = "")
  ;
  
data Rel
  = relation(str name, str target, set[Mod] modifiers)
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

Graph spec2graph(Spec s) = { <f, l, t> | <str f, class(_, /relation(str l, str t, _), _)> <- s.classes, t != "" };

App[Model] etAlApp()
  = app(init, view, update, |http://localhost:9900|, |project://EtAl/src/et_al|);
  
data Msg
  = addNewClass()
  | updateNewClass(str name)
  | updateClassName(Class class, str newName)
  | addNewRel(Class class)
  | updateNewRel(Class class, str newRel)
  | updateRelName(Class class, Rel relation, str newName)
  | updateRelTarget(Class class, Rel relation, str newTarget)
  | setRelInverse(Class class, Rel relation, str inverseRel)
  | setModifier(Class class, Rel relation, Mod modifier, bool enabled)
  ;

Model init() = <"", spec([])>;

Model update(Msg msg, Model m) {
  lrel[str, Class] updateClass(lrel[str, Class] classes, Class class)
    = [ <cn, cn == class.name ? class : c> | <str cn, Class c> <- classes ]; 

  lrel[str, Rel] updateRel(lrel[str, Rel] relations, Rel r)
    = [ <rn, rn == r.name ? r : r0> | <str rn, Rel r0> <- relations ]; 

  switch (msg) {
    case addNewClass(): {
      if (m.newClass != "", m.newClass notin m.spec.classes<0>) {
        m.spec.classes += [<m.newClass, class(m.newClass, [], [])>];
        m.newClass = "";
      }
    }
    
    case updateNewClass(str n):
      m.newClass = n;
    
    case updateClassName(Class class, str n): {
      m.spec.classes = [ <cn == class.name ? n : cn, cn == class.name ? class[name=n] : c> | <str cn, Class c> <- m.spec.classes ];
      m.spec.classes = visit (m.spec.classes) {
        case r:relation(_, str target, _) => r[target=n] when target == class.name
      }  
    }
    
    case addNewRel(Class class): {
      if (class.newRel notin class.relations<0>) {
        class.relations += [<class.newRel, relation(class.newRel, "", {})>];
        m.spec.classes = updateClass(m.spec.classes, class[newRel=""]);
      }
    }
    
    case updateNewRel(Class class, str n):
      m.spec.classes = updateClass(m.spec.classes, class[newRel=n]); 
    
    case updateRelName(Class class, Rel old, str newName): {
      class.relations = [ <rn == old.name ? newName : rn, rn == old.name ? old[name=newName] : r> | <str rn, Rel r> <- class.relations ];
      m.spec.classes = updateClass(m.spec.classes, class);
      m.spec.classes = visit (m.spec.classes) {
        case r: relation(_, str target, {inverse(str invName), *mods}) => r[modifiers=mods + {inverse(newName)}]
          when target == class.name, invName == old.name
      }
    }
    
    case updateRelTarget(Class class, Rel relation, str newTarget): { 
      class.relations = updateRel(class.relations, relation[target = newTarget]);
      m.spec.classes = updateClass(m.spec.classes, class);
    }

    case setRelInverse(Class class, Rel relation, str inverseRel): {
      relation.modifiers = { modi | modi <- relation.modifiers, inv(_) !:= modi };
      relation.modifiers += {inverse(inverseRel)};
      class.relations = updateRel(class.relations, relation);
      m.spec.classes = updateClass(m.spec.classes, class);       
    }

    case setModifier(Class class, Rel relation, Mod modi, bool enabled): {
      relation.modifiers = ( relation.modifiers - {modi} | it + {modi} | enabled );
      class.relations = updateRel(class.relations, relation);
      m.spec.classes = updateClass(m.spec.classes, class);
    }
  } 
  
  return m;
}

void view(Model m) {
  div(() {
    div(class("row"), () {
      div(class("col-md-12"), () {
        h2("Et Al Modeling");
      });
    });
    div(class("row"), () {
      div(class("col-md-6"), () {
        for (<_, Class c> <- m.spec.classes) {
          viewClass(c, m);
        }
        input(\type("text"), \value(m.newClass), onInput(updateNewClass));
        button(onClick(addNewClass()), "Add");
      });
      div(class("col-md-6"), () {
        div(uml2svgNode(graph2uml(spec2graph(m.spec))));
      });
    });
  });
}

str relKey(Rel r, Class ctx, str suffix) = "<ctx.name>_<r.name>_<suffix>";

void viewClass(Class class, Model model) {
  h3(class.name);
  fieldset(() {
    label(\for("<class.name>_name"), "Name");
    input(id("<class.name>_name"), \type("text"), \value(class.name), onInput(partial(updateClassName, class)));
    viewRels(class, model);
    input(\type("text"), \value(class.newRel), onInput(partial(updateNewRel, class)));
    button(onClick(addNewRel(class)), "Add relation");
  });
}

void viewRels(Class class, Model model) {
  table(style(<"padding", "5px">), () {
    thead(() {
      tr(() {
        th("Relation");
        th("Target");
        th("Sur");
        th("Inj");
        th("Ref");
        th("Trans");
        th("Sym");
        th("Uni");
        th("Inverse");
      });
    });
    for (<_, Rel r> <- class.relations) {
      tr(() {
        viewRel(r, class, model);
      });
    }
  });
}


void viewRel(Rel r, Class ctx, Model model) {
  td(() {
    input(id(relKey(r, ctx, "name")), \type("text"), \value(r.name), onInput(partial(updateRelName, ctx, r)));
  });
  td(() {
    dropDown(relKey(r, ctx, "target"), model.spec.classes<0>, r.target, "Select class...", partial(updateRelTarget, ctx, r));
  });
  
  viewModifiers(r.modifiers, r, ctx, model);
}

void viewModifiers(set[Mod] mods, Rel r, Class ctx, Model model) {
  Attr checked(Mod m) = checked(m in mods);
  
  void checkBox(Mod m) {
    input(\type("checkbox"), onCheck(partial(setModifier, ctx, r, m)), checked(m));
  }


  td(() { checkBox(surjective()); });  
  td(() { checkBox(injective()); });  
  td(() { checkBox(reflexive()); }); 
  td(() { checkBox(transitive()); });
  td(() { checkBox(symmetric()); }); 
  td(() { checkBox(univalent()); }); 
  
  str myInverse() = (inv(str r) <- mods) ? r : "";
  
  list[str] inverses = [ i | Class c <- model.spec.classes[r.target], <str i, _> <- c.relations];
  
  td(() {
    dropDown("<ctx.name>_<r.name>_inv", inverses, myInverse(), "Inverse...", partial(setRelInverse, ctx, r));
  });
}

void dropDown(str x, list[str] options, str sel, str hint, Msg(str) message) {
  select(id(x), onInput(message), () {
    option(\value(""), disabled(true), selected(true), hint);
    for (str opt <- options) {
      option(\value(opt), selected(opt == sel), opt);
    }
  });
}
