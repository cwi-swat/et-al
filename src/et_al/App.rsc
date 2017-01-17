module et_al::App

import et_al::EtAl;
import et_al::ToDiagram;
import salix::App;
import salix::HTML;
import salix::Core;
import salix::lib::UML;
import ParseTree;


alias Model = tuple[start[Entities] spec];

App[Model] etAlApp()
  = app(init, view, update, |http://localhost:9900|, |project://EtAl/src/et_al|);

Model init() = <parse(#start[Entities], |project://EtAl/src/example.ea|)>;

Model update(Msg msg, Model m) = m;

void view(Model m) {
  div(uml2svgNode(graph2uml(spec2graph(m.spec))));
}