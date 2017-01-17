module et_al::ToDiagram

import et_al::EtAl;
import vis::Figure;
import vis::Render;

alias Graph = rel[str from, str label, str to];
alias Graph2 = rel[str from, str roleFrom, str to, str roleTo];


Graph spec2graph(start[Entities] es)  
  = ( {} | it + entity2graph(e) | Entity e <- es.top.entities );

Graph entity2graph((Entity)`class <EId class> <Decl* decls>`)
  = ( {} | it + decl2graph(decl, class) | Decl decl <- decls );

Graph decl2graph((Decl)`<Id r>: <EId target>`, EId owner)
  = { <"<owner>", "<r>", "<target>"> };
  
Graph decl2graph((Decl)`<Id r>: <EId target> [<{Modifier ","}+ mods>]`, EId owner)
  = { <"<owner>", "<r>", "<target>"> };
  
default Graph decl2graph(Decl _, EId _) = {};

/*
 nodes = [box(id("<i>"), fillColor(arbColor()), size(minX + round(arbReal() * (maxX-minX)), minY + round(arbReal() * (maxY -minY))),resizable(false)) | i <- [1 .. nNodes+1]];
   edges = [edge("<1+arbInt(nNodes)>", "<1+arbInt(nNodes)>") |  i <- [1 .. nEdges+1]];
   return graph(nodes, edges, std(gap(hg,vg)), orientation(or));
   */
   
public FProperty TO_ARROW = toArrow(triangle(7));
   
Figure graph2figure(Graph g) {
  nodes = [ box(text(class), gap(10.0, 10.0), id(class)) | str class <- g<0> + g<2> ]
        + [ ellipse(text(l), id("<f>/<l>/<t>"), gap(10.0, 10.0)) | <str f, str l, str t> <- g ]; 
  edges = [ edge(f, "<f>/<l>/<t>"), edge("<f>/<l>/<t>", t, TO_ARROW) | <str f, str l, str t> <- g ];
  return graph(nodes, edges, gap(60.0,60.0), hint("layered"), orientation(topDown()));
}   

str graph2uml(Graph g) {
  str src = "@startuml\nhide members\n";
  for (str class <- g<0> + g<2>) {
    src += "class <class>\n";
  }
  for (<str f, str l, str t> <- g) {
    src += "<f> -- <t>: <l> \>\n"; 
  }
  return src + "@enduml";
}