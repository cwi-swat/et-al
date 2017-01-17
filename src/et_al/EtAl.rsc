module et_al::EtAl

extend lang::std::Layout;

start syntax Entities
  = Entity* entities
  ;
  
syntax Entity
  = "class" EId name Decl* decls
  ;

syntax Invariant
  = implies: Expr "⊢" Expr
  | equals: Expr "=" Expr
  ;

syntax Expr
  = base: EId "." Id
  | local: Id
  | empty: "{" "}"
  | total: "total"
  | id: EId "." "id"
  | localId: "id"
  | flip: "~" Expr
  | not: "!" Expr
  > right compose: Expr "." Expr
  > left isect: Expr "&" Expr
  > left union: Expr "+" Expr
  ;

syntax Decl
  = attribute: Id ":" Type
  | relation: Id name ":" EId target Modifiers?
  | rule: "rule" Id ":" Invariant
  ;

syntax Modifiers
  = "[" {Modifier ","}+ "]"
  ;
  
syntax Modifier
  = "uni"
  | "ref"
  | "inj"
  | "sur"
  | "sym"
  | "trans"
  | "inv" "(" Id ")"
  ;

syntax Inv
  = "(" Id ")"
  ;
  
syntax Type
  = "int"
  | "str"
  | "bool"
  ;

lexical EId
  = [A-Z][a-zA-Z0-9_]* !>> [a-zA-Z0-9_]
  ;  

lexical Id
  = ([a-z][a-zA-Z0-9_]* !>> [a-zA-Z0-9_]) \ Reserved
  ;  
  
keyword Reserved = "id" | "total";



