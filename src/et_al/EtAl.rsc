module et_al::EtAl

extend et_al::Expr; 

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




