module et_al::Expr

extend lang::std::Layout;

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
  
lexical EId
  = [A-Z][a-zA-Z0-9_]* !>> [a-zA-Z0-9_]
  ;  

lexical Id
  = ([a-z][a-zA-Z0-9_]* !>> [a-zA-Z0-9_]) \ Reserved
  ;  
  
keyword Reserved = "id" | "total";

