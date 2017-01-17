module et_al::World

extend lang::std::Layout;
extend et_al::EtAl;

start syntax EtAlWorld
  = Instance*;
  
syntax Instance
  = "obj" Id ":" EId Rel*
  ;
  
syntax Rel
  = Id "-\>" {Id ","}+
  ;  
  
  
keyword Reserved = "obj";

