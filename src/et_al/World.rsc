module et_al::World

extend lang::std::Layout;
import et_al::EtAl;

start syntax World
  = Instance*;
  
syntax Instance
  = "obj" Id ":" EId Rel*
  ;
  
syntax Rel
  = Id "-\>" {Id ","}+
  ;  
  
  
keyword Reserved = "obj";

