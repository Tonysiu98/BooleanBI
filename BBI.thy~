(*  Title:      BBI.thy
    Author:     Tony Siu
*)


theory BBI
  imports Main
begin

section "BBI formula"
(* First we declare a new type called atom which represents atomic proposition, typedecl allows Isabelle aware the existence of atom without defining it*)
typedecl atom


(* We now define a variable which have a natural number associate with it. In this way we can genereate inifinte varaiables *)
datatype var = P nat

(* Here we define a constant for proposition variable. This means atomic proposition is  var maps to a bool type. For example,P 0 is map to True; P1 is map to False and so on*)
consts atom :: "var \<Rightarrow> bool"

(* With inifinte proposition variablse we can now define BBI formula. N.B. Capial M means the connective is a multiplicative connective *)
datatype BBI_form = Atom atom
  | Neg  BBI_form  
  | Mneg BBI_form 
  | Con BBI_form BBI_form
  | MCon BBI_form BBI_form
  | Dis BBI_form BBI_form
  | Mdis BBI_form BBI_form

section "Classical Logic Axioms"




end