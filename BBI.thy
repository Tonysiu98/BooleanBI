(*  Title:      BBI.thy
    Author:     Tony Siu
*)


theory BBI
  imports Main
begin

section "BBI formula"


(* We define a variable which is indexed by natural number. In this way we can genereate inifinte atomic proposition varaiables *)
datatype atom = P nat

(* With inifinte proposition variablse we can now define BBI formula. N.B. Capial M means the connective is a multiplicative connective *)
datatype BBI_form = Atom atom
  | Neg  BBI_form  
  | Mneg BBI_form 
  | Con BBI_form BBI_form
  | MCon BBI_form BBI_form
  | Dis BBI_form BBI_form
  | Mdis BBI_form BBI_form

(* We now define a constant  which can evaluate BBI_form to Boolean type but we dont define how it is done*)
consts evalF :: "BBI_form \<Rightarrow> bool" 

(* An automatic induction proof for any BBI formula you can induct the next BBI formula *)
lemma BBI_induc: "BBI_form \<Longrightarrow> BBI_form"
proof auto
qed




end