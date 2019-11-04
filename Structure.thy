(*  Title:      structure.thy
    Author:     Tony Siu
*)

theory Structure
  imports Main BBI
begin

text \<open> We imported BBI formula definition in this thy file. And now we will be defining 
Structure connectives and rules\<close>

(* Substructure occureences in a structure X are classified as either positive or negative*)
datatype sign = positive | negative

section "Structure Definition"

text \<open> We define structures in terms of Antecedent and consequent. This is done through mutual recursion
dataype definition. As BBI is CL + LM, our connectives are based on DL of CL & LM\<close>

datatype Antecedent_Structure =
formulaA BBI_form|
AddNilA       ("\<emptyset>\<^sub>A") |
SharpA Consequent_Structure    ("\<sharp>\<^sub>A _" 100)|
SemiColonA   Antecedent_Structure Antecedent_Structure (infix ";\<^sub>A" 101)|
MultNilA     ("\<oslash>")|
CommaA Antecedent_Structure Antecedent_Structure (infix ",\<^sub>A" 101)
and
Consequent_Structure = 
formula BBI_form |
AddNil       ("\<emptyset>")|
Sharp Antecedent_Structure  ("\<sharp> _" 100)|
SemiColon Consequent_Structure Consequent_Structure (infix ";" 101)|
DotArrow Antecedent_Structure Consequent_Structure  (infix "\<comment>\<circ>" 101)

text \<open> With basic definition of Antecedent Structure and Consequent Structure, we now define 
formula meaning in Structures. If we using the same datatype pattern for Antecedent and Consequent,
there will be a clash of type in Isabelle\<close>

primrec 
  \<psi> :: "Antecedent_Structure \<Rightarrow> BBI_form"  and 
  \<gamma> :: "Consequent_Structure \<Rightarrow> BBI_form"
  where
"\<psi> (formulaA F)  = F"|
"\<psi> AddNilA = \<top>\<^sub>B"|
"\<psi> (SharpA X) =\<not>\<^sub>B \<gamma> X "|
"\<psi> (SemiColonA X Y) = (\<psi> X) \<and>\<^sub>B (\<psi> Y)"|
"\<psi> MultNilA = \<top>\<^sup>*\<^sub>B "|
"\<psi> (CommaA X Y) = (\<psi> X) *\<^sub>B (\<psi> Y) "|
"\<gamma> (formula F) = F"|
"\<gamma> AddNil = \<bottom>\<^sub>B "|
"\<gamma> (Sharp X) =  \<not>\<^sub>B \<psi> X"|
"\<gamma> (SemiColon X Y) = \<gamma> X \<or>\<^sub>B \<gamma> Y"|
"\<gamma> (DotArrow X Y) = \<psi> X \<rightarrow>\<^emph>\<^sub>B \<gamma> Y"

definition Valid :: "Antecedent_Structure \<Rightarrow> Consequent_Structure \<Rightarrow> bool" (infix "\<turnstile>" 100)
  where "X \<turnstile> Y \<equiv> \<psi> X \<turnstile>\<^sub>B \<gamma> Y "

end