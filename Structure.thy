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


datatype Consecution = Consecution Antecedent_Structure Consequent_Structure (infix "\<turnstile>\<^sub>C" 50)

text \<open>We define a new datatype called Consecution which takes a pair of Antecedent and Consecution 
Structure. Then using this definition we define the meaning of valid structure.\<close>

(* This is the initial definition of Valid. The problem with this definition is  (Consecution X Y) 
is a malformed argument *)
(*
definition Valid :: "Consecution \<Rightarrow> bool" where
"Valid (Consecution X Y) \<equiv> \<psi> X  \<turnstile>\<^sub>B \<gamma> Y"
*)

(*Then the new approach is to define two function which can output the Antecedent and Consequent 
Structures*)
primrec antC :: "Consecution \<Rightarrow> Antecedent_Structure" where
"antC (X \<turnstile>\<^sub>C Y) = X"

primrec ConC :: "Consecution \<Rightarrow> Consequent_Structure" where
"ConC (X \<turnstile>\<^sub>C Y) = Y"

(*Then the below definition can be evaluated succefully*)
definition Valid :: "Consecution \<Rightarrow> bool" where
"Valid C \<equiv> \<psi> (antC C) \<turnstile>\<^sub>B \<gamma> (ConC C)"

(*Now we try to define a symmetric relation called Display Postulates. We are using Isabelle 
predefined relation theory rel. Therefore Display_postulates is a set of relations*)
type_synonym Display_postulates = "Consecution rel"

(*Alternative we can define a type of Display_postulates which contains all pairs of DL_CL+LM  
postulates. However, we encounter an illegal operation. Please see below.*)
(*
typedef DLDP  = "{((X ;\<^sub>A Y)\<turnstile>\<^sub>CZ , X \<turnstile>\<^sub>C (\<sharp>Y ; Z ))}"
*)

(*We now declare a new type called display equivalence without actually defining the type*)
typedecl display_equivalence 

(*What we trying to do in below inductive defintion is to experiment from a postulate can we 
define a equivalence. Which we encounter the same problem as DLDP*)
(*
inductive display_equivalence :: "Consecution \<Rightarrow> Consecution \<Rightarrow> bool" (infix "\<equiv>\<^sub>D" 100)
  where
intro: "X \<equiv>\<^sub>D  X"|
postulates:"(X ;\<^sub>A Y)\<turnstile>\<^sub>C Z \<equiv>\<^sub>D (X \<turnstile>\<^sub>C (\<sharp>Y ; Z ))"|
display: "X' \<turnstile>\<^sub>C Y'\<Longrightarrow> X \<turnstile>\<^sub>C Y \<Longrightarrow> (X' \<turnstile>\<^sub>C Y)\<equiv>\<^sub>D (X \<turnstile>\<^sub>C Y)"
*)

(*We trying to define logical and structual rules for DL. However, what we encounter is the same as 
above. We have a illegal operation, where  Structure cannot be used in Consecution. i.e. if Y is an 
Antecedent Structure, we cannot use Y again in Consequent Structure due to clash of type*)

(*
inductive turnstile_DL :: "Antecedent_Structure \<Rightarrow> Consequent_Structure \<Rightarrow> bool " (infix "\<turnstile>" 100)
  where 
id : "FormulaA F \<turnstile> Formula F"|
botL : "formulaA \<bottom>\<^sub>B \<turnstile> X"|
cut_elimination: "X \<turnstile> F \<Longrightarrow> F \<turnstile> Y \<Longrightarrow> X \<turnstile> Y"

*)

text\<open>What we experiencing in above definition is clash of type. This is a huge problem for our next 
development. We need resolve the clash of type so that we can define Display Calculus rules.\<close>

end