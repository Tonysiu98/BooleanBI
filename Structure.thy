(*  Title:      structure.thy
    Author:     Tony Siu
*)

theory Structure
  imports Main BBI
begin

text \<open> We imported BBI formula definition in this thy file. And now we will be defining 
Structure connectives and rules (A higher hierarchy abstract) for our display calculus\<close>

(* Substructure occureences in a structure X are classified as either positive or negative*)
datatype sign = positive | negative

section "Structure Definition"

text \<open> We define structures in terms of Antecedent and consequent. This is done through mutual 
recursion dataype definition. As BBI is CL + LM, our connectives are based on DL of CL & LM.\<close>

datatype Antecedent_Structure =
formulaA BBI_form|
AddNilA       ("\<emptyset>\<^sub>A") |
SharpA Consequent_Structure    ("\<sharp>\<^sub>A")|
SemiColonA   Antecedent_Structure Antecedent_Structure (infix ";\<^sub>A" 101)|
MultNilA     ("\<oslash>")|
CommaA Antecedent_Structure Antecedent_Structure (infix ",\<^sub>A" 101)
and
Consequent_Structure = 
formula BBI_form |
AddNil       ("\<emptyset>")|
Sharp Antecedent_Structure  ("\<sharp>")|
SemiColon Consequent_Structure Consequent_Structure (infix ";" 101)|
DotArrow Antecedent_Structure Consequent_Structure  (infix "\<rightarrow>\<circ>" 101)

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

text \<open>With above Structure definitions, we can now define Consecution which is a datatype that 
takes a pair of Antecedent and Consequent Structures in the syntax of X \<turnstile> Y\<close>

datatype Consecution = Consecution Antecedent_Structure Consequent_Structure (infix "\<turnstile>\<^sub>C" 50)

text \<open>We define the meaning of a valid Consecution is. X \<turnstile> Y is said to be valid iff  \<psi> X  \<turnstile> \<gamma> Y in logic \<L> \<close>

(* using fun which is introduced in HOL, we can use pattern matching for defining valid*)
fun Valid :: "Consecution \<Rightarrow> bool" where
"Valid (Consecution X Y) =  \<psi> X  \<turnstile>\<^sub>B \<gamma> Y"

text \<open>Now we define a display calculius of BBI. We use an inductive definition to define Displaying.
i.e. Display equivalence. Our intro rules are Display Positulates for CL + LM. We also define this 
definition to be reflexive and transistive with symmetric Display Positulates.\<close> 

inductive display :: "Consecution \<Rightarrow> Consecution \<Rightarrow> bool " (infix "\<equiv>\<^sub>D" 100) where
(*(X ;\<^sub>A Y) \<turnstile>\<^sub>C Z) <>\<^sub>D (X \<turnstile>\<^sub>C \<sharp>Y ; Z) <>\<^sub>D (Y ;\<^sub>A X \<turnstile>\<^sub>C Z)*)
positulatesCL1 [intro]:"((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C \<sharp>Y ; Z)"|
positulatesCL2 [intro]:"(X \<turnstile>\<^sub>C \<sharp>Y ; Z) \<equiv>\<^sub>D (Y ;\<^sub>A X \<turnstile>\<^sub>C Z)"|
(*(X \<turnstile>\<^sub>C Y ; Z) <>\<^sub>D (X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z) <>\<^sub>D (X \<turnstile>\<^sub>C Z ; Y)*)
positulatesCL3 [intro]:"(X \<turnstile>\<^sub>C Y ; Z) \<equiv>\<^sub>D (X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z) "|
positulatesCL4 [intro]:"(X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C Z ; Y)"|
(*(X \<turnstile>\<^sub>C Y) <>\<^sub>D (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X ) <>\<^sub>D (\<sharp>\<^sub>A\<sharp>\<^sub>AX \<turnstile>\<^sub>C Y)*)
positulatesCL5 [intro]:"(X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X )"|
positulatesCL6 [intro]:"(\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X ) \<equiv>\<^sub>D (\<sharp>\<^sub>A(\<sharp>X) \<turnstile>\<^sub>C Y)"|
(*(X ,\<^sub>A Y \<turnstile>\<^sub>C Z) <>\<^sub>D (X \<turnstile>\<^sub>C Y \<comment>\<circ> Z ) <>\<^sub>D (Y ,\<^sub>A X \<turnstile>\<^sub>C Z)*)
positulatesCL7 [intro]:"(X ,\<^sub>A Y \<turnstile>\<^sub>C Z) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z )"|
positulatesCL8 [intro]:"(X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z ) \<equiv>\<^sub>D (Y ,\<^sub>A X \<turnstile>\<^sub>C Z)"|
(*Reflective Transistive Symmetric*)
display_refl  [simp]:"C \<equiv>\<^sub>D C"|
display_symm  [simp]:"C \<equiv>\<^sub>D C' \<Longrightarrow> C' \<equiv>\<^sub>D C"|
display_trans [simp]:"C \<equiv>\<^sub>D C' \<Longrightarrow> C' \<equiv>\<^sub>D C'' \<Longrightarrow> C \<equiv>\<^sub>D C''"




end 