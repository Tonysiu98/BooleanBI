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

section "Display Calculus"

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

text \<open> We then define logical and Structural rules for our display calculus. We use the symbol \<P>
to show that the consecution is provable. 
Again we use an inductive definition for proving our future theorem\<close>

inductive rules :: "Consecution \<Rightarrow>bool" ("\<P>") where
(*Logical Rules For DL_CL*)
BotL: "\<P> ((formulaA \<bottom>\<^sub>B) \<turnstile>\<^sub>C X)"|
BotR: "\<P> (X \<turnstile>\<^sub>C \<emptyset>) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C formula \<bottom>\<^sub>B)"|
TopL: "\<P> (\<emptyset>\<^sub>A \<turnstile>\<^sub>C X) \<Longrightarrow> \<P> (formulaA \<top>\<^sub>B \<turnstile>\<^sub>C X) "|
TopR: "\<P> (X \<turnstile>\<^sub>C (formula \<top>\<^sub>B))"|
notL: "\<P> ((\<sharp>\<^sub>A(formula F)) \<turnstile>\<^sub>C X) \<Longrightarrow> \<P> (formulaA (\<not>\<^sub>B F) \<turnstile>\<^sub>C X)"|
notR: "\<P> (X \<turnstile>\<^sub>C (\<sharp>(formulaA F))) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C formula (\<not>\<^sub>B F)) "|
orL : "\<P> (formulaA F \<turnstile>\<^sub>C X) \<Longrightarrow> \<P> (formulaA G \<turnstile>\<^sub>C X) \<Longrightarrow> \<P> (formulaA (F \<or>\<^sub>B G) \<turnstile>\<^sub>C X)"|
orR : "\<P> (X \<turnstile>\<^sub>C formula F;formula G) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C formula (F \<or>\<^sub>B G))"|
andL: "\<P> (formulaA F ;\<^sub>A formulaA G \<turnstile>\<^sub>C X) \<Longrightarrow> \<P> (formulaA (F \<and>\<^sub>B G) \<turnstile>\<^sub>C X)"|
andR: "\<P> (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C formula G) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C formula (F \<and>\<^sub>B G))"|
impL: "\<P> (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> \<P> (formulaA G \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (formulaA (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>C (\<sharp>X;Y))"|
impR: "\<P> (X ;\<^sub>A formulaA F \<turnstile>\<^sub>C formula G) \<Longrightarrow>\<P> (X \<turnstile>\<^sub>C formula (F \<rightarrow>\<^sub>B G))"|
(* Structural Rules For DL_CL*)
nilL : "\<P> (\<emptyset>\<^sub>A ;\<^sub>A X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C Y)"|
nilL_sym: "\<P> (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (\<emptyset>\<^sub>A ;\<^sub>A X \<turnstile>\<^sub>C Y)"|
nilR : "\<P> (X \<turnstile>\<^sub>C Y ; \<emptyset>) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C Y)"|
nilR_sym: "\<P> (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C Y ; \<emptyset>)"|
AAL : "\<P> (W ;\<^sub>A (X ;\<^sub>A Y) \<turnstile>\<^sub>C Z) \<Longrightarrow> \<P> ((W ;\<^sub>A X) ;\<^sub>A Y \<turnstile>\<^sub>C Z)"|
AAL_sym: "\<P> ((W ;\<^sub>A X) ;\<^sub>A Y \<turnstile>\<^sub>C Z) \<Longrightarrow> \<P> (W ;\<^sub>A (X ;\<^sub>A Y) \<turnstile>\<^sub>C Z)"|
AAR : "\<P> (W \<turnstile>\<^sub>C (X ; Y) ; Z) \<Longrightarrow> \<P> (W \<turnstile>\<^sub>C X ; (Y ; Z))"|
AAR_sym: "\<P> (W \<turnstile>\<^sub>C X ; (Y ; Z)) \<Longrightarrow> \<P> (W \<turnstile>\<^sub>C (X ; Y) ; Z)"|
WkL: "\<P> (X \<turnstile>\<^sub>C Z) \<Longrightarrow> \<P> (X ;\<^sub>A Y \<turnstile>\<^sub>C Z)"|
WkR: "\<P> (X \<turnstile>\<^sub>C Z) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C Y ; Z)"|
CtrL: "\<P> (X ;\<^sub>A X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C Y)"|
CtrR: "\<P> (X \<turnstile>\<^sub>C Y ; Y) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C Y)"|
(*Logical Rules for DL_LM*)
TopMultL : "\<P> (\<oslash> \<turnstile>\<^sub>C X) \<Longrightarrow> \<P> (formulaA \<top>\<^sup>*\<^sub>B \<turnstile>\<^sub>C X)"|
andMultL : "\<P> ((formulaA F ,\<^sub>A formulaA G) \<turnstile>\<^sub>C X) \<Longrightarrow> \<P> (formulaA (F *\<^sub>B G) \<turnstile>\<^sub>C X)"|
impMultL: "\<P> (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> \<P> (formulaA G \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (formulaA (F \<rightarrow>\<^emph>\<^sub>B G) \<turnstile>\<^sub>C X \<rightarrow>\<circ> Y)"|
TopMultR: "\<P> (\<oslash> \<turnstile>\<^sub>C formula \<top>\<^sup>*\<^sub>B)"|
andMultR: "\<P> (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> \<P> (Y \<turnstile>\<^sub>C formula G) \<Longrightarrow> \<P> (X ,\<^sub>A Y \<turnstile>\<^sub>C formula (F *\<^sub>B G))"|
impMultR: "\<P> (X ,\<^sub>A formulaA F \<turnstile>\<^sub>C formula G) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C formula (F \<rightarrow>\<^emph>\<^sub>B G))"|
(*Structural Rules for DL_LM*)
nilMultL: "\<P> (\<oslash> ,\<^sub>A X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C Y)" |
nilMultL_sym: "\<P> (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (\<oslash> ,\<^sub>A X \<turnstile>\<^sub>C Y)"|
MAL: "\<P> (W ,\<^sub>A (X ,\<^sub>A Y) \<turnstile>\<^sub>C Z) \<Longrightarrow> \<P> ((W ,\<^sub>A X) ,\<^sub>A Y \<turnstile>\<^sub>C Z)"|
MAL_sym: "\<P> ((W ,\<^sub>A X) ,\<^sub>A Y \<turnstile>\<^sub>C Z) \<Longrightarrow> \<P> (W ,\<^sub>A (X ,\<^sub>A Y) \<turnstile>\<^sub>C Z)" 

end 