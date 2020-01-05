theory DisplayCalculusBBI
  imports Main
begin

section "BBI formula definiton"

datatype atom = P nat

datatype BBI_form = 
  Truth                     ("\<top>\<^sub>B")
  | Falsity                 ("\<bottom>\<^sub>B")
  | Mfalsity                ("\<top>\<^sup>*\<^sub>B")
  | Atom atom
  | Neg BBI_form            ("\<not>\<^sub>B _" 100)
  | Con BBI_form BBI_form   (infix "\<and>\<^sub>B" 101)
  | MCon BBI_form BBI_form  (infix "*\<^sub>B" 101)
  | Dis BBI_form BBI_form   (infix "\<or>\<^sub>B" 101)
  | Imp  BBI_form BBI_form  (infix "\<rightarrow>\<^sub>B" 101)
  | Mimp  BBI_form BBI_form (infix "\<rightarrow>\<^emph>\<^sub>B" 101)

section "BBI formula Axioms"

(* Initial attempt of turnstile, this includes both CL and LM*)
inductive turnstile_BBI :: "BBI_form \<Rightarrow> BBI_form \<Rightarrow> bool" (infix "\<turnstile>\<^sub>B" 55)
  where 
Id : "Atom atom \<turnstile>\<^sub>B Atom atom"|
Ax : "F \<turnstile>\<^sub>B F"|
Top : "F \<turnstile>\<^sub>B \<top>\<^sub>B"|
Bot : "\<bottom>\<^sub>B \<turnstile>\<^sub>B F"|
Imp : "F \<and>\<^sub>B G \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B G \<rightarrow>\<^sub>B H"|
MP : "F \<turnstile>\<^sub>B G \<Longrightarrow> G \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B H"|
Notl: "(\<not>\<^sub>B F) \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B \<bottom>\<^sub>B" |
Notr: "F \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B (\<not>\<^sub>B F)"|
Notnot : "(\<not>\<^sub>B \<not>\<^sub>B F) \<turnstile>\<^sub>B F" |
ConjI : "F \<turnstile>\<^sub>B G \<Longrightarrow> F \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B G \<and>\<^sub>B H" |
DisjE : "F \<turnstile>\<^sub>B H \<Longrightarrow> G \<turnstile>\<^sub>B H \<Longrightarrow> F \<or>\<^sub>B G \<turnstile>\<^sub>B H"|
ConjE1 : "F \<and>\<^sub>B H \<turnstile>\<^sub>B F"|
ConjE2 : "F \<and>\<^sub>B H \<turnstile>\<^sub>B H" |
DisjI1 : "F \<turnstile>\<^sub>B F \<and>\<^sub>B H" |
DisjI2 : "H \<turnstile>\<^sub>B F \<and>\<^sub>B H"|
Topl : "(F *\<^sub>B \<top>\<^sup>*\<^sub>B) \<turnstile>\<^sub>B F"|
Topr : "F \<turnstile>\<^sub>B (F *\<^sub>B \<top>\<^sup>*\<^sub>B)"|
Impstar : "F *\<^sub>B G \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B (G \<rightarrow>\<^emph>\<^sub>B H)"|
Assocl: "F *\<^sub>B (G *\<^sub>B H) \<turnstile>\<^sub>B (F *\<^sub>B G) *\<^sub>B H"|
Assocr: "(F *\<^sub>B G) *\<^sub>B H \<turnstile>\<^sub>B F *\<^sub>B (G *\<^sub>B H)"|
Comm : "(F *\<^sub>B G) \<turnstile>\<^sub>B (G *\<^sub>B F)"|
ConjIstar : "F1  \<turnstile>\<^sub>B G1 \<Longrightarrow> F2  \<turnstile>\<^sub>B G2 \<Longrightarrow> (F1 *\<^sub>B F2) \<turnstile>\<^sub>B (G1 *\<^sub>B G2)"

definition double_turnstile_CL :: "BBI_form \<Rightarrow> BBI_form \<Rightarrow> bool" (infix "\<stileturn>\<turnstile>\<^sub>B" 55)
  where " F \<stileturn>\<turnstile>\<^sub>B G \<equiv> (F \<turnstile>\<^sub>B G) \<and> (G \<turnstile>\<^sub>B F) "

section "Structure Definition"

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

(* using fun which is introduced in HOL, we can use pattern matching for defining valid*)
fun Valid :: "Consecution \<Rightarrow> bool" where
"Valid (Consecution X Y) =  \<psi> X  \<turnstile>\<^sub>B \<gamma> Y"

section "Display Calculus"

inductive displayEquiv :: "Consecution \<Rightarrow> Consecution \<Rightarrow> bool " (infix "\<equiv>\<^sub>D" 100) where
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

inductive Provable :: "Consecution \<Rightarrow>bool" ("\<P>") where
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
MAL_sym: "\<P> ((W ,\<^sub>A X) ,\<^sub>A Y \<turnstile>\<^sub>C Z) \<Longrightarrow> \<P> (W ,\<^sub>A (X ,\<^sub>A Y) \<turnstile>\<^sub>C Z)"|
(*Cut-elimination*)
cut: "\<P> (X \<turnstile>\<^sub>C (formula F)) \<Longrightarrow> \<P> ((formulaA F) \<turnstile>\<^sub>C Y) \<Longrightarrow>\<P> (X \<turnstile>\<^sub>C Y)"

section"Soundness and Completeness"
(*
theorem Soundness: "\<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid(X \<turnstile>\<^sub>C Y)"
proof (induction rule:Provable.induct)
case (BotL X)
then show ?case 
  by (simp add: Bot)
next
  case (BotR X)
then show ?case 
  by simp
next
  case (TopL X)
then show ?case 
  by simp
next
case (TopR X)
  then show ?case 
    by (simp add: Top)
next
  case (notL F X)
  then show ?case
    by simp
next
  case (notR X F)
  then show ?case 
    by simp
next
  case (orL F X G)
  then show ?case 
    by (simp add: DisjE)
next
  case (orR X F G)
  then show ?case 
    by simp
next
  case (andL F G X)
  then show ?case 
    by simp
next
  case (andR X F G)
  then show ?case 
    by (simp add: ConjI)
next
  case (impL X F G Y)
  then show ?case 
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  case (impR X F G)
  then show ?case 
    by (simp add: Imp)
next
  case (nilL X Y)
  then show ?case 
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  case (nilL_sym X Y)
  then show ?case 
    using ConjE1 DisjI2 MP Valid.simps by blast
next
case (nilR X Y)
  then show ?case 
    using ConjE1 DisjI2 MP Valid.simps by blast
next
  case (nilR_sym X Y)
  then show ?case 
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  case (AAL W X Y Z)
  then show ?case 
    using ConjE1 DisjI2 MP Valid.simps by blast
next
  case (AAL_sym W X Y Z)
  then show ?case 
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  case (AAR W X Y Z)
  then show ?case 
    using ConjE1 DisjI2 MP Valid.simps by blast
next
  case (AAR_sym W X Y Z)
  then show ?case 
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  case (WkL X Z Y)
  then show ?case 
    using ConjE1 DisjI2 MP Valid.simps by blast
next
  case (WkR X Z Y)
  then show ?case 
    using ConjE1 DisjI2 MP Valid.simps by blast
next
  case (CtrL X Y)
  then show ?case 
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  case (CtrR X Y)
  then show ?case 
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  case (TopMultL X)
  then show ?case 
    by simp
next
  case (andMultL F G X)
  then show ?case 
    by simp
next
  case (impMultL X F G Y)
  then show ?case 
    using ConjE1 DisjI2 MP Valid.simps by blast
next
  case TopMultR
  then show ?case 
    by (simp add: Ax)
next
  case (andMultR X F Y G)
  then show ?case 
    using ConjIstar by auto
next
  case (impMultR X F G)
  then show ?case
    by (simp add: Impstar)
next
case (nilMultL X Y)
then show ?case 
  using ConjE2 DisjI1 MP Valid.simps by blast
next
case (nilMultL_sym X Y)
then show ?case 
  using ConjE1 DisjI2 MP Valid.simps by blast
next
case (MAL W X Y Z)
then show ?case 
  using ConjE2 DisjI1 MP Valid.simps by blast
next
case (MAL_sym W X Y Z)
then show ?case
  using ConjE2 DisjI1 MP Valid.simps by blast
next
  case (cut X F Y)
  then show ?case
    using ConjE2 DisjI1 MP Valid.simps by blast
qed



section "display proof"

*)
theorem SoundTest:
  assumes "C \<equiv>\<^sub>D C'" 
  shows "Valid(C) \<Longrightarrow> Valid(C')"

proof -
  assume "C = ((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z)" and "C' = (X \<turnstile>\<^sub>C \<sharp>Y ; Z)" 
  have "Valid C"
    by (meson ConjE1 DisjI2 MP Valid.elims(3))
  then have "Valid C'" 
    by (meson ConjE2 DisjI1 MP Valid.elims(3))
  have "Valid(((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z)) \<Longrightarrow> Valid((X \<turnstile>\<^sub>C \<sharp>Y ; Z))" sledgehammer
    using \<open>C' = (X \<turnstile>\<^sub>C \<sharp> Y ; Z)\<close> \<open>Valid C'\<close> by blast
  show "Valid(C) \<Longrightarrow> Valid(C')"
  



axiomatization where
equiv : "(\<P> C' \<Longrightarrow> \<P> C) \<Longrightarrow> (C' \<equiv>\<^sub>D C)"

type_synonym Structure = "Antecedent_Structure + Consequent_Structure"

inductive pos :: "Structure \<Rightarrow> Structure \<Rightarrow> bool"
and neg :: "Structure \<Rightarrow> Structure \<Rightarrow> bool"
where
"pos X X" |
"neg Z (Inl X) \<Longrightarrow> pos Z (Inr(\<sharp>X))"|
"pos Z (Inl X1) \<Longrightarrow> pos Z (Inl (X1 ;\<^sub>A X2))"|
"pos Z (Inl X2) \<Longrightarrow> pos Z (Inl (X1 ;\<^sub>A X2))"|
"pos Z (Inl X1) \<Longrightarrow> pos Z (Inl (X1 ,\<^sub>A X2))"|
"pos Z (Inl X2) \<Longrightarrow> pos Z (Inl (X1 ,\<^sub>A X2))"|
"neg Z (Inl X1) \<Longrightarrow> pos Z (Inr (X1 \<rightarrow>\<circ> X2))"|
"pos Z (Inr X2) \<Longrightarrow> pos Z (Inr (X1 \<rightarrow>\<circ> X2))"|
(* Reverse pos and neg *)
"pos Z (Inl X) \<Longrightarrow> neg Z (Inr(\<sharp>X))"|
"neg Z (Inl X1) \<Longrightarrow> neg Z (Inl (X1 ;\<^sub>A X2))"|
"neg Z (Inl X2) \<Longrightarrow> neg Z (Inl (X1 ;\<^sub>A X2))"|
"neg Z (Inl X1) \<Longrightarrow> neg Z (Inl (X1 ,\<^sub>A X2))"|
"neg Z (Inl X2) \<Longrightarrow> neg Z (Inl (X1 ,\<^sub>A X2))"|
"pos Z (Inl X1) \<Longrightarrow> neg Z (Inr (X1 \<rightarrow>\<circ> X2))"|
"pos Z (Inr X2) \<Longrightarrow> neg Z (Inr (X1 \<rightarrow>\<circ> X2))"

fun ant_part :: "Structure \<Rightarrow> Consecution \<Rightarrow> bool" where
"ant_part Z (X \<turnstile>\<^sub>C Y) = ((pos Z (Inl X)) \<or> (neg Z (Inr Y)))"

fun con_part :: "Structure \<Rightarrow> Consecution \<Rightarrow> bool" where
"con_part Z (X \<turnstile>\<^sub>C Y) = ((neg Z (Inl X)) \<or> (pos Z (Inr Y)))"

lemma display :
  assumes "ant_part (Inl Z) (X \<turnstile>\<^sub>C Y)"
  shows "(\<exists>W. ((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)))"
proof -
  from assms have "((pos (Inl Z) (Inl X)) \<or> (neg (Inl Z) (Inr Y)))" by simp
  have "(pos (Inl Z) (Inl X)) \<Longrightarrow> (\<exists>W. ((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z  \<turnstile>\<^sub>C W)))"

  proof (cases X )
case (formulaA x1)
then show ?thesis sledgehammer
  using display_symm equiv by blast
next
case AddNilA
then show ?thesis sledgehammer
  using display_symm equiv by blast
next
case (SharpA x3)
then show ?thesis sledgehammer
  using display_symm equiv by blast
next
case (SemiColonA x41 x42)
then show ?thesis 
  using display_symm equiv by blast
next
  case MultNilA
  then show ?thesis
    using display_symm equiv by blast
next
  case (CommaA x61 x62)
  then show ?thesis
    using display_symm equiv by blast
qed
next 
  have "(neg (Inl Z) (Inr Y)) \<Longrightarrow> (\<exists>W. ((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z  \<turnstile>\<^sub>C W)))"
  proof (cases Y )
case (formula x1)
then show ?thesis sledgehammer
  using TopR equiv by blast
next
case AddNil
then show ?thesis sorry
next
case (Sharp x3)
then show ?thesis sorry
next
case (SemiColon x41 x42)
then show ?thesis sorry
next
  case (DotArrow x51 x52)
  then show ?thesis sorry
qed
  show ?thesis 
    using display_symm equiv by blast
qed
  
   
  





   
  

end