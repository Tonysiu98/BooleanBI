theory def
  imports Main
begin
section "BBI formula definiton"

datatype atom = P nat

datatype BBI_form = 
  Truth                     ("\<top>\<^sub>B")
  | Falsity                 ("\<bottom>\<^sub>B")
  | MTruth                  ("\<top>\<^sup>*\<^sub>B")
  | Atom atom
  | Neg BBI_form            ("\<not>\<^sub>B")
  | Con BBI_form BBI_form   (infix "\<and>\<^sub>B" 101)
  | MCon BBI_form BBI_form  (infix "*\<^sub>B" 101)
  | Dis BBI_form BBI_form   (infix "\<or>\<^sub>B" 101)
  | Imp  BBI_form BBI_form  (infix "\<rightarrow>\<^sub>B" 101)
  | Mimp  BBI_form BBI_form (infix "\<rightarrow>*\<^sub>B" 101)


section "BBI formula Axioms"

inductive turnstile_BBI :: "BBI_form \<Rightarrow> BBI_form \<Rightarrow> bool" (infix "\<turnstile>\<^sub>B" 55)
  where 
Ax : "F \<turnstile>\<^sub>B F"|
Top : "F \<turnstile>\<^sub>B \<top>\<^sub>B"|
Bot : "\<bottom>\<^sub>B \<turnstile>\<^sub>B F"|
ImpT : "F \<and>\<^sub>B G \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B G \<rightarrow>\<^sub>B H"|
ImpB : "F \<turnstile>\<^sub>B G \<rightarrow>\<^sub>B H \<Longrightarrow> F \<and>\<^sub>B G \<turnstile>\<^sub>B H"|
MP : "F \<turnstile>\<^sub>B G \<Longrightarrow> G \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B H"|
Notl: "(\<not>\<^sub>B F) \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B \<bottom>\<^sub>B" |
Notr: "F \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B (\<not>\<^sub>B F)"|
Notnot : "(\<not>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B F" |
ConjI : "F \<turnstile>\<^sub>B G \<Longrightarrow> F \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B G \<and>\<^sub>B H" |
DisjE : "F \<turnstile>\<^sub>B H \<Longrightarrow> G \<turnstile>\<^sub>B H \<Longrightarrow> F \<or>\<^sub>B G \<turnstile>\<^sub>B H"|
ConjE1 : "G1 \<and>\<^sub>B G2 \<turnstile>\<^sub>B G1"|
ConjE2 : "G1 \<and>\<^sub>B G2 \<turnstile>\<^sub>B G2" |
DisjI1 : "G1 \<turnstile>\<^sub>B G1 \<or>\<^sub>B G2" |
DisjI2 : "G2 \<turnstile>\<^sub>B G1 \<or>\<^sub>B G2"|
Topl : "(F *\<^sub>B \<top>\<^sup>*\<^sub>B) \<turnstile>\<^sub>B F"|
Topr : "F \<turnstile>\<^sub>B (F *\<^sub>B \<top>\<^sup>*\<^sub>B)"|
ImpstarT : "F *\<^sub>B G \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B (G \<rightarrow>*\<^sub>B H)"|
ImpstarB : "F \<turnstile>\<^sub>B (G \<rightarrow>*\<^sub>B H) \<Longrightarrow> F *\<^sub>B G \<turnstile>\<^sub>B H"|
Assocl: "F *\<^sub>B (G *\<^sub>B H) \<turnstile>\<^sub>B (F *\<^sub>B G) *\<^sub>B H"|
Assocr: "(F *\<^sub>B G) *\<^sub>B H \<turnstile>\<^sub>B F *\<^sub>B (G *\<^sub>B H)"|
Comm : "(F *\<^sub>B G) \<turnstile>\<^sub>B (G *\<^sub>B F)"|
ConjIstar : "F1  \<turnstile>\<^sub>B G1 \<Longrightarrow> F2  \<turnstile>\<^sub>B G2 \<Longrightarrow> (F1 *\<^sub>B F2) \<turnstile>\<^sub>B (G1 *\<^sub>B G2)"


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
  \<Psi> :: "Antecedent_Structure \<Rightarrow> BBI_form"  and 
  \<Upsilon> :: "Consequent_Structure \<Rightarrow> BBI_form"
  where
"\<Psi> (formulaA F)  = F"|
"\<Psi> \<emptyset>\<^sub>A = \<top>\<^sub>B"|
"\<Psi> (\<sharp>\<^sub>A Y) = \<not>\<^sub>B (\<Upsilon> Y) "|
"\<Psi> (X1 ;\<^sub>A X2) = (\<Psi> X1) \<and>\<^sub>B (\<Psi> X2)"|
"\<Psi> \<oslash> = \<top>\<^sup>*\<^sub>B "|
"\<Psi> (X1 ,\<^sub>A X2) = (\<Psi> X1) *\<^sub>B (\<Psi> X2) "|
"\<Upsilon> (formula F) = F"|
"\<Upsilon> \<emptyset> = \<bottom>\<^sub>B "|
"\<Upsilon> (\<sharp> X) =  \<not>\<^sub>B (\<Psi> X)"|
"\<Upsilon> (Y1 ; Y2) = \<Upsilon> Y1 \<or>\<^sub>B \<Upsilon> Y2"|
"\<Upsilon> (X \<rightarrow>\<circ> Y) = \<Psi> X \<rightarrow>*\<^sub>B \<Upsilon> Y"

datatype Consecution = Consecution Antecedent_Structure Consequent_Structure (infix "\<turnstile>\<^sub>C" 50)

(* using fun which is introduced in HOL, we can use pattern matching for defining valid*)
primrec Valid :: "Consecution \<Rightarrow> bool" where
"Valid (X \<turnstile>\<^sub>C Y) =  \<Psi> X  \<turnstile>\<^sub>B \<Upsilon> Y"

section "Display Calculus"

inductive displayEquiv  :: "Consecution \<Rightarrow> Consecution \<Rightarrow> bool " (infix "\<equiv>\<^sub>D" 100) where
(*(X ;\<^sub>A Y) \<turnstile>\<^sub>C Z) <>\<^sub>D (X \<turnstile>\<^sub>C \<sharp>Y ; Z) <>\<^sub>D (Y ;\<^sub>A X \<turnstile>\<^sub>C Z)*)
postulateCL1:"((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C \<sharp>Y ; Z)"|
postulateCL1S :"(X \<turnstile>\<^sub>C \<sharp>Y ; Z) \<equiv>\<^sub>D ((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z)"|
postulateCL2 :"(X \<turnstile>\<^sub>C \<sharp>Y ; Z) \<equiv>\<^sub>D (Y ;\<^sub>A X \<turnstile>\<^sub>C Z)"|
postulateCL2S :"(Y ;\<^sub>A X \<turnstile>\<^sub>C Z) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C \<sharp>Y ; Z)"|
(*(X \<turnstile>\<^sub>C Y ; Z) <>\<^sub>D (X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z) <>\<^sub>D (X \<turnstile>\<^sub>C Z ; Y)*)
postulateCL3 :"(X \<turnstile>\<^sub>C Y ; Z) \<equiv>\<^sub>D (X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z) "|
postulateCL3S :"(X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z) \<equiv>\<^sub>D  (X \<turnstile>\<^sub>C Y ; Z)"|
postulateCL4 :"(X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C Z ; Y)"|
postulateCL4S :"(X \<turnstile>\<^sub>C Z ; Y) \<equiv>\<^sub>D (X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z)"|
(*(X \<turnstile>\<^sub>C Y) <>\<^sub>D (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X) <>\<^sub>D (\<sharp>\<^sub>A\<sharp>\<^sub>AX \<turnstile>\<^sub>C Y)*)
postulateCL5 :"(X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X)"|
postulateCL5S :"(\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C Y)"|
postulateCL6 :"(\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X) \<equiv>\<^sub>D (\<sharp>\<^sub>A(\<sharp>X) \<turnstile>\<^sub>C Y)"|
postulateCL6S :"(\<sharp>\<^sub>A(\<sharp>X) \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X)"|
(*(X ,\<^sub>A Y \<turnstile>\<^sub>C Z) <>\<^sub>D (X \<turnstile>\<^sub>C Y \<comment>\<circ> Z ) <>\<^sub>D (Y ,\<^sub>A X \<turnstile>\<^sub>C Z)*)
postulateCL7 :"(X ,\<^sub>A Y \<turnstile>\<^sub>C Z) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z )"|
postulateCL7S :"(X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z ) \<equiv>\<^sub>D (X ,\<^sub>A Y \<turnstile>\<^sub>C Z)"|
postulateCL8:"(X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z) \<equiv>\<^sub>D (Y ,\<^sub>A X \<turnstile>\<^sub>C Z)"|
postulateCL8S:"(Y ,\<^sub>A X \<turnstile>\<^sub>C Z) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z)"|
(*Reflective Transistive Closure*)
display_refl :"C \<equiv>\<^sub>D C"|
display_trans :"C \<equiv>\<^sub>D C' \<Longrightarrow> C' \<equiv>\<^sub>D C'' \<Longrightarrow> C \<equiv>\<^sub>D C''"

section"Structure Axioms"

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
AAL : "\<P> ((W ;\<^sub>A (X ;\<^sub>A Y) \<turnstile>\<^sub>C Z)) \<Longrightarrow> \<P> (((W ;\<^sub>A X) ;\<^sub>A Y \<turnstile>\<^sub>C Z))"|
AAL_sym: "\<P> (((W ;\<^sub>A X) ;\<^sub>A Y \<turnstile>\<^sub>C Z)) \<Longrightarrow> \<P> ((W ;\<^sub>A (X ;\<^sub>A Y) \<turnstile>\<^sub>C Z))"|
AAR : "\<P> ((W \<turnstile>\<^sub>C (X ; Y) ; Z)) \<Longrightarrow> \<P> ((W \<turnstile>\<^sub>C X ; (Y ; Z)))"|
AAR_sym: "\<P> ((W \<turnstile>\<^sub>C X ; (Y ; Z))) \<Longrightarrow> \<P> ((W \<turnstile>\<^sub>C (X ; Y) ; Z))"|
WkL: "\<P> (X \<turnstile>\<^sub>C Z) \<Longrightarrow> \<P> (X ;\<^sub>A Y \<turnstile>\<^sub>C Z)"|
WkR: "\<P> (X \<turnstile>\<^sub>C Z) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C Y ; Z)"|
CtrL: "\<P> (X ;\<^sub>A X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C Y)"|
CtrR: "\<P> (X \<turnstile>\<^sub>C Y ; Y) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C Y)"|
(*Logical Rules for DL_LM*)
TopMultL : "\<P> (\<oslash> \<turnstile>\<^sub>C X) \<Longrightarrow> \<P> (formulaA \<top>\<^sup>*\<^sub>B \<turnstile>\<^sub>C X)"|
andMultL : "\<P> ((formulaA F ,\<^sub>A formulaA G) \<turnstile>\<^sub>C X) \<Longrightarrow> \<P> (formulaA (F *\<^sub>B G) \<turnstile>\<^sub>C X)"|
impMultL: "\<P> (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> \<P> (formulaA G \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (formulaA (F \<rightarrow>*\<^sub>B G) \<turnstile>\<^sub>C X \<rightarrow>\<circ> Y)"|
TopMultR: "\<P> (\<oslash> \<turnstile>\<^sub>C formula \<top>\<^sup>*\<^sub>B)"|
andMultR: "\<P> (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> \<P> (Y \<turnstile>\<^sub>C formula G) \<Longrightarrow> \<P> (X ,\<^sub>A Y \<turnstile>\<^sub>C formula (F *\<^sub>B G))"|
impMultR: "\<P> (X ,\<^sub>A formulaA F \<turnstile>\<^sub>C formula G) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C formula (F \<rightarrow>*\<^sub>B G))"|
(*Structural Rules for DL_LM*)
nilMultL: "\<P> (\<oslash> ,\<^sub>A X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C Y)" |
nilMultL_sym: "\<P> (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (\<oslash> ,\<^sub>A X \<turnstile>\<^sub>C Y)"|
MAL: "\<P> (W ,\<^sub>A (X ,\<^sub>A Y) \<turnstile>\<^sub>C Z) \<Longrightarrow> \<P> ((W ,\<^sub>A X) ,\<^sub>A Y \<turnstile>\<^sub>C Z)"|
MAL_sym: "\<P> ((W ,\<^sub>A X) ,\<^sub>A Y \<turnstile>\<^sub>C Z) \<Longrightarrow> \<P> (W ,\<^sub>A (X ,\<^sub>A Y) \<turnstile>\<^sub>C Z)"|
(*Cut-elimination*)
cut: "\<P> (X \<turnstile>\<^sub>C (formula F)) \<Longrightarrow> \<P> ((formulaA F) \<turnstile>\<^sub>C Y) \<Longrightarrow>\<P> (X \<turnstile>\<^sub>C Y)"|
(*display equivalence*)
equiv: "\<P>(X' \<turnstile>\<^sub>C Y') \<Longrightarrow> \<P>(X \<turnstile>\<^sub>C Y)" if "(X' \<turnstile>\<^sub>C Y') \<equiv>\<^sub>D (X \<turnstile>\<^sub>C Y)"|
(*id*)
id: "\<P>(formulaA (Atom atom) \<turnstile>\<^sub>C formula (Atom atom))"

section"positive and negative structure"
inductive pos_ant :: "Antecedent_Structure \<Rightarrow> Antecedent_Structure \<Rightarrow> bool" and    
          neg_con :: "Antecedent_Structure \<Rightarrow> Consequent_Structure \<Rightarrow> bool" where
(*pos part*)
"pos_ant X X"|
"neg_con Z X \<Longrightarrow> pos_ant Z (\<sharp>\<^sub>A X)"|
"pos_ant Z X1 \<Longrightarrow> pos_ant Z (X1 ;\<^sub>A X2)"|
"pos_ant Z X2 \<Longrightarrow> pos_ant Z (X1 ;\<^sub>A X2)"|
"pos_ant Z X1 \<Longrightarrow> pos_ant Z (X1 ,\<^sub>A X2)"|
"pos_ant Z X2 \<Longrightarrow> pos_ant Z (X1 ,\<^sub>A X2)"|
(*neg part*)
"pos_ant Z X  \<Longrightarrow> neg_con Z (\<sharp> X)"|
"neg_con Z X1 \<Longrightarrow> neg_con Z (X1 ; X2)"|
"neg_con Z X2 \<Longrightarrow> neg_con Z (X1 ; X2)"|
"pos_ant Z X1 \<Longrightarrow> neg_con Z (X1 \<rightarrow>\<circ> X2)"|
"neg_con Z X2 \<Longrightarrow> neg_con Z (X1 \<rightarrow>\<circ> X2)"


inductive pos_con :: "Consequent_Structure \<Rightarrow> Consequent_Structure \<Rightarrow> bool" and    
          neg_ant :: "Consequent_Structure \<Rightarrow> Antecedent_Structure \<Rightarrow> bool" where
(*pos part*)
"pos_con X X"|
"neg_ant Z X \<Longrightarrow> pos_con Z (\<sharp> X)"|
"pos_con Z X1 \<Longrightarrow> pos_con Z (X1 ; X2)"|
"pos_con Z X2 \<Longrightarrow> pos_con Z (X1 ; X2)"|
"neg_ant Z X1 \<Longrightarrow> pos_con Z (X1 \<rightarrow>\<circ> X2)"|
"pos_con Z X2 \<Longrightarrow> pos_con Z (X1 \<rightarrow>\<circ> X2)"|
(*neg part*)
"pos_con Z X \<Longrightarrow> neg_ant Z (\<sharp>\<^sub>A X)"|
"neg_ant Z X1 \<Longrightarrow> neg_ant Z (X1 ;\<^sub>A X2)"|
"neg_ant Z X2 \<Longrightarrow> neg_ant Z (X1 ;\<^sub>A X2)"|
"neg_ant Z X1 \<Longrightarrow> neg_ant Z (X1 ,\<^sub>A X2)"|
"neg_ant Z X2 \<Longrightarrow> neg_ant Z (X1 ,\<^sub>A X2)"


primrec ant_part :: "Antecedent_Structure \<Rightarrow> Consecution \<Rightarrow> bool" where
"ant_part Z (X \<turnstile>\<^sub>C Y) = ((pos_ant Z X) \<or> (neg_con Z Y))"

primrec con_part :: "Consequent_Structure \<Rightarrow> Consecution \<Rightarrow> bool" where
"con_part Z (X \<turnstile>\<^sub>C Y) = ((neg_ant Z  X) \<or> (pos_con Z Y))"



end