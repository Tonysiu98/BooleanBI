(*  Title:      BBI.thy
    Author:     Tony Siu
*)

theory BBI
  imports Main
begin

section "BBI formula definiton"

text \<open>First we define a variable which is indexed by natural number. 
In this way we can genereate inifinte atomic proposition varaiables\<close>

datatype atom = P nat

text \<open>We now define a axiom which can evaluate atom to boolean without define how the function works
We are generalising the method. This method allows Isabelle to cast an atomic variable to a boolean type\<close>

axiomatization evalP :: "atom \<Rightarrow> bool" 

text \<open>With inifinte proposition variables we can now define a BBI formula datatype.
It is a recursive definition which includes symbols (both prefix and infix).
The natural number next to the symbol indicate its precedence Isabell recommended range is >= 100\<close>

datatype BBI_form = 
  Truth                     ("\<top>\<^sub>B")
  | Falsity                 ("\<bottom>\<^sub>B")
  | Atom atom
  | Neg  BBI_form           ("\<not>\<^sub>B _" 100)
  | Mneg BBI_form           ("~\<^sub>B _" 100)
  | Con BBI_form BBI_form   (infix "\<and>\<^sub>B" 101)
  | MCon BBI_form BBI_form  (infix "*\<^sub>B" 101)
  | Dis BBI_form BBI_form   (infix "\<or>\<^sub>B" 101)
  | Mdis BBI_form BBI_form  (infix "\<or>*\<^sub>B" 101)
  | Imp  BBI_form BBI_form  (infix "\<rightarrow>\<^sub>B" 101)
  | Mimp  BBI_form BBI_form  (infix "\<rightarrow>*\<^sub>B" 101)

text \<open>BBI_form is a custom mathematical object. Therefore it is difficult for Isabelle to prove any
thing on this object. Therefore, we define a primitive recursive function to evaluate the formula to 
boolean type\<close>

primrec evalF :: "BBI_form \<Rightarrow> bool" where
  "evalF Truth = True"|
  "evalF Falsity = False"|
  "evalF (Atom p) = evalP p"|
  "evalF (\<not>\<^sub>B \<phi>) = (\<not>(evalF \<phi>))"|
  "evalF (~\<^sub>B \<phi>) =  (\<not>(evalF \<phi>))" |
  "evalF (\<phi> \<and>\<^sub>B \<psi>) = ((evalF \<phi>)\<and>(evalF \<psi>))"|
  "evalF (\<phi> *\<^sub>B \<psi>) = ((evalF \<phi>)\<and>(evalF \<psi>))"|
  "evalF (\<phi> \<or>\<^sub>B \<psi>) = ((evalF \<phi>)\<or>(evalF \<psi>))"|
  "evalF (\<phi> \<or>*\<^sub>B \<psi>) = ((evalF \<phi>)\<or>(evalF \<psi>))"|
  "evalF (\<phi> \<rightarrow>\<^sub>B \<psi>) = ((evalF \<phi>)\<longrightarrow>(evalF \<psi>))"|
  "evalF (\<phi> \<rightarrow>*\<^sub>B \<psi>) = ((evalF \<phi>)\<longrightarrow>(evalF \<psi>))"


text \<open>The following evaluation is used to prove negation of atomic BBI formula can produce correct results
As all BBI formula are borken down to a list of atomic propositions. Therefore, through a induction proof \<close>

lemma negateAtom : 
  "evalF (Neg (Atom a)) \<Longrightarrow>  \<not>(evalP a)" 
  "evalF (Mneg (Atom a)) \<Longrightarrow>  \<not>(evalP a)"
  "evalF (Neg Truth) \<Longrightarrow>  False" 
  "evalF (Neg Falsity) \<Longrightarrow>  True" 
  "evalF (Mneg Truth) \<Longrightarrow>  False" 
  "evalF (Mneg Falsity) \<Longrightarrow> True" 
  by auto

(* Missing BBI_form induction proof*)

section "Axioms and Rules"
text \<open>Now we try to implement CL and LM Rules through lemmas. 
Due to our definition we can cast our BBI_form to a HOL object.
All the rules can be proved using basic HOL rules without setting up customise proof notepad
The auto prover help us to prove all LM rules.However, it does not show sub goals of proofs which is 
opposite to CL lemmas\<close>

text \<open>The following axiom rules apply to both CL and LM\<close>
lemma Ax : "evalF f \<Longrightarrow> evalF f"
  by blast

lemma MP : "\<lbrakk>evalF F \<Longrightarrow> evalF G; evalF G \<Longrightarrow> evalF H\<rbrakk> \<Longrightarrow> (evalF F \<Longrightarrow> evalF H)"
  by blast

subsection "Classical Logic Axioms and Rules"


(* IL Rules*)
lemma top: "evalF f \<Longrightarrow> True"
  by auto

lemma bot: "False \<Longrightarrow> evalF f"
  by auto

lemma disI :"\<lbrakk>evalF F; evalF G\<rbrakk> \<Longrightarrow> (evalF F \<or> evalF G)"
  by blast

lemma conI : "\<lbrakk>evalF F \<Longrightarrow> evalF G; evalF F \<Longrightarrow> evalF H\<rbrakk> \<Longrightarrow> evalF F \<Longrightarrow> evalF G \<and> evalF H" 
  by blast

lemma imp : "\<lbrakk>evalF F \<and> evalF G \<Longrightarrow> evalF H\<rbrakk> \<Longrightarrow> evalF F \<Longrightarrow> evalF G \<longrightarrow> evalF H"
  by blast

lemma conE1 : "\<lbrakk>evalF F \<and> evalF G\<rbrakk> \<Longrightarrow> evalF F"
  by blast

lemma conE2 : "\<lbrakk>evalF F \<and> evalF G\<rbrakk> \<Longrightarrow> evalF G"
  by blast

lemma disE : "\<lbrakk>evalF F \<Longrightarrow> evalF H; evalF G \<Longrightarrow> evalF H\<rbrakk> \<Longrightarrow> (evalF F \<or> evalF G \<Longrightarrow> evalF H)"
  by blast


(* CL rules*)
lemma not : "\<lbrakk>\<not>(evalF F) \<Longrightarrow> evalF F ; evalF F \<Longrightarrow> \<not>(evalF F)\<rbrakk> \<Longrightarrow> False"
  by blast

lemma notnot : "\<lbrakk>\<not>\<not>(evalF F)\<rbrakk> \<Longrightarrow> evalF F"
  by blast
  
subsection "Lambek Logic Axioms and Rules"

(* Associative rule*)
lemma assoc : "evalF (F  *\<^sub>B (G *\<^sub>B H)) \<longleftrightarrow> evalF ((F *\<^sub>B G)*\<^sub>B H)"
  by auto

lemma Mtruth : "evalF (F *\<^sub>B \<top>\<^sub>B ) \<longleftrightarrow> evalF F"
  by auto

(* Commutative rule*)
lemma comm : "evalF (F *\<^sub>B G) \<Longrightarrow> evalF(G *\<^sub>B F)"
  by auto

lemma MconI : "\<lbrakk>evalF F\<^sub>1 \<Longrightarrow> evalF G\<^sub>1 ;evalF F\<^sub>2 \<Longrightarrow> evalF G\<^sub>2\<rbrakk> \<Longrightarrow> (evalF (F\<^sub>1 *\<^sub>B F\<^sub>2) \<Longrightarrow> evalF (G\<^sub>1 *\<^sub>B G\<^sub>2))"
  by auto

lemma Mimp : "\<lbrakk>evalF (F *\<^sub>B G) \<Longrightarrow> evalF H\<rbrakk> \<Longrightarrow> (evalF F \<Longrightarrow> evalF(G \<rightarrow>*\<^sub>B H))"
  by auto


 