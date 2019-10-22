(*  Title:      BBI.thy
    Author:     Tony Siu
*)


theory BBI
  imports Main
begin

section "BBI formula"


(* We define a variable which is indexed by natural number. In this way we can genereate inifinte atomic proposition varaiables *)
datatype atom = P nat

(* We now define a axiom which can evaluate atom to boolean *)
axiomatization evalP :: "atom \<Rightarrow> bool" 

(* With inifinte proposition variablse we can now define BBI formula. N.B. Capial M means the connective is a multiplicative connective *)
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

(* We now define a recursive evaluation to evaluate BBI formula to a boolean type*)
primrec evalF :: "BBI_form \<Rightarrow> bool" where
  "evalF Truth = True"|
  "evalF Falsity = False"|
  "evalF (Atom p) = evalP p"|
  "evalF (\<not>\<^sub>B \<phi>) = (\<not>(evalF \<phi>))"|
  "evalF (~\<^sub>B \<phi>) =  (\<not>(evalF \<phi>))" |
  "evalF (\<phi> \<and>\<^sub>B \<psi>) = ((evalF \<phi> )\<and>(evalF \<psi>))"|
  "evalF (\<phi> *\<^sub>B \<psi>) = ((evalF \<phi> )\<and>(evalF \<psi>))"|
  "evalF (\<phi> \<or>\<^sub>B \<psi>) = ((evalF \<phi> )\<or>(evalF \<psi>))"|
  "evalF (\<phi> \<or>*\<^sub>B \<psi>) = ((evalF \<phi> )\<or>(evalF \<psi>))"

definition "evaluation \<phi> \<equiv>  {\<xi>. \<xi>(evalF \<phi>)}"

(* Here we have to create a lemma to show that negation of atomic BBI formula is equal to the negation of atomic proposition*)
lemma negateAtom : 
  "evalF (Neg (Atom a)) \<Longrightarrow>  \<not>(evalP a)" 
  "evalF (Mneg (Atom a)) \<Longrightarrow>  \<not>(evalP a)"
  "evalF (Neg Truth) \<Longrightarrow>  False" 
  "evalF (Neg Falsity) \<Longrightarrow>  True" 
  "evalF (Mneg Truth) \<Longrightarrow>  False" 
  "evalF (Mneg Falsity) \<Longrightarrow> True" 
  by auto

(* Basic Axiom for both CL and LM using auto proof through induction*)
lemma Ax : "evalF f \<Longrightarrow> evalF f"
  by auto

section "Classical Logic Axioms and Rules"

lemma top: "evalF f \<Longrightarrow> True"
  by auto

lemma bot: "False \<Longrightarrow> evalF f"
  by auto


