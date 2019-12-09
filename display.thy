theory display
  imports Main Structure HOL.Sum_Type
begin

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

lemma display : "ant_part (Inl Z) (X \<turnstile>\<^sub>C Y) \<Longrightarrow>  \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))"
  apply (rule pos.cases)
  sorry
  



(* Testing purpose *)
datatype testA = Q | sharp testB ("#")
and 
testB = R | percent testA ("%")

type_synonym testAB = "testA + testB"

fun sharps:: "testAB \<Rightarrow> bool" where
"sharps (Inr R) = True"|
"sharps (Inl (#x)) = False"

inductive \<F> :: "testAB \<Rightarrow> testAB \<Rightarrow> bool" where
"\<F> x x"|
"\<F> a y \<Longrightarrow> \<F> (Inl (sharp x)) y"|
"\<F> x y \<Longrightarrow> \<F> (Inl (sharp x)) y"

end