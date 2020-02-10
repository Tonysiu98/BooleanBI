theory test
  imports Main def
begin

inductive pos :: "Structure \<Rightarrow> Structure \<Rightarrow> bool"
and neg :: "Structure \<Rightarrow> Structure \<Rightarrow> bool"
where
(*any structure is positive to itself*)
"pos X X" |
(*Antecedent part pos*)
"neg (Inl Z) (Inr X)"  if " pos (Inl Z) (Inl (\<sharp>\<^sub>A X))" for Z 


lemma "((pos (Inl Z) (Inl X) \<longrightarrow> (\<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)))) \<and> ((neg (Inl Z) (Inr Y) \<longrightarrow> (\<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))))"
proof(induction rule: pos_neg.induct)
case (1 X)
  then show ?case sorry
next
  case (2 Z X)
  then show ?case sorry
qed

end