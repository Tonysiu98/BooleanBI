theory display
  imports Main def
begin 
section "display proof"

subsection"display Antecedent"


lemma  "pos (Inl Z) (Inl X) \<Longrightarrow> (\<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))" 
      and
       "neg (Inl Z) (Inr Y) \<Longrightarrow> (\<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))"
proof (induct rule:pos_neg.inducts ) print_cases
case (1 Z X)
  then show ?case sorry
 (* proof- 
    have "Z = X" 
      by (simp add: "1.hyps")
    then have "pos (Inl Z) (Inl X)" 
      using pos_neg.intros(1) by auto
    then have "\<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)" 
      using "1.hyps" display_refl by blast
    then show ?case using \<open>Z = X\<close> sorry
    oops 
   *)
   
next
case (2 X)
then show ?case sorry
next
  case (3 Z X)
  then show ?case sorry
next
case (4 Z X1 X2)
  then show ?case sorry
next
  case (5 Z X2 X1)
  then show ?case sorry
next
case (6 Z X1 X2)
then show ?case sorry
next
  case (7 Z X2 X1)
  then show ?case sorry
next
  case (8 Z X)
  then show ?case sorry
next
  case (9 Z X1 X2)
  then show ?case sorry
next
  case (10 Z X2 X1)
  then show ?case sorry
next
  case (11 Z X1 X2)
  then show ?case sorry
next
  case (12 Z X2 X1)
  then show ?case sorry
next
  case (13 Z X)
  then show ?case sorry
next
  case (14 Z X1 X2)
  then show ?case sorry
next
  case (15 Z X2 X1)
  then show ?case sorry
next
  case (16 Z X1 X2)
  then show ?case sorry
next
  case (17 Z X2 X1)
  then show ?case sorry
next
  case (18 Z X)
  then show ?case sorry
next
  case (19 Z X1 X2)
  then show ?case sorry
next
  case (20 Z X2 X1)
  then show ?case sorry
next
  case (21 Z X1 X2)
  then show ?case sorry
next
  case (22 Z X2 X1)
  then show ?case sorry
qed print_cases

lemma  "(pos (Inl Z) (Inl X) \<longrightarrow> (\<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))) \<and>
       (neg (Inl Z) (Inr Y) \<longrightarrow> (\<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)))"
proof(induct rule: pos_neg.induct)
  oops

lemma displayAnt : "ant_part (Inl Z) (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))"
  apply simp
sorry


subsection"display Consequent"
lemma displayCon : "con_part (Inr Z) (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (W \<turnstile>\<^sub>C Z))" 
  apply simp
  sorry



end