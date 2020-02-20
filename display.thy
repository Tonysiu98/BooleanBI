theory display
  imports Main def
begin 
section "display proof"

subsection"display Antecedent"

lemma displayAnt : "ant_part Z (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))"
  apply simp
proof-
  have "pos_ant Z X \<Longrightarrow> \<forall>Y.\<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))" 
       and "neg_con Z Y \<Longrightarrow> \<forall>X.\<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))"
  proof(induction rule: pos_ant_neg_con.inducts)
case (1 X)
then show ?case
  using display_refl by blast
next
  case (2 Z X)
  then show ?case
    by (metis display_symm display_trans positulatesCL5 positulatesCL6)
next
case (3 Z X1 X2)
  then show ?case
    using display_trans positulatesCL1 by blast
next
  case (4 Z X2 X1)
then show ?case
  using display_symm display_trans positulatesCL2 by blast
next
  case (5 Z X1 X2)
  then show ?case 
    using display_trans positulatesCL7 by blast
next
  case (6 Z X2 X1)
  then show ?case
    using display_symm display_trans positulatesCL8 by blast
next
  case (7 Z X)
  then show ?case 
    by (meson display_symm display_trans positulatesCL5 positulatesCL6)
next
  case (8 Z X1 X2)
  then show ?case 
    using display_symm display_trans positulatesCL4 by blast
next
  case (9 Z X2 X1)
  then show ?case 
    using display_trans positulatesCL3 by blast
next
  case (10 Z X1 X2)
  then show ?case
    using display_trans positulatesCL7 positulatesCL8 by blast
next
  case (11 Z X2 X1)
  then show ?case 
    using display_trans positulatesCL8 by blast
qed
  then show "pos_ant Z X \<or> neg_con Z Y \<Longrightarrow> \<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)" 
    by blast
qed

subsection"display Consequent"
lemma displayCon : "con_part Z (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (W \<turnstile>\<^sub>C Z))" 
  apply simp
proof-
  have "pos_con Z Y \<Longrightarrow>  \<forall>X.\<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (W \<turnstile>\<^sub>C Z))" 
       and "neg_ant Z X \<Longrightarrow>  \<forall>Y.\<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (W \<turnstile>\<^sub>C Z))"
  proof(induction rule: pos_con_neg_ant.inducts)
case (1 X)
then show ?case 
  using display_refl by auto
next
case (2 Z X)
then show ?case 
  by (meson display_symm display_trans positulatesCL5 positulatesCL6)
next
  case (3 Z X1 X2)
  then show ?case 
    using display_symm display_trans positulatesCL4 by blast
next
  case (4 Z X2 X1)
  then show ?case 
    using display_trans positulatesCL3 by blast
next
  case (5 Z X1 X2)
  then show ?case
    using display_trans positulatesCL7 positulatesCL8 by blast
next
  case (6 Z X2 X1)
  then show ?case 
    using display_trans positulatesCL8 by blast
next
  case (7 Z X)
  then show ?case 
    by (metis display_symm display_trans positulatesCL5 positulatesCL6)
next
  case (8 Z X1 X2)
  then show ?case 
    using display_trans positulatesCL1 by blast
next
  case (9 Z X2 X1)
  then show ?case 
    using display_symm display_trans positulatesCL2 by blast
next
  case (10 Z X1 X2)
  then show ?case
    using display_trans positulatesCL7 by blast
next
  case (11 Z X2 X1)
  then show ?case
    using display_symm display_trans positulatesCL8 by blast
qed
  then show "neg_ant Z X \<or> pos_con Z Y \<Longrightarrow> \<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (W \<turnstile>\<^sub>C Z)"
    by blast
qed
end