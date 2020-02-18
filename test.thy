theory test
  imports Main def
begin

lemma  "(pos A B \<longrightarrow> f A B) \<and> (neg C D \<longrightarrow> g C D)"
proof (induct rule:pos_neg.induct) print_cases
  oops
lemma  "(pos A (Inl B) \<longrightarrow>  f A B) \<and> (neg C D \<longrightarrow> g C D)"
proof (induct rule:pos_neg.induct) print_cases
  oops

lemma  "(pos A B \<Longrightarrow> f A B)" and " (neg C D \<Longrightarrow> g C D)"
proof (induct rule:pos_neg.inducts) print_cases
  oops

lemma "A \<or> B \<Longrightarrow> C"
proof -
  have "A \<Longrightarrow> C" and "B \<Longrightarrow> C" sorry
  then show "A \<or> B \<Longrightarrow> C" by blast
qed

section "test datatype for display"

datatype consecution = consecution Structure Structure (infixr "\<turnstile>\<^sub>c" 50)

inductive display :: "consecution \<Rightarrow> consecution \<Rightarrow> bool" (infixr "\<equiv>\<^sub>d" 60)
  where
CL1 :"(Inl(X ;\<^sub>A Y) \<turnstile>\<^sub>c (Inr Z)) \<equiv>\<^sub>d ((Inl X) \<turnstile>\<^sub>c (Inr (\<sharp>Y ; Z)))"|
refl :"C \<equiv>\<^sub>d C"|
symm :"C \<equiv>\<^sub>d C' \<Longrightarrow> C' \<equiv>\<^sub>d C"|
trans :"C \<equiv>\<^sub>d C' \<Longrightarrow> C' \<equiv>\<^sub>d C'' \<Longrightarrow> C \<equiv>\<^sub>d C''"

inductive pos :: "Structure \<Rightarrow> Structure \<Rightarrow> bool"
      and neg :: "Structure \<Rightarrow> Structure \<Rightarrow> bool"
      where
"pos X X"|
"neg Z (Inr X) \<Longrightarrow> pos Z (Inl (\<sharp>\<^sub>A X))"|
"pos Z (Inr X) \<Longrightarrow> neg Z (Inl (\<sharp>\<^sub>A X))"

lemma  "(pos Z X \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>c Y) \<equiv>\<^sub>d (Z \<turnstile>\<^sub>c W)))" and "(neg Z Y \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>c Y) \<equiv>\<^sub>d (Z \<turnstile>\<^sub>c W)))"
proof (induct rule:pos_neg.inducts)
case (1 X)
then show ?case 
  using display.refl by blast
next
  case (2 Z X)
  then show ?case sorry
next
  case (3 Z X)
  then show ?case sorry
qed


inductive pos_ant :: "Antecedent_Structure \<Rightarrow> Antecedent_Structure \<Rightarrow> bool" and    
          neg_con :: "Antecedent_Structure \<Rightarrow> Consequent_Structure \<Rightarrow> bool" where
"pos_ant X X"|
"neg_con Z Y \<Longrightarrow> pos_ant Z (\<sharp>\<^sub>A Y)"|
"pos_ant Z X1 \<Longrightarrow> pos_ant Z (X1 ;\<^sub>A X2)"|
"neg_con Z X1 \<Longrightarrow> neg_con Z (X1 ; X2)"
thm pos_ant_neg_con.induct
inductive  pos_con :: "Structure \<Rightarrow> Consequent_Structure \<Rightarrow> bool" and
neg_ant :: "Structure \<Rightarrow> Antecedent_Structure \<Rightarrow> bool" where
"pos_con (Inr Y) Y"|
"neg_ant Z X \<Longrightarrow> pos_con Z (\<sharp>X)"         

lemma  "(pos_ant Z X \<longrightarrow> (\<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)))) \<and> (neg_con C D \<longrightarrow> (\<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))))"
proof (induct rule:pos_ant_neg_con.induct)
case (1 X)
then show ?case
  using display_refl by blast
next
  case (2 Z Y)
  then show ?case sorry
next
  case (3 Z X1 X2)
  then show ?case 
  proof -
    have "\<exists>W. (X1 \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)" 
      by (simp add: "3.hyps"(2))
    have "\<exists>W. (X1 ;\<^sub>A X2 \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (X1 \<turnstile>\<^sub>C W)" 
      using positulatesCL1 by blast
    have "\<exists>W. (X1 \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (X1 \<turnstile>\<^sub>C W)" 
      using display_refl by blast
     have "\<exists>W. (X1 \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)" 
       using "3.hyps"(2) by blast
     have "pos_ant  X1 X1"
       by (simp add: pos_ant_neg_con.intros(1))
    note \<open>\<exists>W. (X1 ;\<^sub>A X2 \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (X1 \<turnstile>\<^sub>C W)\<close> \<open>\<exists>W. (X1 \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)\<close> 
    have "\<exists>W. (X1 ;\<^sub>A X2 \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)" 
      oops
      
next
  case (4 Z X1 X2)
  then show ?case sorry
qed 


end