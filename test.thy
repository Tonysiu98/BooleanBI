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
"neg Z (Inr X) \<Longrightarrow> pos Z (Inl (\<sharp>\<^sub>A X))"

lemma  "(pos Z X \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>c Y) \<equiv>\<^sub>d (Z \<turnstile>\<^sub>c W)))" and "(neg Z Y \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>c Y) \<equiv>\<^sub>d (Z \<turnstile>\<^sub>c W)))"
proof (induct rule:pos_neg.inducts)
  case (1 X)
then show ?case 
  using display.refl by auto
next
  case (2 Z X)
  then show ?case
    using test.neg.simps by blast
qed 

end