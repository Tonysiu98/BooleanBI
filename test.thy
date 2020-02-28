theory test
  imports Main def
begin

lemma "A \<Longrightarrow> B \<Longrightarrow> C"

lemma "A \<or> B \<Longrightarrow> C"
proof -
  have "A \<Longrightarrow> C" and "B \<Longrightarrow> C" sorry
  then show "A \<or> B \<Longrightarrow> C" by blast
qed

lemma \<psi>L: "\<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P>(formulaA (\<psi> X) \<turnstile>\<^sub>C Y)"
      and \<gamma>R : "\<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P>(X \<turnstile>\<^sub>C formula (\<gamma> Y))"
      and \<psi>R: "\<P>(X \<turnstile>\<^sub>C formula (\<psi> X))" 
      and \<gamma>Y : "\<P>(formulaA (\<gamma> Y) \<turnstile>\<^sub>C Y)"
proof(induction X and Y)
case (formulaA x)
then show "\<And>x. \<P> (formulaA x \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P> (formulaA (\<psi> (formulaA x)) \<turnstile>\<^sub>C Y)" 
  by simp
next
  case (SharpA x)
  then show ?thesis sorry
next
  case (SemiColonA x1 x2)
  then show ?thesis sorry
next
  case MultNilA
  then show ?thesis sorry
next
  case (CommaA x1 x2)
  then show ?thesis sorry
next
  case (formula x)
  then show ?thesis sorry
next
  case AddNil
  then show ?thesis sorry
next
  case (Sharp x)
  then show ?thesis sorry
next
  case (SemiColon x1 x2)
  then show ?thesis sorry
next
  case (DotArrow x1 x2)
  then show ?thesis sorry
qed


end