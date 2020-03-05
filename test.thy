theory test
  imports Main def
begin

lemma "(X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C \<sharp>(\<sharp>\<^sub>A Y))"
  by (meson display_symm display_trans positulatesCL5 positulatesCL6)

lemma "(\<sharp>\<^sub>A X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D(\<sharp>\<^sub>A Y \<turnstile>\<^sub>C X)" 
  by (meson display_symm display_trans positulatesCL5 positulatesCL6)



lemma \<psi>L: "\<forall>Y. \<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<forall>Y.  \<P>(formulaA (\<psi> X) \<turnstile>\<^sub>C Y)"
      and \<gamma>R : " \<forall>X.  \<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<forall>X.  \<P>(X \<turnstile>\<^sub>C formula (\<gamma> Y))"

proof(induction X and Y)
case (formulaA x)
then show ?case 
  by simp
next
  case AddNilA
then show ?case 
  using TopL by auto
next
  case (SharpA x)
  then show ?case 
    sorry

next
  case (SemiColonA x1 x2)
  then show ?case
  proof-
    have "\<P>(x1 \<turnstile>\<^sub>C \<sharp>x2; Y)" 
      using SemiColonA.prems equiv positulatesCL1 by blast
    then have " \<P>(x1 \<turnstile>\<^sub>C \<sharp>x2; Y) \<Longrightarrow> \<P> (formulaA (\<psi> x1) \<turnstile>\<^sub>C  \<sharp>x2; Y)" sorry
    show ?case sorry
  qed
next
  case MultNilA
  then show ?case
    by (simp add: TopMultL)
next
  case (CommaA x1 x2)
  then show ?case sorry
next
  case (formula x)
  then show ?case 
    by auto
next
  case AddNil
  then show ?case 
    by (simp add: BotR)
next
  case (Sharp x)
  then show ?case sorry
next
  case (SemiColon x1 x2)
  then show ?case sorry
next
  case (DotArrow x1 x2)
  then show ?case sorry
qed
 


end