theory test
  imports Main def
begin


lemma "(X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C \<sharp>(\<sharp>\<^sub>A Y))"
  by (meson display_symm display_trans positulatesCL5 positulatesCL6)

lemma "(\<sharp>\<^sub>A X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D(\<sharp>\<^sub>A Y \<turnstile>\<^sub>C X)" 
  by (meson display_symm display_trans positulatesCL5 positulatesCL6)

lemma \<psi>L1: "\<And>Y. \<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P>(formulaA (\<psi> X) \<turnstile>\<^sub>C Y)" and 
    \<gamma>R2: "\<And>X. \<P>(X \<turnstile>\<^sub>C Y) \<longrightarrow> \<P>(X \<turnstile>\<^sub>C formula (\<gamma> Y))"
proof(induction X and Y)
case (formulaA x)
then show ?case sorry
next
  case AddNilA
  then show ?case sorry
next
  case (SharpA x)
  then show ?case sorry
next
  case (SemiColonA x1 x2)
  then show ?case 
  proof-
    note \<open>\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C Y)\<close>
    then have "\<P>(x1 \<turnstile>\<^sub>C \<sharp>x2 ; Y)" 
      using equiv positulatesCL1 by blast
    then have "\<P>(formulaA (\<psi> x1) \<turnstile>\<^sub>C \<sharp>x2 ; Y)"
      by (simp add: SemiColonA.IH(1))
    then have "\<P>(x2  \<turnstile>\<^sub>C \<sharp>(formulaA (\<psi> x1)) ; Y)"
      using equiv positulatesCL1 positulatesCL2 by blast
    then have "\<P>(formulaA (\<psi> x2)  \<turnstile>\<^sub>C \<sharp>(formulaA (\<psi> x1)) ; Y)" 
      using SemiColonA.IH(2) by blast
    then have "\<P>(formulaA (\<psi> x1) ;\<^sub>A formulaA (\<psi> x2)  \<turnstile>\<^sub>C  Y)"
      using equiv positulatesCL2 by blast
    then have "\<P>(formulaA ((\<psi> x1) \<and>\<^sub>B (\<psi> x2))  \<turnstile>\<^sub>C  Y)"
      using andL by blast
    thus "\<P> (formulaA (\<psi> (x1 ;\<^sub>A x2)) \<turnstile>\<^sub>C Y)" 
      by simp
  qed
  
next
  case MultNilA
  then show ?case sorry
next
  case (CommaA x1 x2)
  then show ?case sorry
next
  case (formula x)
  then show ?case sorry
next
  case AddNil
  then show ?case sorry
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


lemma \<psi>L: "\<forall>Y. \<P>(X \<turnstile>\<^sub>C Y) \<longrightarrow>  \<P>(formulaA (\<psi> X) \<turnstile>\<^sub>C Y)" and 
    \<gamma>R: "\<forall>X. \<P>(X \<turnstile>\<^sub>C Y) \<longrightarrow> \<P>(X \<turnstile>\<^sub>C formula (\<gamma> Y))"
proof(induction X and Y)
  case (SemiColonA x1 x2)
  then show ?case 
   proof -
     have 1:"\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C Z) \<longrightarrow> \<P>(x1 \<turnstile>\<^sub>C \<sharp>x2 ; Z)" 
       using equiv positulatesCL1 by blast
     have 2:"\<P>(x1 \<turnstile>\<^sub>C \<sharp>x2 ; Z) \<longrightarrow> \<P>(formulaA (\<psi> x1) \<turnstile>\<^sub>C \<sharp>x2 ; Z)" 
       using SemiColonA.IH(1) by blast
     have 3:"\<P>(formulaA (\<psi> x1) \<turnstile>\<^sub>C \<sharp>x2 ; Z) \<longrightarrow> \<P> (x2 \<turnstile>\<^sub>C \<sharp>(formulaA (\<psi> x1)) ; Z )"
       using equiv positulatesCL1 positulatesCL2 by blast
     have 4:"\<P> (x2 \<turnstile>\<^sub>C \<sharp>(formulaA (\<psi> x1)) ; Z ) \<longrightarrow> \<P> (formulaA (\<psi> x2) \<turnstile>\<^sub>C \<sharp>(formulaA (\<psi> x1)) ; Z )"
       using SemiColonA.IH(2) by blast
     have 5: "\<P> (formulaA (\<psi> x2) \<turnstile>\<^sub>C \<sharp>(formulaA (\<psi> x1)) ; Z ) \<longrightarrow> 
              \<P>(formulaA (\<psi> x1) ;\<^sub>A formulaA (\<psi> x2) \<turnstile>\<^sub>C Z)" 
       using equiv positulatesCL2 by blast
     have 6:"\<P>(formulaA (\<psi> x1) ;\<^sub>A formulaA (\<psi> x2) \<turnstile>\<^sub>C Z) \<longrightarrow> \<P> (formulaA (\<psi> x1 \<and>\<^sub>B \<psi> x2) \<turnstile>\<^sub>C Z)" 
       by (simp add: andL)
     have 7:"\<P> (formulaA (\<psi> x1 \<and>\<^sub>B \<psi> x2) \<turnstile>\<^sub>C Z) \<longrightarrow>\<P> (formulaA (\<psi> (x1 ;\<^sub>A x2)) \<turnstile>\<^sub>C Z)"
       by simp
     have "\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C Z) \<longrightarrow> \<P> (formulaA (\<psi> (x1 ;\<^sub>A x2)) \<turnstile>\<^sub>C Z)"
       using "1" "2" "3" "4" "5" "6" "7" by blast
     show ?case sorry
   qed
next
  case (CommaA X1 X2)
  then show ?case
  proof-
    have "\<forall>Y. \<P>(X1 ,\<^sub>A X2 \<turnstile>\<^sub>C Y) \<longrightarrow> \<P>(X1 \<turnstile>\<^sub>C X2 \<rightarrow>\<circ> Y)" 
      using equiv positulatesCL7 by blast
    have "\<forall>Y. \<P>(X1 \<turnstile>\<^sub>C X2 \<rightarrow>\<circ> Y) \<longrightarrow> \<P>(formulaA (\<psi> X1) \<turnstile>\<^sub>C X2 \<rightarrow>\<circ> Y)"
      using CommaA.IH(1) by blast
    then have 1: "\<forall>Y. \<P>(X1 ,\<^sub>A X2 \<turnstile>\<^sub>C Y) \<longrightarrow> \<P>(formulaA (\<psi> X1) \<turnstile>\<^sub>C X2 \<rightarrow>\<circ> Y)"
      using \<open>\<forall>Y. \<P> (X1 ,\<^sub>A X2 \<turnstile>\<^sub>C Y) \<longrightarrow> \<P> (X1 \<turnstile>\<^sub>C X2 \<rightarrow>\<circ> Y)\<close> by blast
    have " \<forall>Y. \<P>(formulaA (\<psi> X1) \<turnstile>\<^sub>C X2 \<rightarrow>\<circ> Y) \<longrightarrow> \<P>( X2 \<turnstile>\<^sub>C formulaA (\<psi> X1)  \<rightarrow>\<circ> Y)" 
      using equiv positulatesCL7 positulatesCL8 by blast
    have "\<forall>Y. \<P>( X2 \<turnstile>\<^sub>C formulaA (\<psi> X1)  \<rightarrow>\<circ> Y) \<longrightarrow> \<P>(formulaA (\<psi> X2) \<turnstile>\<^sub>C formulaA (\<psi> X1)  \<rightarrow>\<circ> Y)"
      using CommaA.IH(2) by auto
    have " \<forall>Y. \<P>(formulaA (\<psi> X2) \<turnstile>\<^sub>C formulaA (\<psi> X1)  \<rightarrow>\<circ> Y) \<longrightarrow> \<P>(formulaA (\<psi> X1) ,\<^sub>A formulaA (\<psi> X2) \<turnstile>\<^sub>C Y)" 
      using equiv positulatesCL8 by blast
    have 2: "\<forall>Y. \<P>(X1 ,\<^sub>A X2 \<turnstile>\<^sub>C Y) \<longrightarrow> \<P>(formulaA (\<psi> X1) ,\<^sub>A formulaA (\<psi> X2) \<turnstile>\<^sub>C Y)"
      using "1" CommaA.IH(2) \<open>\<forall>Y. \<P> (formulaA (\<psi> X1) \<turnstile>\<^sub>C X2 \<rightarrow>\<circ> Y) \<longrightarrow> \<P> (X2 \<turnstile>\<^sub>C formulaA (\<psi> X1) \<rightarrow>\<circ> Y)\<close>
            \<open>\<forall>Y. \<P> (formulaA (\<psi> X2) \<turnstile>\<^sub>C formulaA (\<psi> X1) \<rightarrow>\<circ> Y) \<longrightarrow> \<P> (formulaA (\<psi> X1) ,\<^sub>A formulaA (\<psi> X2) \<turnstile>\<^sub>C Y)\<close> by blast
    have "\<forall>Y. \<P>(formulaA (\<psi> X1) ,\<^sub>A formulaA (\<psi> X2) \<turnstile>\<^sub>C Y) \<longrightarrow> \<P>(formulaA ((\<psi> X1) *\<^sub>B (\<psi> X2)) \<turnstile>\<^sub>C Y)"
      using andMultL by auto
    have "\<forall>Y. \<P>(formulaA ((\<psi> X1) *\<^sub>B (\<psi> X2)) \<turnstile>\<^sub>C Y) \<longrightarrow> \<P>(formulaA (\<psi>( X1 ,\<^sub>A  X2)) \<turnstile>\<^sub>C Y)" 
      by simp
    have 3: "\<forall>Y. \<P>(formulaA (\<psi> X1) ,\<^sub>A formulaA (\<psi> X2) \<turnstile>\<^sub>C Y) \<longrightarrow> \<P>(formulaA (\<psi>( X1 ,\<^sub>A  X2)) \<turnstile>\<^sub>C Y)" 
      by (simp add: \<open>\<forall>Y. \<P> (formulaA (\<psi> X1) ,\<^sub>A formulaA (\<psi> X2) \<turnstile>\<^sub>C Y) \<longrightarrow> \<P> (formulaA (\<psi> X1 *\<^sub>B \<psi> X2) \<turnstile>\<^sub>C Y)\<close>)
    have 4: "\<forall>Y. \<P>(X1 ,\<^sub>A X2 \<turnstile>\<^sub>C Y) \<longrightarrow> \<P>(formulaA (\<psi>( X1 ,\<^sub>A  X2)) \<turnstile>\<^sub>C Y)"
      using "2" "3" by blast
    show "\<forall>Y. \<P> (X1 ,\<^sub>A X2 \<turnstile>\<^sub>C Y) \<longrightarrow> \<P> (formulaA (\<psi> (X1 ,\<^sub>A X2)) \<turnstile>\<^sub>C Y)" 
      using "4" by auto
  qed 
next
  case (SharpA x)
  then show ?case 
  proof -
{ fix cc :: Consequent_Structure
  have "\<not> \<P> (\<sharp>\<^sub>A x \<turnstile>\<^sub>C cc) \<or> \<P> (formulaA (\<psi> (\<sharp>\<^sub>A x)) \<turnstile>\<^sub>C cc)"
by (metis SharpA.IH \<psi>.simps(3) display_symm equiv notL positulatesCL5 positulatesCL6) }
then show ?thesis
  by meson
qed


end
