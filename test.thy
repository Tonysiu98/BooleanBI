theory test
  imports Main def
begin


lemma "(X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (X \<turnstile>\<^sub>C \<sharp>(\<sharp>\<^sub>A Y))"
  by (meson display_symm display_trans positulatesCL5 positulatesCL6)

lemma "(\<sharp>\<^sub>A X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D(\<sharp>\<^sub>A Y \<turnstile>\<^sub>C X)" 
  by (meson display_symm display_trans positulatesCL5 positulatesCL6)



lemma \<psi>L: "\<forall>Y. \<P>(X \<turnstile>\<^sub>C Y) \<longrightarrow>  \<P>(formulaA (\<psi> X) \<turnstile>\<^sub>C Y)" and 
    \<gamma>R: "\<forall>X. \<P>(X \<turnstile>\<^sub>C Y) \<longrightarrow> \<P>(X \<turnstile>\<^sub>C formula (\<gamma> Y))"
proof(induction X and Y)
  case (SemiColonA x1 x2)
  then show ?case 
   proof -
     have "\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C Z) \<longrightarrow> \<P>(x1 \<turnstile>\<^sub>C \<sharp>x2 ; Z)" 
       using equiv positulatesCL1 by blast
     obtain Y where "\<sharp>x2 ; Z = Y" 
       by simp
     then have "\<P>(x1 \<turnstile>\<^sub>C \<sharp>x2 ; Z) \<longrightarrow> \<P>(formulaA (\<psi> x1) \<turnstile>\<^sub>C \<sharp>x2 ; Z)" 
       using SemiColonA.IH(1) by blast
     have "\<P>(formulaA (\<psi> x1) \<turnstile>\<^sub>C \<sharp>x2 ; Z) \<longrightarrow> \<P> (x2 \<turnstile>\<^sub>C \<sharp>(formulaA (\<psi> x1)) ; Z )"
       using equiv positulatesCL1 positulatesCL2 by blast
     obtain Y where "Y = \<sharp>(formulaA (\<psi> x1)) ; Z" by simp
     then have "\<P> (x2 \<turnstile>\<^sub>C \<sharp>(formulaA (\<psi> x1)) ; Z ) \<longrightarrow> \<P> (formulaA (\<psi> x2) \<turnstile>\<^sub>C \<sharp>(formulaA (\<psi> x1)) ; Z )"
       using SemiColonA.IH(2) by blast
     have "\<P> (formulaA (\<psi> x2) \<turnstile>\<^sub>C \<sharp>(formulaA (\<psi> x1)) ; Z ) \<longrightarrow> 
              \<P>(formulaA (\<psi> x1) ;\<^sub>A formulaA (\<psi> x2) \<turnstile>\<^sub>C Z)" 
       using equiv positulatesCL2 by blast
     have "\<P>(formulaA (\<psi> x1) ;\<^sub>A formulaA (\<psi> x2) \<turnstile>\<^sub>C Z) \<longrightarrow> \<P> (formulaA (\<psi> x1 \<and>\<^sub>B \<psi> x2) \<turnstile>\<^sub>C Z)" 
       by (simp add: andL)
     have "\<P> (formulaA (\<psi> x1 \<and>\<^sub>B \<psi> x2) \<turnstile>\<^sub>C Z) \<longrightarrow>\<P> (formulaA (\<psi> (x1 ;\<^sub>A x2)) \<turnstile>\<^sub>C Z)"
       by simp
     show ?case 
       by (metis SemiColonA.IH(1) SemiColonA.IH(2) \<psi>.simps(4) andL equiv positulatesCL1 positulatesCL2)
   qed
next
  case (CommaA X1 X2)
  then show ?case
proof -
  have "\<forall>c. \<not> \<P> (X2 \<turnstile>\<^sub>C c) \<or> \<P> (formulaA (\<psi> X2) \<turnstile>\<^sub>C c)"
by (meson CommaA.IH(2))
  then show ?thesis
    by (metis CommaA.IH(1) \<psi>.simps(6) andMultL equiv positulatesCL7 positulatesCL8)
qed
next
  case (SharpA x)
  then show ?case 
    by (metis \<psi>.simps(3) display_symm equiv notL positulatesCL5 positulatesCL6)
  

end
