theory completeness
    imports Main def
begin




lemma identity: "\<P>(formulaA F \<turnstile>\<^sub>C formula F)"
proof(induction F)
case Truth
then show ?case 
  by (simp add: TopR)
next
case Falsity
  then show ?case 
    by (simp add: BotL)
next
  case MTruth
  then show ?case 
    by (simp add: TopMultL TopMultR)
next
  case (Atom x)
  then show ?case 
    by (simp add: id)
next
  case (Neg F)
  then show ?case 
  proof-
    have "\<P>(\<sharp>\<^sub>A (formula F) \<turnstile>\<^sub>C \<sharp> (formulaA F))" 
      using Neg.IH equiv positulatesCL5 by blast
    then have "\<P>(\<sharp>\<^sub>A (formula F) \<turnstile>\<^sub>C (formula (\<not>\<^sub>B F)))"
      by (simp add: notR)
    then have "\<P>((formulaA (\<not>\<^sub>B F)) \<turnstile>\<^sub>C (formula (\<not>\<^sub>B F)))"
      by (simp add: notL)
    then show ?case 
      by simp
  qed
next
  case (Con F1 F2)
  then show ?case 
  proof-
    note \<open>\<P> (formulaA F1 \<turnstile>\<^sub>C formula F1)\<close>
    then have "\<P>(((formulaA F1) ;\<^sub>A (formulaA F2)) \<turnstile>\<^sub>C formula F1)" 
      by (simp add: WkL)
    then have "\<P>((formulaA (F1 \<and>\<^sub>B F2)) \<turnstile>\<^sub>C formula F1)"
      by (simp add: andL)
    note \<open>\<P> (formulaA F2 \<turnstile>\<^sub>C formula F2)\<close>
    then have "\<P>(((formulaA F2) ;\<^sub>A (formulaA F1)) \<turnstile>\<^sub>C formula F2)"
      using WkL by auto
    then have "\<P>(((formulaA F1) ;\<^sub>A (formulaA F2)) \<turnstile>\<^sub>C formula F2)" 
      using equiv positulatesCL1 positulatesCL2 by blast
    then have "\<P>((formulaA (F1 \<and>\<^sub>B F2)) \<turnstile>\<^sub>C formula F2)"
      by (simp add: andL)
    note \<open>\<P>((formulaA (F1 \<and>\<^sub>B F2)) \<turnstile>\<^sub>C formula F1)\<close> \<open>\<P>((formulaA (F1 \<and>\<^sub>B F2)) \<turnstile>\<^sub>C formula F2)\<close>
    then show ?case
      by (simp add: andR)
  qed
next
  case (MCon F1 F2)
  then show ?case
  proof -
    note \<open>\<P> (formulaA F1 \<turnstile>\<^sub>C formula F1)\<close> \<open>\<P> (formulaA F2 \<turnstile>\<^sub>C formula F2)\<close>
    then have "\<P>(((formulaA F1) ,\<^sub>A (formulaA F2)) \<turnstile>\<^sub>C formula (F1 *\<^sub>B F2))" 
      using andMultR by blast
    then show ?case
      by (simp add: andMultL)
  qed
next
  case (Dis F1 F2)
  then show ?case 
  proof -
    note \<open>\<P> (formulaA F1 \<turnstile>\<^sub>C formula F1)\<close>
    then have "\<P>(formulaA F1 \<turnstile>\<^sub>C ((formula F1) ; (formula F2)))"
      using WkL equiv positulatesCL4 by blast
    note \<open>\<P> (formulaA F2 \<turnstile>\<^sub>C formula F2)\<close>
    then have "\<P>(formulaA F2 \<turnstile>\<^sub>C ((formula F1) ; (formula F2)))"
      using WkR by auto
    note\<open>\<P>(formulaA F1 \<turnstile>\<^sub>C ((formula F1) ; (formula F2)))\<close>
        \<open>\<P>(formulaA F2 \<turnstile>\<^sub>C ((formula F1) ; (formula F2)))\<close>
    then show ?case 
      by (simp add: orL orR)
  qed
next
  case (Imp F1 F2)
  then show ?case 
  proof -
    note\<open>\<P> (formulaA F1 \<turnstile>\<^sub>C formula F1)\<close>\<open>\<P> (formulaA F2 \<turnstile>\<^sub>C formula F2)\<close>
    then have "\<P>(formulaA (F1 \<rightarrow>\<^sub>B F2) \<turnstile>\<^sub>C ((\<sharp> (formulaA F1)) ; (formula F2)))" 
      using impL by blast
    then have "\<P>(((formulaA (F1 \<rightarrow>\<^sub>B F2)) ;\<^sub>A (formulaA F1)) \<turnstile>\<^sub>C formula F2)"
      using display_symm equiv positulatesCL1 by blast
    then show ?case 
      by (simp add: impR)
  qed
next
  case (Mimp F1 F2)
  then show ?case 
  proof -
    note \<open>\<P> (formulaA F1 \<turnstile>\<^sub>C formula F1)\<close> \<open>\<P> (formulaA F2 \<turnstile>\<^sub>C formula F2)\<close>
    then have "\<P>(formulaA (F1 \<rightarrow>\<^emph>\<^sub>B F2) \<turnstile>\<^sub>C (((formulaA F1)) \<rightarrow>\<circ> (formula F2)))" 
      using impMultL by blast
    then have "\<P>((formulaA (F1 \<rightarrow>\<^emph>\<^sub>B F2) ,\<^sub>A (formulaA F1)) \<turnstile>\<^sub>C formula F2 )"
      using display_symm equiv positulatesCL7 by blast
    then show ?case
      by (simp add: impMultR)
  qed
qed

lemma \<psi>R: "\<P>(X \<turnstile>\<^sub>C formula (\<psi> X))" and \<gamma>Y : "\<P>(formulaA (\<gamma> Y) \<turnstile>\<^sub>C Y)"
proof(induction X and Y)
case (formulaA x)
  then show ?case 
    by (simp add: identity)
next
case AddNilA
  then show ?case 
    by (simp add: TopR)
next
case (SharpA x)
  then show ?case 
  proof-
    note \<open>\<P> (formulaA (\<gamma> x) \<turnstile>\<^sub>C x)\<close>
    then have "\<P> ((\<sharp>\<^sub>A x) \<turnstile>\<^sub>C (\<sharp>(formulaA(\<gamma> x))))" 
      using equiv positulatesCL5 by blast
    then have "\<P> ((\<sharp>\<^sub>A x) \<turnstile>\<^sub>C formula (\<not>\<^sub>B (\<gamma> x)))"
      by (simp add: notR)
    then show ?case 
      by auto
  qed
next
case (SemiColonA x1 x2)
  then show ?case 
  proof -
    note\<open>\<P> (x1 \<turnstile>\<^sub>C formula (\<psi> x1))\<close>
    then have "\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C formula (\<psi> x1))"
      using WkL by blast
    note \<open>\<P> (x2 \<turnstile>\<^sub>C formula (\<psi> x2))\<close>
    then have "\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C formula (\<psi> x2))" 
      using WkR equiv positulatesCL2 by blast
    note\<open>\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C formula (\<psi> x1))\<close> \<open>\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C formula (\<psi> x2))\<close>
    then show ?case 
      using andR by auto
  qed
next
  case MultNilA
  then show ?case
    by (simp add: TopMultR)
next
  case (CommaA x1 x2)
  then show ?case 
  proof -
    note\<open>\<P> (x1 \<turnstile>\<^sub>C formula (\<psi> x1))\<close> \<open>\<P> (x2 \<turnstile>\<^sub>C formula (\<psi> x2))\<close>
    then have "\<P>((x1 ,\<^sub>A x2) \<turnstile>\<^sub>C formula ((\<psi> x1) *\<^sub>B (\<psi> x2)))"
      by (simp add: andMultR)
    then show ?case
      by simp
  qed
next
  case (formula x)
  then show ?case
    by (simp add: identity)
next
  case AddNil
  then show ?case
    by (simp add: BotL)
next
  case (Sharp x)
  then show ?case 
  proof -
    note\<open>\<P> (x \<turnstile>\<^sub>C formula (\<psi> x))\<close>
    then have "\<P>(\<sharp>\<^sub>A (formula (\<psi> x)) \<turnstile>\<^sub>C \<sharp> x)"
      using equiv positulatesCL5 by blast
    then have "\<P>(formulaA (\<not>\<^sub>B (\<psi> x)) \<turnstile>\<^sub>C \<sharp> x)"
      using notL by blast
    then show ?case
      by simp
  qed
next
  case (SemiColon x1 x2)
  then show ?case 
  proof-
    note \<open>\<P> (formulaA (\<gamma> x1) \<turnstile>\<^sub>C x1)\<close>
    then have "\<P> (formulaA (\<gamma> x1) \<turnstile>\<^sub>C x1 ; x2)" 
      using WkL equiv positulatesCL4 by blast
    note \<open>\<P> (formulaA (\<gamma> x2) \<turnstile>\<^sub>C x2)\<close>
    then have "\<P> (formulaA (\<gamma> x2) \<turnstile>\<^sub>C x1 ; x2)"
      using WkR by auto
    note \<open>\<P> (formulaA (\<gamma> x1) \<turnstile>\<^sub>C x1 ; x2)\<close> \<open>\<P> (formulaA (\<gamma> x2) \<turnstile>\<^sub>C x1 ; x2)\<close>
    then have "\<P> (formulaA ((\<gamma> x1) \<or>\<^sub>B(\<gamma> x2)) \<turnstile>\<^sub>C x1 ; x2)"
      by (simp add: orL)
    then show ?case
      by simp
  qed
next
  case (DotArrow x1 x2)
  then show ?case 
  proof -
    note \<open>\<P> (x1 \<turnstile>\<^sub>C formula (\<psi> x1))\<close> \<open>\<P> (formulaA (\<gamma> x2) \<turnstile>\<^sub>C x2)\<close>
    then have "\<P>(formulaA ((\<psi> x1) \<rightarrow>\<^emph>\<^sub>B (\<gamma> x2)) \<turnstile>\<^sub>C x1 \<rightarrow>\<circ> x2)"
      by (simp add: impMultL)
    then show ?case
      by simp
qed
qed


lemma \<psi>L: "\<And>Y. \<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow>   \<P>(formulaA (\<psi> X) \<turnstile>\<^sub>C Y)"
      and \<gamma>R : " \<And>X. \<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow>  \<P>(X \<turnstile>\<^sub>C formula (\<gamma> Y))"
proof(induction X and Y)
case (formulaA x)
then show ?case 
  by auto
next
case AddNilA
then show ?case
  using TopL by auto
next
case (SharpA x)
  then show ?case 
  proof-
    note\<open>\<P> (\<sharp>\<^sub>A x \<turnstile>\<^sub>C Y)\<close>
    then have "\<P> (\<sharp>\<^sub>A Y \<turnstile>\<^sub>C x)" 
      by (meson display_symm equiv positulatesCL5 positulatesCL6)
    then have "\<P> (\<sharp>\<^sub>A Y \<turnstile>\<^sub>C formula (\<gamma> x))" 
      by (simp add: SharpA.IH)
    then have "\<P> (\<sharp>\<^sub>A (formula (\<gamma> x)) \<turnstile>\<^sub>C Y )" 
      by (meson display_symm equiv positulatesCL5 positulatesCL6)
    then have "\<P> (formulaA (\<not>\<^sub>B (\<gamma> x)) \<turnstile>\<^sub>C Y )"
      by (simp add: notL)
    thus  "\<P> (formulaA (\<psi> (\<sharp>\<^sub>A x)) \<turnstile>\<^sub>C Y)" 
      by simp
  qed
next
  case (SemiColonA x1 x2)
  then show ?case 
  proof -
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
  then show ?case 
    by (simp add: TopMultL)
next
  case (CommaA x1 x2)
  then show ?case 
  proof -
    note\<open>\<P> (x1 ,\<^sub>A x2 \<turnstile>\<^sub>C Y)\<close>
    then have "\<P> (x1 \<turnstile>\<^sub>C x2 \<rightarrow>\<circ> Y)" 
      using equiv positulatesCL7 by blast
    then have "\<P> (formulaA (\<psi> x1) \<turnstile>\<^sub>C x2 \<rightarrow>\<circ> Y)" 
      by (simp add: CommaA.IH(1))
    then have "\<P> (x2  \<turnstile>\<^sub>C formulaA (\<psi> x1) \<rightarrow>\<circ> Y)" 
      using equiv positulatesCL7 positulatesCL8 by blast
    then have "\<P> (formulaA (\<psi> x2)  \<turnstile>\<^sub>C formulaA (\<psi> x1) \<rightarrow>\<circ> Y)" 
      by (simp add: CommaA.IH(2))
    then have "\<P> (formulaA (\<psi> x1) ,\<^sub>A  formulaA (\<psi> x2)  \<turnstile>\<^sub>C Y)" 
      using equiv positulatesCL8 by blast
    then have "\<P> (formulaA ((\<psi> x1) *\<^sub>B (\<psi> x2))  \<turnstile>\<^sub>C Y)" 
      by (simp add: andMultL)
    thus "\<P> (formulaA (\<psi>(x1 ,\<^sub>A x2))  \<turnstile>\<^sub>C Y)" by simp
  qed
next
  case (formula x)
  then show ?case 
    by auto
next
  case AddNil
  then show ?case 
    using BotR by auto
next
  case (Sharp y)
  then show ?case 
  proof -
    note\<open>\<P> (X \<turnstile>\<^sub>C \<sharp> y)\<close>
    then have "\<P> (y \<turnstile>\<^sub>C \<sharp>X)" 
      using display_symm equiv positulatesCL5 positulatesCL6 by blast
    then have "\<P> (formulaA (\<psi> y) \<turnstile>\<^sub>C \<sharp>X )"
      using Sharp.IH by blast
    then have "\<P> (X  \<turnstile>\<^sub>C \<sharp>(formulaA (\<psi> y)))" 
      using display_symm equiv positulatesCL5 positulatesCL6 by blast
    then have "\<P> (X  \<turnstile>\<^sub>C (formula (\<not>\<^sub>B(\<psi> y))))"
      by (simp add: notR)
    thus "\<P> (X \<turnstile>\<^sub>C formula (\<gamma> (\<sharp> y)))" by simp
  qed
next
  case (SemiColon y1 y2)
  then show ?case 
  proof -
    note\<open>\<P> (X \<turnstile>\<^sub>C y1 ; y2)\<close>
    then have "\<P> (X ;\<^sub>A (\<sharp>\<^sub>A y1) \<turnstile>\<^sub>C y2)"
      using equiv positulatesCL3 by blast
    then have "\<P> (X ;\<^sub>A (\<sharp>\<^sub>A y1) \<turnstile>\<^sub>C formula (\<gamma> y2))"
      by (simp add: SemiColon.IH(2))
    then have "\<P> (X ;\<^sub>A (\<sharp>\<^sub>A (formula (\<gamma> y2))) \<turnstile>\<^sub>C y1)" 
      using equiv positulatesCL3 positulatesCL4 by blast
    then have "\<P> (X ;\<^sub>A (\<sharp>\<^sub>A (formula (\<gamma> y2))) \<turnstile>\<^sub>C formula (\<gamma> y1))" 
      using SemiColon.IH(1) by blast
    then have "\<P> (X \<turnstile>\<^sub>C formula (\<gamma> y1) ; formula (\<gamma> y2))"
      using equiv positulatesCL4 by blast
    then have "\<P> (X \<turnstile>\<^sub>C formula ((\<gamma> y1) \<or>\<^sub>B (\<gamma> y2)))" 
      using orR by blast
    thus "\<P>(X \<turnstile>\<^sub>C formula (\<gamma> (y1 ; y2)))" by simp
  qed
next
  case (DotArrow x1 y2)
  then show ?case 
  proof -
    note\<open>\<P> (X \<turnstile>\<^sub>C x1 \<rightarrow>\<circ> y2)\<close>
    then have "\<P>(x1 \<turnstile>\<^sub>C X \<rightarrow>\<circ> y2)" 
      using equiv positulatesCL7 positulatesCL8 by blast
    then have "\<P>(formulaA (\<psi> x1) \<turnstile>\<^sub>C X \<rightarrow>\<circ> y2)" 
      using DotArrow.IH(1) by blast
    then have "\<P>(formulaA (\<psi> x1) ,\<^sub>A X \<turnstile>\<^sub>C y2)" 
      using equiv positulatesCL7 positulatesCL8 by blast 
    then have "\<P>(formulaA (\<psi> x1) ,\<^sub>A X \<turnstile>\<^sub>C formula (\<gamma> y2))"
      by (simp add: DotArrow.IH(2))
    then have "\<P>(X ,\<^sub>A formulaA (\<psi> x1) \<turnstile>\<^sub>C formula (\<gamma> y2))"
      using equiv positulatesCL7 positulatesCL8 by blast
    then have "\<P> (X \<turnstile>\<^sub>C formula ((\<psi> x1) \<rightarrow>\<^emph>\<^sub>B(\<gamma> y2)))"
      by (simp add: impMultR)
    thus "\<P> (X \<turnstile>\<^sub>C formula (\<gamma> (x1 \<rightarrow>\<circ> y2)))" 
      by simp
  qed   
qed



section "Completeness"
(*
theorem Completeness: "Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P>(X \<turnstile>\<^sub>C Y)"
  apply simp
proof-
  have "\<P>(X \<turnstile>\<^sub>C formula(\<psi> X))"
    by (simp add: \<psi>R)
  have "\<P>(formulaA(\<psi> X) \<turnstile>\<^sub>C Y)"
  proof-
    have "\<P>(formulaA (\<psi> X) \<turnstile>\<^sub>C formula (\<gamma> Y))" sorry
    have "\<P>(formulaA (\<gamma> Y) \<turnstile>\<^sub>C Y)"
      by (simp add: \<gamma>Y)
    note \<open>\<P>(formulaA (\<psi> X) \<turnstile>\<^sub>C formula (\<gamma> Y))\<close>\<open>\<P>(formulaA (\<gamma> Y) \<turnstile>\<^sub>C Y)\<close>
    thus ?thesis 
      using cut by blast
  qed
  note\<open>\<P>(X \<turnstile>\<^sub>C formula(\<psi> X))\<close> \<open>\<P>(formulaA(\<psi> X) \<turnstile>\<^sub>C Y)\<close>
  thus ?thesis 
    using cut by blast
qed
*)
end