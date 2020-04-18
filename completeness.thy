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
      using equiv positulatesCL1S by blast
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
      using equiv positulatesCL7S by blast
    then show ?case
      by (simp add: impMultR)
  qed
qed

lemma \<Psi>R: "\<P>(X \<turnstile>\<^sub>C formula (\<Psi> X))" and \<Upsilon>L : "\<P>(formulaA (\<Upsilon> Y) \<turnstile>\<^sub>C Y)"
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
    note \<open>\<P> (formulaA (\<Upsilon> x) \<turnstile>\<^sub>C x)\<close>
    then have "\<P> ((\<sharp>\<^sub>A x) \<turnstile>\<^sub>C (\<sharp>(formulaA(\<Upsilon> x))))" 
      using equiv positulatesCL5 by blast
    then have "\<P> ((\<sharp>\<^sub>A x) \<turnstile>\<^sub>C formula (\<not>\<^sub>B (\<Upsilon> x)))"
      by (simp add: notR)
    then show ?case 
      by auto
  qed
next
case (SemiColonA x1 x2)
  then show ?case 
  proof -
    note\<open>\<P> (x1 \<turnstile>\<^sub>C formula (\<Psi> x1))\<close>
    then have "\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C formula (\<Psi> x1))"
      using WkL by blast
    note \<open>\<P> (x2 \<turnstile>\<^sub>C formula (\<Psi> x2))\<close>
    then have "\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C formula (\<Psi> x2))" 
      using WkR equiv positulatesCL2 by blast
    note\<open>\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C formula (\<Psi> x1))\<close> \<open>\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C formula (\<Psi> x2))\<close>
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
    note\<open>\<P> (x1 \<turnstile>\<^sub>C formula (\<Psi> x1))\<close> \<open>\<P> (x2 \<turnstile>\<^sub>C formula (\<Psi> x2))\<close>
    then have "\<P>((x1 ,\<^sub>A x2) \<turnstile>\<^sub>C formula ((\<Psi> x1) *\<^sub>B (\<Psi> x2)))"
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
    note\<open>\<P> (x \<turnstile>\<^sub>C formula (\<Psi> x))\<close>
    then have "\<P>(\<sharp>\<^sub>A (formula (\<Psi> x)) \<turnstile>\<^sub>C \<sharp> x)"
      using equiv positulatesCL5 by blast
    then have "\<P>(formulaA (\<not>\<^sub>B (\<Psi> x)) \<turnstile>\<^sub>C \<sharp> x)"
      using notL by blast
    then show ?case
      by simp
  qed
next
  case (SemiColon x1 x2)
  then show ?case 
  proof-
    note \<open>\<P> (formulaA (\<Upsilon> x1) \<turnstile>\<^sub>C x1)\<close>
    then have "\<P> (formulaA (\<Upsilon> x1) \<turnstile>\<^sub>C x1 ; x2)" 
      using WkL equiv positulatesCL4 by blast
    note \<open>\<P> (formulaA (\<Upsilon> x2) \<turnstile>\<^sub>C x2)\<close>
    then have "\<P> (formulaA (\<Upsilon> x2) \<turnstile>\<^sub>C x1 ; x2)"
      using WkR by auto
    note \<open>\<P> (formulaA (\<Upsilon> x1) \<turnstile>\<^sub>C x1 ; x2)\<close> \<open>\<P> (formulaA (\<Upsilon> x2) \<turnstile>\<^sub>C x1 ; x2)\<close>
    then have "\<P> (formulaA ((\<Upsilon> x1) \<or>\<^sub>B(\<Upsilon> x2)) \<turnstile>\<^sub>C x1 ; x2)"
      by (simp add: orL)
    then show ?case
      by simp
  qed
next
  case (DotArrow x1 x2)
  then show ?case 
  proof -
    note \<open>\<P> (x1 \<turnstile>\<^sub>C formula (\<Psi> x1))\<close> \<open>\<P> (formulaA (\<Upsilon> x2) \<turnstile>\<^sub>C x2)\<close>
    then have "\<P>(formulaA ((\<Psi> x1) \<rightarrow>\<^emph>\<^sub>B (\<Upsilon> x2)) \<turnstile>\<^sub>C x1 \<rightarrow>\<circ> x2)"
      by (simp add: impMultL)
    then show ?case
      by simp
qed
qed


lemma \<Psi>L: "\<And>Y. \<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow>   \<P>(formulaA (\<Psi> X) \<turnstile>\<^sub>C Y)"
      and \<Upsilon>R : " \<And>X. \<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow>  \<P>(X \<turnstile>\<^sub>C formula (\<Upsilon> Y))"
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
      by (metis equiv positulatesCL5 positulatesCL5S positulatesCL6)
    then have "\<P> (\<sharp>\<^sub>A Y \<turnstile>\<^sub>C formula (\<Upsilon> x))" 
      by (simp add: SharpA.IH)
    then have "\<P> (\<sharp>\<^sub>A (formula (\<Upsilon> x)) \<turnstile>\<^sub>C Y )" 
      by (metis equiv positulatesCL5 positulatesCL5S positulatesCL6)
    then have "\<P> (formulaA (\<not>\<^sub>B (\<Upsilon> x)) \<turnstile>\<^sub>C Y )"
      by (simp add: notL)
    thus  "\<P> (formulaA (\<Psi> (\<sharp>\<^sub>A x)) \<turnstile>\<^sub>C Y)" 
      by simp
  qed
next
  case (SemiColonA x1 x2)
  then show ?case 
  proof -
      note \<open>\<P> (x1 ;\<^sub>A x2 \<turnstile>\<^sub>C Y)\<close>
    then have "\<P>(x1 \<turnstile>\<^sub>C \<sharp>x2 ; Y)" 
      using equiv positulatesCL1 by blast
    then have "\<P>(formulaA (\<Psi> x1) \<turnstile>\<^sub>C \<sharp>x2 ; Y)"
      by (simp add: SemiColonA.IH(1))
    then have "\<P>(x2  \<turnstile>\<^sub>C \<sharp>(formulaA (\<Psi> x1)) ; Y)"
      using equiv positulatesCL1 positulatesCL2 by blast
    then have "\<P>(formulaA (\<Psi> x2)  \<turnstile>\<^sub>C \<sharp>(formulaA (\<Psi> x1)) ; Y)" 
      using SemiColonA.IH(2) by blast
    then have "\<P>(formulaA (\<Psi> x1) ;\<^sub>A formulaA (\<Psi> x2)  \<turnstile>\<^sub>C  Y)"
      using equiv positulatesCL2 by blast
    then have "\<P>(formulaA ((\<Psi> x1) \<and>\<^sub>B (\<Psi> x2))  \<turnstile>\<^sub>C  Y)"
      using andL by blast
    thus "\<P> (formulaA (\<Psi> (x1 ;\<^sub>A x2)) \<turnstile>\<^sub>C Y)" 
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
    then have "\<P> (formulaA (\<Psi> x1) \<turnstile>\<^sub>C x2 \<rightarrow>\<circ> Y)" 
      by (simp add: CommaA.IH(1))
    then have "\<P> (x2  \<turnstile>\<^sub>C formulaA (\<Psi> x1) \<rightarrow>\<circ> Y)" 
      using equiv positulatesCL7 positulatesCL8 by blast
    then have "\<P> (formulaA (\<Psi> x2)  \<turnstile>\<^sub>C formulaA (\<Psi> x1) \<rightarrow>\<circ> Y)" 
      by (simp add: CommaA.IH(2))
    then have "\<P> (formulaA (\<Psi> x1) ,\<^sub>A  formulaA (\<Psi> x2)  \<turnstile>\<^sub>C Y)" 
      using equiv positulatesCL8 by blast
    then have "\<P> (formulaA ((\<Psi> x1) *\<^sub>B (\<Psi> x2))  \<turnstile>\<^sub>C Y)" 
      by (simp add: andMultL)
    thus "\<P> (formulaA (\<Psi>(x1 ,\<^sub>A x2))  \<turnstile>\<^sub>C Y)" by simp
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
      using equiv positulatesCL5 positulatesCL5S positulatesCL6 by blast
    then have "\<P> (formulaA (\<Psi> y) \<turnstile>\<^sub>C \<sharp>X )"
      using Sharp.IH by blast
    then have "\<P> (X  \<turnstile>\<^sub>C \<sharp>(formulaA (\<Psi> y)))" 
      using equiv positulatesCL5 positulatesCL5S positulatesCL6 by blast
    then have "\<P> (X  \<turnstile>\<^sub>C (formula (\<not>\<^sub>B(\<Psi> y))))"
      by (simp add: notR)
    thus "\<P> (X \<turnstile>\<^sub>C formula (\<Upsilon> (\<sharp> y)))" by simp
  qed
next
  case (SemiColon y1 y2)
  then show ?case 
  proof -
    note\<open>\<P> (X \<turnstile>\<^sub>C y1 ; y2)\<close>
    then have "\<P> (X ;\<^sub>A (\<sharp>\<^sub>A y1) \<turnstile>\<^sub>C y2)"
      using equiv positulatesCL3 by blast
    then have "\<P> (X ;\<^sub>A (\<sharp>\<^sub>A y1) \<turnstile>\<^sub>C formula (\<Upsilon> y2))"
      by (simp add: SemiColon.IH(2))
    then have "\<P> (X ;\<^sub>A (\<sharp>\<^sub>A (formula (\<Upsilon> y2))) \<turnstile>\<^sub>C y1)" 
      using equiv positulatesCL3 positulatesCL4 by blast
    then have "\<P> (X ;\<^sub>A (\<sharp>\<^sub>A (formula (\<Upsilon> y2))) \<turnstile>\<^sub>C formula (\<Upsilon> y1))" 
      using SemiColon.IH(1) by blast
    then have "\<P> (X \<turnstile>\<^sub>C formula (\<Upsilon> y1) ; formula (\<Upsilon> y2))"
      using equiv positulatesCL4 by blast
    then have "\<P> (X \<turnstile>\<^sub>C formula ((\<Upsilon> y1) \<or>\<^sub>B (\<Upsilon> y2)))" 
      using orR by blast
    thus "\<P>(X \<turnstile>\<^sub>C formula (\<Upsilon> (y1 ; y2)))" by simp
  qed
next
  case (DotArrow x1 y2)
  then show ?case 
  proof -
    note\<open>\<P> (X \<turnstile>\<^sub>C x1 \<rightarrow>\<circ> y2)\<close>
    then have "\<P>(x1 \<turnstile>\<^sub>C X \<rightarrow>\<circ> y2)" 
      using equiv positulatesCL7 positulatesCL8 by blast
    then have "\<P>(formulaA (\<Psi> x1) \<turnstile>\<^sub>C X \<rightarrow>\<circ> y2)" 
      using DotArrow.IH(1) by blast
    then have "\<P>(formulaA (\<Psi> x1) ,\<^sub>A X \<turnstile>\<^sub>C y2)" 
      using equiv positulatesCL7 positulatesCL8 by blast 
    then have "\<P>(formulaA (\<Psi> x1) ,\<^sub>A X \<turnstile>\<^sub>C formula (\<Upsilon> y2))"
      by (simp add: DotArrow.IH(2))
    then have "\<P>(X ,\<^sub>A formulaA (\<Psi> x1) \<turnstile>\<^sub>C formula (\<Upsilon> y2))"
      using equiv positulatesCL7 positulatesCL8 by blast
    then have "\<P> (X \<turnstile>\<^sub>C formula ((\<Psi> x1) \<rightarrow>\<^emph>\<^sub>B(\<Upsilon> y2)))"
      by (simp add: impMultR)
    thus "\<P> (X \<turnstile>\<^sub>C formula (\<Upsilon> (x1 \<rightarrow>\<circ> y2)))" 
      by simp
  qed   
qed


section "Completeness"

lemma intermediate: "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y \<Longrightarrow> \<P>(formulaA (\<Psi> X) \<turnstile>\<^sub>C formula (\<Upsilon> Y))"
proof(induction rule: turnstile_BBI.induct)
case (Ax F)
  then show ?case 
    by (simp add: identity)
next
  case (Top F)
  then show ?case using TopR by simp
next
  case (Bot F)
  then show ?case using BotL by simp
next
  case (ImpT F G H)
  then show ?case 
  proof-
    note \<open>\<P> (formulaA (F \<and>\<^sub>B G) \<turnstile>\<^sub>C formula H)\<close>
    hence "\<P> (formulaA (\<Psi> (formulaA F ;\<^sub>A formulaA G)) \<turnstile>\<^sub>C formula H)" 
      by simp
    hence "\<P> (formulaA F ;\<^sub>A formulaA G \<turnstile>\<^sub>C formula H)" using cut \<Psi>R by blast
    thus ?case 
      using impR by blast
  qed
next
  case (ImpB F G H)
  then show ?case 
  proof-
  (* G \<turnstile> G && H \<turnstile> H *)
    have "\<P>(formulaA (G \<rightarrow>\<^sub>B H) \<turnstile>\<^sub>C \<sharp>(formulaA G) ; formula H)"
      by (simp add: identity impL)
    note\<open>\<P>(formulaA (G \<rightarrow>\<^sub>B H) \<turnstile>\<^sub>C \<sharp>(formulaA G) ; formula H)\<close> \<open>\<P> (formulaA F \<turnstile>\<^sub>C formula (G \<rightarrow>\<^sub>B H))\<close>
    hence "\<P>(formulaA F \<turnstile>\<^sub>C \<sharp>(formulaA G) ; formula H)"
      using cut by blast
    hence "\<P>(formulaA F ;\<^sub>A formulaA G \<turnstile>\<^sub>C formula H)"
      using equiv positulatesCL1 positulatesCL2 by blast
    thus ?case 
      using andL by blast
  qed
next
  case (MP F G H)
  then show ?case using cut by blast
next
  case (Notl F)
  then show ?case 
  proof-
    have"\<P>(formulaA F \<turnstile>\<^sub>C formula F)" using identity by simp
    hence"\<P>(\<sharp>\<^sub>A(formula F) \<turnstile>\<^sub>C \<sharp>(formulaA F))" 
      using equiv positulatesCL5 by blast
    hence "\<P>(\<sharp>\<^sub>A(formula F) \<turnstile>\<^sub>C (formula \<bottom>\<^sub>B) ; \<sharp>(formulaA F))"using WkR by simp
    hence "\<P>(\<sharp>\<^sub>A(formula F) \<turnstile>\<^sub>C  \<sharp>(formulaA F) ; (formula \<bottom>\<^sub>B))" 
      using equiv positulatesCL3 positulatesCL4 by blast
    hence "\<P>(\<sharp>\<^sub>A(formula F) ;\<^sub>A formulaA F \<turnstile>\<^sub>C (formula \<bottom>\<^sub>B))" 
      using equiv positulatesCL1S by blast
    hence "\<P>(\<sharp>\<^sub>A(formula F) \<turnstile>\<^sub>C formula(F \<rightarrow>\<^sub>B \<bottom>\<^sub>B))" 
      by (simp add: impR)
    thus ?case 
      by (simp add: notL)
  qed
next
  case (Notr F)
  then show ?case 
  proof-
    have "\<P>(formulaA F \<turnstile>\<^sub>C formula F)" using identity by simp
    have "\<P>(formulaA \<bottom>\<^sub>B \<turnstile>\<^sub>C \<sharp>(formulaA F))"
      by (simp add: BotL)
    have "\<P>(formulaA (F \<rightarrow>\<^sub>B \<bottom>\<^sub>B) \<turnstile>\<^sub>C \<sharp>(formulaA F) ; \<sharp>(formulaA F))" 
      by (simp add: \<open>\<P> (formulaA F \<turnstile>\<^sub>C formula F)\<close> \<open>\<P> (formulaA \<bottom>\<^sub>B \<turnstile>\<^sub>C \<sharp> (formulaA F))\<close> impL)
    hence "\<P>(formulaA (F \<rightarrow>\<^sub>B \<bottom>\<^sub>B) \<turnstile>\<^sub>C \<sharp>(formulaA F))" using CtrR by blast
    thus ?case 
      by (simp add: notR)
  qed
next
  case (Notnot F)
  then show ?case 
  proof-
    have "\<P>(formulaA F \<turnstile>\<^sub>C formula F)" using identity by simp
    hence"\<P>(\<sharp>\<^sub>A(formula F) \<turnstile>\<^sub>C \<sharp>(formulaA F))" 
      using equiv positulatesCL5 by blast
    hence "\<P>(\<sharp>\<^sub>A(formula F) \<turnstile>\<^sub>C formula(\<not>\<^sub>B F))" 
      using notR by simp
    hence "\<P>(\<sharp>\<^sub>A(formula (\<not>\<^sub>B F)) \<turnstile>\<^sub>C formula F)"
      by (metis \<Upsilon>.simps(1) \<Upsilon>.simps(3) \<open>\<P> (\<sharp>\<^sub>A (formula F) \<turnstile>\<^sub>C \<sharp> (formulaA F))\<close> \<Psi>.simps(1) \<Psi>.simps(3) \<Psi>L \<Psi>R cut equiv positulatesCL6)
    thus ?case
      by (simp add: notL)
  qed
next
  case (ConjI F G H)
  then show ?case using andR by blast
next
  case (DisjE F H G)
  then show ?case using orL by blast
next
  case (ConjE1 F G)
  then show ?case 
  proof-
    have "\<P>(formulaA F \<turnstile>\<^sub>C formula F)" using identity by simp
    hence "\<P>((formulaA F) ;\<^sub>A (formulaA G) \<turnstile>\<^sub>C formula F)" 
      using WkL by blast
    thus ?case using andL by simp
  qed
next
  case (ConjE2 F G)
  then show ?case 
  proof-
    have "\<P>(formulaA G \<turnstile>\<^sub>C formula G)" using identity by simp
    hence "\<P>((formulaA G) ;\<^sub>A (formulaA F) \<turnstile>\<^sub>C formula G)" 
      using WkL by blast
    hence "\<P>((formulaA F) ;\<^sub>A (formulaA G) \<turnstile>\<^sub>C formula G)" 
      using equiv positulatesCL1 positulatesCL2 by blast
    thus ?case 
      by (simp add: andL)
  qed
next
  case (DisjI1 F G)
  then show ?case 
  proof-
    have "\<P>(formulaA F \<turnstile>\<^sub>C formula F)" using identity by simp
    hence "\<P>(formulaA F \<turnstile>\<^sub>C formula G ; formula F)" using WkR by blast
    hence "\<P>(formulaA F \<turnstile>\<^sub>C formula F ; formula G)"
      using equiv positulatesCL3 positulatesCL4 by blast
    thus ?case 
      by (simp add: orR)
  qed
next
  case (DisjI2 G F)
  then show ?case 
  proof-
    have "\<P>(formulaA G \<turnstile>\<^sub>C formula G)" using identity by simp
    hence "\<P>(formulaA G \<turnstile>\<^sub>C formula F ; formula G)"
      by (simp add: WkR)
    thus ?case
      by (simp add: orR)
  qed
next
  case (Topl F)
  then show ?case 
  proof-
    have "\<P>(formulaA F \<turnstile>\<^sub>C formula F)" using identity by simp
    hence "\<P>(\<oslash> ,\<^sub>A formulaA F \<turnstile>\<^sub>C formula F)"
      using nilMultL_sym by blast
    hence "\<P>(\<oslash> \<turnstile>\<^sub>C formulaA F \<rightarrow>\<circ> formula F)" 
      using equiv positulatesCL7 by blast
    hence "\<P>(formulaA \<top>\<^sup>*\<^sub>B \<turnstile>\<^sub>C formulaA F \<rightarrow>\<circ> formula F)"
      using TopMultL by blast
    hence "\<P>(formulaA F ,\<^sub>A formulaA \<top>\<^sup>*\<^sub>B \<turnstile>\<^sub>C  formula F)" 
      using equiv positulatesCL8 by blast
    thus ?case 
      by (simp add: andMultL)
  qed
next
  case (Topr F)
  then show ?case 
  proof-
    have "\<P>(formulaA F \<turnstile>\<^sub>C formula F)" using identity by simp
    hence "\<P>(formulaA F ,\<^sub>A \<oslash> \<turnstile>\<^sub>C formula (F *\<^sub>B \<top>\<^sup>*\<^sub>B))"
      using TopMultR andMultR by blast
    hence "\<P>(\<oslash> ,\<^sub>A formulaA F \<turnstile>\<^sub>C formula (F *\<^sub>B \<top>\<^sup>*\<^sub>B))" 
      using equiv positulatesCL7 positulatesCL8 by blast
    thus ?case 
      using nilMultL by blast
  qed
next
  case (ImpstarT F G H)
  then show ?case 
  proof-
    note\<open>\<P> (formulaA (F *\<^sub>B G) \<turnstile>\<^sub>C formula H)\<close>
    hence "\<P> (formulaA (\<Psi> (formulaA F) *\<^sub>B \<Psi> (formulaA G)) \<turnstile>\<^sub>C formula H)" 
      by simp
    hence "\<P> (formulaA (\<Psi> (formulaA F ,\<^sub>A formulaA G)) \<turnstile>\<^sub>C formula H)" 
      by simp
    hence "\<P> (formulaA F ,\<^sub>A formulaA G \<turnstile>\<^sub>C formula H)"
      using \<Psi>R cut by blast
    thus ?case
      using impMultR by blast
  qed
  
next
  case (ImpstarB F G H)
  then show ?case 
  proof-
    note \<open>\<P> (formulaA F \<turnstile>\<^sub>C formula (G \<rightarrow>\<^emph>\<^sub>B H))\<close>
    hence "\<P> (formulaA F \<turnstile>\<^sub>C formulaA G \<rightarrow>\<circ> formula H)" 
      using cut identity impMultL by blast
    hence "\<P> (formulaA F ,\<^sub>A formulaA G \<turnstile>\<^sub>C formula H)"
      using equiv positulatesCL7S by blast
    thus ?case 
      by (simp add: andMultL)
  qed
next
  case (Assocl F G H)
  then show ?case 
  proof-
    have "\<P>(formulaA F ,\<^sub>A formulaA G \<turnstile>\<^sub>C formula(F *\<^sub>B G))" 
      by (simp add: andMultR identity)
    have "\<P>(formulaA H \<turnstile>\<^sub>C formula H)" using identity by simp
    have "\<P>((formulaA F ,\<^sub>A formulaA G) ,\<^sub>A formulaA H \<turnstile>\<^sub>C formula((F *\<^sub>B G) *\<^sub>B H))"
      using \<open>\<P> (formulaA F ,\<^sub>A formulaA G \<turnstile>\<^sub>C formula (F *\<^sub>B G))\<close> 
            \<open>\<P> (formulaA H \<turnstile>\<^sub>C formula H)\<close> andMultR by auto
    hence "\<P>(formulaA F ,\<^sub>A (formulaA G ,\<^sub>A formulaA H) \<turnstile>\<^sub>C formula((F *\<^sub>B G) *\<^sub>B H))" 
      by (simp add: MAL_sym)
    thus ?case 
      using \<Psi>L by force
  qed
next
  case (Assocr F G H)
  then show ?case 
  proof- 
    have "\<P>(formulaA G ,\<^sub>A formulaA H \<turnstile>\<^sub>C formula (G *\<^sub>B H))" 
      by (simp add: andMultR identity)
    hence "\<P>(formulaA F ,\<^sub>A (formulaA G ,\<^sub>A formulaA H) \<turnstile>\<^sub>C formula (F *\<^sub>B (G *\<^sub>B H)))"
      by (simp add: andMultR identity)
    hence "\<P>((formulaA F ,\<^sub>A formulaA G) ,\<^sub>A formulaA H \<turnstile>\<^sub>C formula (F *\<^sub>B (G *\<^sub>B H)))" 
      using MAL by blast
    thus ?case 
      using \<Psi>L by force
  qed
next
  case (Comm F G)
  then show ?case 
  proof-
    have "\<P>(formulaA G ,\<^sub>A formulaA F \<turnstile>\<^sub>C formula (G *\<^sub>B F))" 
      using andMultR identity by auto
    hence "\<P>(formulaA F ,\<^sub>A formulaA G \<turnstile>\<^sub>C formula (G *\<^sub>B F))" 
      using equiv positulatesCL7 positulatesCL8 by blast
    thus ?case
      by (simp add: andMultL)
  qed
next
  case (ConjIstar F1 G1 F2 G2)
  then show ?case 
  proof-
    note \<open>\<P> (formulaA F1 \<turnstile>\<^sub>C formula G1)\<close> \<open>\<P> (formulaA F2 \<turnstile>\<^sub>C formula G2)\<close>
    hence  "\<P>(formulaA F1 ,\<^sub>A formulaA F2 \<turnstile>\<^sub>C formula (G1 *\<^sub>B G2))" 
      by (simp add: andMultR)
    thus ?case
      by (simp add: andMultL)
  qed
qed

theorem Completeness: "Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P>(X \<turnstile>\<^sub>C Y)"
  apply simp
proof-
  assume "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y"
  have "\<P>(X \<turnstile>\<^sub>C formula(\<Psi> X))"
    by (simp add: \<Psi>R)
  have "\<P>(formulaA(\<Psi> X) \<turnstile>\<^sub>C Y)"
  proof-
    note\<open>\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y\<close>
    then have "\<P>(formulaA (\<Psi> X) \<turnstile>\<^sub>C formula (\<Upsilon> Y))"
      by (simp add: intermediate)
    have "\<P>(formulaA (\<Upsilon> Y) \<turnstile>\<^sub>C Y)"
      by (simp add: \<Upsilon>L)
    note \<open>\<P>(formulaA (\<Psi> X) \<turnstile>\<^sub>C formula (\<Upsilon> Y))\<close>\<open>\<P>(formulaA (\<Upsilon> Y) \<turnstile>\<^sub>C Y)\<close>
    thus ?thesis 
      using cut by blast
  qed
  note\<open>\<P>(X \<turnstile>\<^sub>C formula(\<Psi> X))\<close> \<open>\<P>(formulaA(\<Psi> X) \<turnstile>\<^sub>C Y)\<close>
  thus ?thesis 
    using cut by blast
qed

end