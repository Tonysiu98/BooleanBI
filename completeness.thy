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
  then show ?case sorry
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

lemma \<psi>L: "\<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P>(formulaA (\<psi> X) \<turnstile>\<^sub>C Y)"
      and \<gamma>R : "\<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P>(X \<turnstile>\<^sub>C formula (\<gamma> Y))"
proof(induction X and Y)
case (formulaA x)
then show ?case
  by auto
next
  case AddNilA
  then show ?case
    by (simp add: TopL)
next
  case (SharpA x)
  then show ?case 
    sorry
next
  case (SemiColonA x1 x2)
  then show ?case sorry
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






theorem Completeness: "Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P>(X \<turnstile>\<^sub>C Y)"
  apply simp
proof(induction rule: turnstile_BBI.induct)
case (Id atom)
then show ?case sorry
next
  case (Ax F)
  then show ?case sorry
next
  case (Top F)
  then show ?case sorry
next
  case (Bot F)
  then show ?case sorry
next
  case (ImpT F G H)
  then show ?case sorry
next
  case (ImpB F G H)
  then show ?case sorry
next
  case (MP F G H)
  then show ?case sorry
next
  case (Notl F)
  then show ?case sorry
next
  case (Notr F)
  then show ?case sorry
next
  case (Notnot F)
  then show ?case sorry
next
  case (ConjI F G H)
  then show ?case sorry
next
  case (DisjE F H G)
  then show ?case sorry
next
  case (ConjE1 G1 G2)
  then show ?case sorry
next
  case (ConjE2 G1 G2)
  then show ?case sorry
next
  case (DisjI1 G1 G2)
  then show ?case sorry
next
  case (DisjI2 G2 G1)
  then show ?case sorry
next
  case (Topl F)
  then show ?case sorry
next
  case (Topr F)
  then show ?case sorry
next
  case (ImpstarT F G H)
  then show ?case sorry
next
  case (ImpstarB F G H)
  then show ?case sorry
next
  case (Assocl F G H)
  then show ?case sorry
next
  case (Assocr F G H)
  then show ?case sorry
next
  case (Comm F G)
  then show ?case sorry
next
  case (ConjIstar F1 G1 F2 G2)
  then show ?case sorry
qed



end