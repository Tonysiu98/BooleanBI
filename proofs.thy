theory proofs
  imports Main def
begin
section"Soundness and Completeness"

lemma  "A \<longrightarrow> B \<Longrightarrow> \<not>A \<or> B"
proof -
  assume "A \<longrightarrow> B"
  have "\<not>\<not>(\<not>A \<or> B)"
  proof
    assume "\<not>(\<not>A \<or> B)"
    have "\<not>\<not> A"
    proof
      assume "\<not> A"
      show False
      proof - 
        have "\<not>A \<or> B" 
          by (simp add: \<open>\<not> A\<close>)
        show False 
          using \<open>\<not> (\<not> A \<or> B)\<close> \<open>\<not> A\<close> by auto
      qed
    qed
    from \<open>\<not>\<not> A\<close> have A by blast
    then have B using \<open>A \<longrightarrow> B\<close> by blast
    hence "\<not>A \<or> B" by (rule disjI2)
    thus False using \<open>\<not> (\<not> A \<or> B)\<close> by blast
  qed
  then have "\<not>A \<or> B" using \<open>\<not>\<not>(\<not>A \<or> B)\<close> by blast
  thus ?thesis 
    by blast
qed
  

lemma implication: "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B (\<not>\<^sub>BF \<or>\<^sub>B G)"
  sorry

lemma SoundnessCL5L: "Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X)"
  apply simp
proof -
  assume "\<psi> X \<turnstile>\<^sub>B \<gamma> Y"
  then have "(\<not>\<^sub>B \<gamma> Y) \<and>\<^sub>B \<psi> X \<turnstile>\<^sub>B \<bottom>\<^sub>B"
    by (meson ConjE1 ConjE2 ConjI ImpB MP Notl)
  then show "(\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<not>\<^sub>B \<psi> X"
    using ImpT MP Notr by blast
qed

lemma SoundnessCL5R : "Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y)"
  apply simp
proof -
  assume "(\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<not>\<^sub>B \<psi> X"
  then have "\<psi> X \<and>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<bottom>\<^sub>B"
    by (meson ConjE1 ConjE2 ConjI ImpB MP Notl)
  then show "\<psi> X \<turnstile>\<^sub>B \<gamma> Y"
    by (meson ImpT MP Notnot Notr)
qed



lemma SoundnessCL1L: "Valid(((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z)) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C \<sharp>Y ; Z)"
  apply simp
  by (meson Bot ConjI DisjI1 ImpB ImpT MP Notl implication)

lemma SoundnessCL1R :"Valid(X \<turnstile>\<^sub>C \<sharp>Y ; Z) \<Longrightarrow> Valid (((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z))"
  apply simp
proof -
  have "\<psi> X \<turnstile>\<^sub>B \<bottom>\<^sub>B"
    by (meson ConjI DisjI1 ImpB ImpT MP Notl implication)
  then show "\<psi> X \<and>\<^sub>B \<psi> Y \<turnstile>\<^sub>B \<gamma> Z"
    by (meson Bot ImpB MP)
qed

lemma SoundnessCL3L : "Valid(X \<turnstile>\<^sub>C Y ; Z) \<Longrightarrow> Valid(X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z)"
  apply simp

proof -
  have "\<psi> X \<turnstile>\<^sub>B \<bottom>\<^sub>B"
    by (meson ConjI DisjI1 ImpB ImpT MP Notl implication)
  then show "\<psi> X \<and>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<gamma> Z"
    using Bot ImpB MP by blast
qed

theorem Soundness: "\<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid(X\<turnstile>\<^sub>C Y)"

proof (induction rule:Provable.induct)
case (BotL X)
then show ?case 
  by (simp add: Bot)
next
  case (BotR X)
then show ?case 
  by simp
next
  case (TopL X)
then show ?case 
  by simp
next
case (TopR X)
  then show ?case 
    by (simp add: Top)
next
  case (notL F X)
  then show ?case
    by simp
next
  case (notR X F)
  then show ?case 
    by simp
next
  case (orL F X G)
  then show ?case 
    by (simp add: DisjE)
next
  case (orR X F G)
  then show ?case 
    by simp
next
  case (andL F G X)
  then show ?case 
    by simp
next
  case (andR X F G)
  then show ?case 
    by (simp add: ConjI)
next
  case (impL X F G Y)
  then show ?case 
    by (meson Bot ConjI DisjI1 ImpB ImpT MP Notl Valid.elims(3) implication)
next
  case (impR X F G)
  then show ?case 
    by (simp add: ImpT)
next
  case (nilL X Y)
  then show ?case 
  proof -
    have "\<psi> (\<emptyset>\<^sub>A ;\<^sub>A X) \<turnstile>\<^sub>B \<gamma> Y"
      by (meson Valid.simps nilL.IH)
    then show ?thesis
      by (metis Ax ConjI MP Top Valid.simps \<psi>.simps(2) \<psi>.simps(4))
  qed
next
  case (nilL_sym X Y)
  then show ?case 
    by (metis ConjE2 Consecution.inject MP Valid.elims(2) Valid.elims(3) \<psi>.simps(4))
next
case (nilR X Y)
  then show ?case 
  proof -
    have "\<forall>b. b \<or>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B b"
      using Ax Bot DisjE by presburger
    then show ?thesis
      using MP Valid.simps \<gamma>.simps(2) \<gamma>.simps(4) nilR.IH by presburger
  qed
next
  case (nilR_sym X Y)
  then show ?case 
    by (simp add: DisjI1 MP)
next
  case (AAL W X Y Z)
  then show ?case 
    by (meson Bot ConjI DisjI1 ImpB ImpT MP Notl Valid.elims(3) implication)
next
  case (AAL_sym W X Y Z)
  then show ?case 

    by (meson Bot ConjI DisjI1 ImpB ImpT MP Notl Valid.elims(3) implication)
next
  case (AAR W X Y Z)
  then show ?case 
    by (meson Bot ConjI DisjI1 ImpB ImpT MP Notl Valid.elims(3) implication)
next
  case (AAR_sym W X Y Z)
  then show ?case 
   by (meson Bot ConjI DisjI1 ImpB ImpT MP Notl Valid.elims(3) implication)
next
  case (WkL X Z Y)
  then show ?case 
    by (metis ConjE1 Consecution.inject MP Valid.elims(2) Valid.elims(3) \<psi>.simps(4))
next
  case (WkR X Z Y)
  then show ?case 
    by (simp add: DisjI2 MP)
next
  case (CtrL X Y)
  then show ?case 
    by (metis Ax ConjI MP Valid.simps \<psi>.simps(4))
next
  case (CtrR X Y)
  then show ?case 
    by (metis Ax DisjE MP Valid.simps \<gamma>.simps(4))
next
  case (TopMultL X)
  then show ?case 
    by simp
next
  case (andMultL F G X)
  then show ?case 
    by simp
next
  case (impMultL X F G Y)
  then show ?case 
    by (meson Bot ConjI DisjI1 ImpB ImpT MP Notl Valid.elims(3) implication)
next
  case TopMultR
  then show ?case 
    by (simp add: Ax)
next
  case (andMultR X F Y G)
  then show ?case 
    using ConjIstar by auto
next
  case (impMultR X F G)
  then show ?case
    by (simp add: ImpstarT)
next
case (nilMultL X Y)
then show ?case 
  by (metis Comm MP Topr Valid.simps \<psi>.simps(5) \<psi>.simps(6))
next
case (nilMultL_sym X Y)
then show ?case 
  by (metis Comm Consecution.inject MP Topl Valid.elims(2) Valid.elims(3) \<psi>.simps(5) \<psi>.simps(6))
next
case (MAL W X Y Z)
then show ?case 
  using Assocr MP by fastforce
next
case (MAL_sym W X Y Z)
then show ?case
  using Assocl MP by fastforce
next
  case (cut X F Y)
  then show ?case
  proof -
    have "F \<turnstile>\<^sub>B \<gamma> Y"
      using Valid.simps \<psi>.simps(1) cut.IH(2) by presburger
    then show ?thesis
      by (metis (no_types) MP Valid.simps \<gamma>.simps(1) cut.IH(1))
  qed
qed



section "display proof"



fun ant_part :: "Structure \<Rightarrow> Consecution \<Rightarrow> bool" where
"ant_part Z (X \<turnstile>\<^sub>C Y) = ((pos Z (Inl X)) \<or> (neg Z (Inr Y)))"

fun con_part :: "Structure \<Rightarrow> Consecution \<Rightarrow> bool" where
"con_part Z (X \<turnstile>\<^sub>C Y) = ((neg Z (Inl X)) \<or> (pos Z (Inr Y)))"

lemma display : "ant_part (Inl Z) (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))"
  apply simp
proof-
  assume "ant_part (Inl Z) (X \<turnstile>\<^sub>C Y)"
  have "pos (Inl Z) (Inl X) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))" and "neg (Inl Z) (Inr Y) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))" 
  proof (induction X and Y)
case (formulaA x)
then show ?case sorry
next
  case AddNilA
  then show ?case
    sorry
next
  case (SharpA x)
  then show ?case  sorry
  (*proof -
  assume "X = \<sharp>\<^sub>A x"
    have "(SharpA Y \<turnstile>\<^sub>C x) \<equiv>\<^sub>D (\<sharp>\<^sub>A x \<turnstile>\<^sub>C Y)" 
      by (meson display_symm display_trans positulatesCL5 positulatesCL6)
    from this have "\<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))" 
      using SharpA.prems \<open>X = \<sharp>\<^sub>A x\<close> display_refl pos.cases by blast
    then have "neg (Inl Z) (Inr x) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))" 
      by blast
    then have "pos (Inl Z) (Inl (\<sharp>\<^sub>A x)) \<Longrightarrow> \<exists>W. (\<sharp>\<^sub>A x \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)" 
      using \<open>X = \<sharp>\<^sub>A x\<close> \<open>\<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)\<close> by blast
    then have "(neg (Inl Z) (Inr x) \<Longrightarrow> \<exists>W. (X \<turnstile>\<^sub>C x) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)) \<Longrightarrow> pos (Inl Z) (Inl (\<sharp>\<^sub>A x)) \<Longrightarrow> \<exists>W. (\<sharp>\<^sub>A x \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)" 
      by blast
    oops
  qed(auto)*)
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



end