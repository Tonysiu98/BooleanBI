theory proofs
  imports Main def
begin
section"Soundness and Completeness"

lemma commAnd : "F \<and>\<^sub>B G \<turnstile>\<^sub>B G \<and>\<^sub>B F"
  by (simp add: ConjE1 ConjE2 ConjI)

lemma impTodis:"F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B \<not>\<^sub>BF \<or>\<^sub>B G"
  sorry
    
lemma SoundPostulateCL1 : "Valid((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C \<sharp>Y ; Z)"
  apply simp
  sorry
 
lemma SoundPostulateCL2 : "Valid((X \<turnstile>\<^sub>C \<sharp>Y ; Z)) \<Longrightarrow> Valid (Y ;\<^sub>A X \<turnstile>\<^sub>C Z)"
  apply simp
  sorry

lemma SoundPostulateCL3 : "Valid ((X \<turnstile>\<^sub>C Y ; Z)) \<Longrightarrow> Valid((X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z))"
  apply simp
  sorry

lemma SoundPostulateCL4 : "Valid (X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Z ; Y)"
  apply simp
  sorry

lemma SoundPostulateCL5 : "Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X)"
  apply simp
proof-
  assume "\<psi> X \<turnstile>\<^sub>B \<gamma> Y"
  have "\<gamma>  Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<gamma> Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B" using Ax by simp
  then have "\<gamma> Y \<turnstile>\<^sub>B (\<gamma> Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" using ImpT ImpB MP commAnd by blast
  then have "\<psi> X \<turnstile>\<^sub>B (\<gamma> Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
    using MP \<open>\<psi> X \<turnstile>\<^sub>B \<gamma> Y\<close> by blast
  then have "\<gamma> Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<psi> X \<rightarrow>\<^sub>B \<bottom>\<^sub>B" using ImpT ImpB MP commAnd by blast
  then have "\<gamma> Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<not>\<^sub>B \<psi> X " using Notr MP by blast
  then have "(\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<not>\<^sub>B \<psi> X" using Notl MP by blast
  then show "\<psi> X \<turnstile>\<^sub>B \<gamma> Y \<Longrightarrow> (\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<not>\<^sub>B \<psi> X" by simp
qed

lemma SoundPostulateCL6 : "Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X) \<Longrightarrow> Valid (\<sharp>\<^sub>A(\<sharp>X) \<turnstile>\<^sub>C Y)"
  apply simp
proof -
  assume "(\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<not>\<^sub>B \<psi> X" 
  have "(\<not>\<^sub>B \<psi> X) \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B (\<not>\<^sub>B \<psi> X) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" using Ax by simp 
  then have "(\<not>\<^sub>B \<psi> X) \<turnstile>\<^sub>B ((\<not>\<^sub>B \<psi> X) \<rightarrow>\<^sub>B \<bottom>\<^sub>B) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" using ImpT ImpB commAnd MP by blast
  then have "(\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B ((\<not>\<^sub>B \<psi> X) \<rightarrow>\<^sub>B \<bottom>\<^sub>B) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" using MP \<open>(\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<not>\<^sub>B \<psi> X\<close> by blast
  then have "((\<not>\<^sub>B \<psi> X) \<rightarrow>\<^sub>B \<bottom>\<^sub>B) \<turnstile>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" using ImpT ImpB commAnd MP by blast
  then have "(\<not>\<^sub>B\<not>\<^sub>B \<psi> X) \<turnstile>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" using Notl MP by blast
  then have "(\<not>\<^sub>B\<not>\<^sub>B \<psi> X) \<turnstile>\<^sub>B (\<not>\<^sub>B\<not>\<^sub>B \<gamma> Y)" using Notr MP by blast
  then have "(\<not>\<^sub>B\<not>\<^sub>B \<psi> X) \<turnstile>\<^sub>B \<gamma> Y" using Notnot MP by blast
  then show "(\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<not>\<^sub>B \<psi> X \<Longrightarrow> (\<not>\<^sub>B \<not>\<^sub>B \<psi> X) \<turnstile>\<^sub>B \<gamma> Y" by simp 
qed

lemma SoundPostulateCL7 : "Valid (X ,\<^sub>A Y \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z)"
  apply simp
proof - 
  assume "\<psi> X *\<^sub>B \<psi> Y \<turnstile>\<^sub>B \<gamma> Z" 
  then have "\<psi> X \<turnstile>\<^sub>B \<psi> Y  \<rightarrow>\<^emph>\<^sub>B \<gamma> Z" using ImpstarT by blast
  thus "\<psi> X *\<^sub>B \<psi> Y \<turnstile>\<^sub>B \<gamma> Z \<Longrightarrow> \<psi> X \<turnstile>\<^sub>B \<psi> Y \<rightarrow>\<^emph>\<^sub>B \<gamma> Z" by simp
qed

lemma SoundPostulateCL8 : "Valid (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z) \<Longrightarrow> Valid (Y ,\<^sub>A X \<turnstile>\<^sub>C Z)"
  apply simp 
proof -
  assume "\<psi> X \<turnstile>\<^sub>B \<psi> Y \<rightarrow>\<^emph>\<^sub>B \<gamma> Z"
  then have "\<psi> X *\<^sub>B \<psi> Y \<turnstile>\<^sub>B \<gamma> Z" using ImpstarB by blast
  then have "\<psi> Y *\<^sub>B \<psi> X \<turnstile>\<^sub>B \<gamma> Z" using Comm MP by blast
  thus "\<psi> X \<turnstile>\<^sub>B \<psi> Y \<rightarrow>\<^emph>\<^sub>B \<gamma> Z \<Longrightarrow> \<psi> Y *\<^sub>B \<psi> X \<turnstile>\<^sub>B \<gamma> Z" by simp
qed
 

lemma SoundnessRules: "\<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid(X\<turnstile>\<^sub>C Y)"
 proof (induction rule:Provable.induct)
  case (BotL X)
  then show ?case 
proof-
  have "\<psi> (formulaA \<bottom>\<^sub>B) \<turnstile>\<^sub>B \<gamma> X" 
    by (simp add: Bot)
  thus ?case 
    by auto
qed
next
  case (BotR X)
then show ?case 
  proof - 
    have "\<psi> X \<turnstile>\<^sub>B \<gamma> \<emptyset>" 
      using BotR.IH by auto
    hence " \<psi> X \<turnstile>\<^sub>B \<bottom>\<^sub>B" 
      using Ax  by simp
    thus ?case by simp
  qed
next
  case (TopL X)
then show ?case 
proof-
  have "\<psi> (formulaA \<bottom>\<^sub>B) \<turnstile>\<^sub>B \<gamma> X" 
    by (simp add: Bot)
  thus ?case 
    using TopL.IH by auto
qed
next
  case (TopR X)
then show ?case 
proof-
  have "\<psi> X \<turnstile>\<^sub>B \<gamma> (formula \<top>\<^sub>B)" 
    by (simp add: Top)
  thus ?case by simp
qed
next
  case (notL F X)
  then show ?case
  proof-
    have "(\<not>\<^sub>B \<gamma> (formula F)) \<turnstile>\<^sub>B \<gamma> X" 
      using notL.IH by auto
    hence "(\<not>\<^sub>B F) \<turnstile>\<^sub>B \<gamma> X" using Ax by simp
    thus ?case by simp
    qed
next
  case (notR X F)
  then show ?case 
  proof -
    have "\<psi> X \<turnstile>\<^sub>B \<not>\<^sub>B \<psi> (formulaA F )"
      using notR.IH by auto
    hence "\<psi> X \<turnstile>\<^sub>B \<not>\<^sub>B F" using Ax by simp
    thus ?case by simp
  qed
next
  case (orL F X G)
  then show ?case 
  proof - 
    have "F \<turnstile>\<^sub>B \<gamma> X" and " G \<turnstile>\<^sub>B \<gamma> X"  
      using orL.IH(1) apply auto[1]
      using orL.IH(2) by auto
    hence "F \<or>\<^sub>B G \<turnstile>\<^sub>B \<gamma> X" using DisjE by simp
    thus ?case by simp
  qed
next
  case (orR X F G)
  then show ?case 
  proof -
    have "\<psi> X \<turnstile>\<^sub>B \<gamma> (formula F) \<or>\<^sub>B \<gamma> (formula G)"
      using orR.IH by auto
    hence "\<psi> X \<turnstile>\<^sub>B \<gamma> (formula F) \<or>\<^sub>B \<gamma> (formula G)"
      by blast
      thus ?case
        by simp
    qed
next
  case (andL F G X)
  then show ?case 
  proof -
    have "\<psi> (formulaA F) \<and>\<^sub>B \<psi> (formulaA G) \<turnstile>\<^sub>B \<gamma> X" 
      using andL.IH by auto
    hence  "F \<and>\<^sub>B G \<turnstile>\<^sub>B \<gamma> X" by simp
    thus ?case by simp
  qed
next
  case (andR X F G)
  then show ?case 
  proof - 
    have "\<psi> X \<turnstile>\<^sub>B \<gamma> (formula F)" and "\<psi> X \<turnstile>\<^sub>B \<gamma> (formula G)"  
      using andR.IH(1) apply auto[1]
      using andR.IH(2) by auto
    hence "\<psi> X \<turnstile>\<^sub>B F \<and>\<^sub>B G" using ConjI by simp
    thus ?case by simp
  qed
next
  case (impL X F G Y)
  then show ?case 
  proof -
    have "\<psi> X \<turnstile>\<^sub>B F" and "G \<turnstile>\<^sub>B \<gamma> Y" 
      using impL.IH(1) apply auto[1]
      using impL.IH(2) by auto
    have "(\<psi> X \<rightarrow>\<^sub>B \<gamma> Y)\<turnstile>\<^sub>B ((\<not>\<^sub>B \<psi> X) \<or>\<^sub>B \<gamma> Y)" sorry
    have "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G" using Ax by simp
    then have "F \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B G" using ImpT ImpB MP commAnd by blast
    then have "\<psi> X \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B G" using MP \<open>\<psi> X \<turnstile>\<^sub>B F\<close> by blast
    have "(F \<rightarrow>\<^sub>B G) \<and>\<^sub>B \<psi> X \<turnstile>\<^sub>B \<gamma> Y" using commAnd MP \<open>G \<turnstile>\<^sub>B \<gamma> Y\<close> ImpB \<open>\<psi> X \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B G\<close>
      by blast
    then have "(F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B (\<psi> X \<rightarrow>\<^sub>B \<gamma> Y)" using ImpT by simp
    then have "(F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B (\<not>\<^sub>B \<psi> X) \<or>\<^sub>B \<gamma> Y" using MP \<open>(\<psi> X \<rightarrow>\<^sub>B \<gamma> Y)\<turnstile>\<^sub>B ((\<not>\<^sub>B \<psi> X) \<or>\<^sub>B \<gamma> Y)\<close> by blast
    thus ?case 
      by simp
  qed
next
  case (impR X F G)
  then show ?case 
  proof -
    have "\<psi> X \<and>\<^sub>B F \<turnstile>\<^sub>B G "
      using impR.IH by auto
    then have "\<psi> X \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G" using ImpT by simp
    thus ?case 
      by simp
  qed

next
  case (nilL X Y)
  then show ?case 
  proof -
    have "\<top>\<^sub>B \<and>\<^sub>B \<psi> X \<turnstile>\<^sub>B \<gamma> Y"
      using nilL.IH by auto
    have "\<psi> X \<turnstile>\<^sub>B \<gamma> Y" 
      using Ax ConjI MP Top \<open>\<top>\<^sub>B \<and>\<^sub>B \<psi> X \<turnstile>\<^sub>B \<gamma> Y\<close> by blast
    thus ?case by simp
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
    sorry
next
  case (AAL_sym W X Y Z)
  then show ?case 
    sorry
next 
  case (AAR W X Y Z)
  then show ?case 
    sorry
next
  case (AAR_sym W X Y Z)
  then show ?case 
    sorry
next
  case (WkL X Z Y)
  then show ?case 
  proof -
    have "\<psi> X \<turnstile>\<^sub>B \<gamma> Z" 
      using WkL.IH by auto
    then show ?case 
      using ConjE1 MP by fastforce
  qed
next
  case (WkR X Z Y)
  then show ?case 
  proof - 
    have "\<psi> X \<turnstile>\<^sub>B \<gamma> Z" 
      using WkR.IH by auto
    then show ?case using DisjI2 MP by auto
  qed
next
  case (CtrL X Y)
  then show ?case 
  proof -
    have "\<psi> X \<and>\<^sub>B \<psi> X \<turnstile>\<^sub>B \<gamma> Y" using CtrL.IH by auto
    then have "\<psi> X \<turnstile>\<^sub>B \<gamma> Y" using Ax ConjI MP by blast
    thus ?case by simp
  qed
next
  case (CtrR X Y)
  then show ?case 
  proof -
    have "\<psi> X \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<gamma> Y" using CtrR.IH by auto
    then have "\<psi> X \<turnstile>\<^sub>B \<gamma> Y "
      using Ax DisjE MP by blast
    thus ?case by simp 
  qed
next
  case (TopMultL X)
  then show ?case 
  proof - 
    have "\<top>\<^sup>*\<^sub>B \<turnstile>\<^sub>B \<gamma> X" using TopMultL.IH by auto
    thus ?case by simp
  qed
next
  case (andMultL F G X)
  then show ?case 
  proof -
    have "F *\<^sub>B G \<turnstile>\<^sub>B \<gamma> X" using andMultL.IH by auto
    thus ?case by simp
  qed
next
  case (impMultL X F G Y)
  then show ?case 
    sorry 
next
  case TopMultR
  then show ?case 
  proof - 
    have "\<top>\<^sup>*\<^sub>B \<turnstile>\<^sub>B \<top>\<^sup>*\<^sub>B" using Ax by simp
    thus ?case by auto
  qed
next
  case (andMultR X F Y G)
  then show ?case 
  proof-
    have "\<psi> X \<turnstile>\<^sub>B F" and "\<psi> Y \<turnstile>\<^sub>B G" 
      using andMultR.IH(1) apply auto[1]
      using andMultR.IH(2) by auto
    then have "\<psi> X *\<^sub>B \<psi> Y \<turnstile>\<^sub>B F *\<^sub>B G" 
      using ConjIstar by blast
    thus ?case by simp
  qed
next
  case (impMultR X F G)
  then show ?case
  proof -
    have "\<psi> X *\<^sub>B F \<turnstile>\<^sub>B G" using impMultR.IH by auto
    then have "\<psi> X \<turnstile>\<^sub>B F \<rightarrow>\<^emph>\<^sub>B G" using ImpstarT by blast
    thus ?case by simp
  qed
next
case (nilMultL X Y)
then show ?case 
proof - 
  have "\<top>\<^sup>*\<^sub>B *\<^sub>B \<psi> X \<turnstile>\<^sub>B \<gamma> Y" using nilMultL.IH by auto
  then have "\<psi> X \<turnstile>\<^sub>B \<gamma> Y" 
    using Comm MP Topr by blast
  thus ?case by simp
qed
next
case (nilMultL_sym X Y)
then show ?case 
proof - 
  have "\<psi> X \<turnstile>\<^sub>B \<gamma> Y" using nilMultL_sym.IH by auto
  then have "\<top>\<^sup>*\<^sub>B *\<^sub>B \<psi> X \<turnstile>\<^sub>B \<gamma> Y" 
    using Comm MP Topl by blast
  thus ?case by simp
qed
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
    have "\<psi> X \<turnstile>\<^sub>B F" and "F \<turnstile>\<^sub>B \<gamma> Y" using cut.IH by auto
    then have "\<psi> X \<turnstile>\<^sub>B \<gamma> Y" using MP 
      by blast
    thus ?case by simp
  qed
qed





section "display proof"


fun ant_part :: "Structure \<Rightarrow> Consecution \<Rightarrow> bool" where
"ant_part Z (X \<turnstile>\<^sub>C Y) = ((pos Z (Inl X)) \<or> (neg Z (Inr Y)))"

fun con_part :: "Structure \<Rightarrow> Consecution \<Rightarrow> bool" where
"con_part Z (X \<turnstile>\<^sub>C Y) = ((neg Z (Inl X)) \<or> (pos Z (Inr Y)))"

lemma displayAnt : "ant_part (Inl Z) (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))"
  apply simp
proof-
  have "pos (Inl Z) (Inl X) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))" and "neg (Inl Z) (Inr Y) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))" 
  proof (induction X and Y)
  case (formulaA x)
  then show ?case 
  proof-
    have "pos (Inl Z) (Inl (formulaA x))" 
      by (simp add: formulaA.prems)
    then have "Z = formulaA x" 
      using pos.cases by auto
    thus ?case 
      using display_refl by blast
  qed
next
  case AddNilA
  then show ?case
  proof-
    have "pos (Inl Z) (Inl \<emptyset>\<^sub>A)" 
      by (simp add: AddNilA.prems)
    then have "Z = \<emptyset>\<^sub>A" 
      using pos.cases by fastforce
    thus ?case
      using display_refl by auto
  qed
next
  case (SharpA x)
  then show ?case  
    sorry
next
  case (SemiColonA x1 x2)
  then show ?case sorry
next
  case MultNilA
  then show ?case 
  proof - 
  have "Z = \<oslash>" 
    using MultNilA.prems pos.cases by fastforce
  thus ?case 
    using display_refl by blast
  qed
next
  case (CommaA x1 x2)
  then show ?case sorry
next
  case (formula x)
  then show ?case 
  proof -
    have "Z = \<sharp>\<^sub>A (formula x)" 
      using formula.prems neg.cases by force
    thus ?case 
      using positulatesCL5 by blast
  qed
next
  case AddNil
  then show ?case 
  proof -
    have "Z = \<sharp>\<^sub>A \<emptyset>" 
      using AddNil.prems neg.cases by fastforce
    thus ?case
      using positulatesCL5 by blast
  qed
next
  case (Sharp x)
  then show ?case 
    sorry
next
  case (SemiColon x1 x2)
  then show ?case sorry
next
  case (DotArrow x1 x2)
  then show ?case sorry
qed
  oops

lemma displayCon : "con_part (Inr Z) (X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (W \<turnstile>\<^sub>C Z))" 
  apply simp
proof -
  have "neg (Inr Z) (Inl X) \<Longrightarrow> \<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (W \<turnstile>\<^sub>C Z)" and "pos (Inr Z) (Inr Y) \<Longrightarrow> \<exists>W. (X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (W \<turnstile>\<^sub>C Z)"
  proof(induction X and Y)
case (formulaA x)
  then show ?case 
  proof -
    have "neg (Inr Z) (Inl (formulaA x))" 
      by (simp add: formulaA.prems)
    then have "Z = \<sharp>(formulaA x)" 
      using neg.cases by fastforce
    thus ?case 
      using positulatesCL5 by blast
  qed
next
  case AddNilA
  then show ?case 
  proof-
have "neg (Inr Z) (Inl \<emptyset>\<^sub>A)" 
  by (simp add: AddNilA.prems)
    then have "Z = \<sharp>\<emptyset>\<^sub>A" 
      using neg.cases by fastforce
    thus ?case 
      using positulatesCL5 by blast
  qed
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
  oops
end