theory soundness
  imports Main def
begin
section"Soundness"

section"shortcut lemmas"

lemma assocAnd1 : "F \<and>\<^sub>B (G \<and>\<^sub>B H) \<turnstile>\<^sub>B (F \<and>\<^sub>B G) \<and>\<^sub>B H"
  by (meson ConjE1 ConjE2 ConjI MP)

lemma assocAnd2 : "(F \<and>\<^sub>B G) \<and>\<^sub>B H \<turnstile>\<^sub>B F \<and>\<^sub>B (G \<and>\<^sub>B H)"
  by (meson ConjE1 ConjE2 ConjI MP)

lemma assocOr1 : "F \<or>\<^sub>B (G \<or>\<^sub>B H) \<turnstile>\<^sub>B (F \<or>\<^sub>B G) \<or>\<^sub>B H" 
  by (meson DisjE DisjI1 DisjI2 MP)

lemma assocOr2 : "(F \<or>\<^sub>B G) \<or>\<^sub>B H \<turnstile>\<^sub>B F \<or>\<^sub>B (G \<or>\<^sub>B H)" 
  by (meson DisjE DisjI1 DisjI2 MP)

lemma NotnotR : "F \<turnstile>\<^sub>B \<not>\<^sub>B \<not>\<^sub>B F"
  by (meson ConjE1 ConjE2 ConjI ImpB ImpT MP Notl Notr)

lemma commOR :"F \<or>\<^sub>B G \<turnstile>\<^sub>B G \<or>\<^sub>B F" 
  by (simp add: DisjE DisjI1 DisjI2)

lemma commAnd : "F \<and>\<^sub>B G \<turnstile>\<^sub>B G \<and>\<^sub>B F"
  by (simp add: ConjE1 ConjE2 ConjI)

lemma disToimp : "(\<not>\<^sub>BF) \<or>\<^sub>B G \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G"
proof
  show "(\<not>\<^sub>B F) \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G" 
    using Bot ImpB ImpT MP Notl by blast
  show  "G \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G"
    by (simp add: ConjE1 ImpT) 
qed

lemma impTodis:"F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B(\<not>\<^sub>BF) \<or>\<^sub>B G"
proof-
  have "\<top>\<^sub>B \<turnstile>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)"
  proof-
    have "F \<turnstile>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F))" using DisjI1 by simp
    then have "F \<turnstile>\<^sub>B (\<not>\<^sub>B \<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F)))" using NotnotR MP by blast
    then have "F \<turnstile>\<^sub>B  (\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<rightarrow>\<^sub>B \<bottom>\<^sub>B"  using MP Notl by blast
    then have "(\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<turnstile>\<^sub>B  F \<rightarrow>\<^sub>B \<bottom>\<^sub>B" using ImpB ImpT MP commAnd by blast
    then have "(\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<turnstile>\<^sub>B (\<not>\<^sub>B F)" using MP Notr by blast
    have "(\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<turnstile>\<^sub>B F" by (meson ConjI DisjI1 DisjI2 ImpB MP \<open>(\<not>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B \<not>\<^sub>B F\<close> disToimp)
    have "(\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<turnstile>\<^sub>B F \<and>\<^sub>B (\<not>\<^sub>B F)" by (simp add: ConjI \<open>(\<not>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B F\<close> \<open>(\<not>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B \<not>\<^sub>B F\<close>)
    have "F \<and>\<^sub>B (\<not>\<^sub>B F) \<turnstile>\<^sub>B \<bottom>\<^sub>B" using ImpB MP Notl commAnd by blast
    then have "(\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<turnstile>\<^sub>B \<bottom>\<^sub>B " 
      using MP \<open>(\<not>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B F \<and>\<^sub>B (\<not>\<^sub>B F)\<close> by blast
    then have "(\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<turnstile>\<^sub>B \<top>\<^sub>B \<rightarrow>\<^sub>B \<bottom>\<^sub>B" using Bot MP by blast
    then have  "(\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<and>\<^sub>B \<top>\<^sub>B \<turnstile>\<^sub>B \<bottom>\<^sub>B" 
      by (simp add: ImpB)
    then have  "\<top>\<^sub>B \<turnstile>\<^sub>B (\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F)))\<rightarrow>\<^sub>B \<bottom>\<^sub>B " 
      using ImpT MP commAnd by blast
    then show "\<top>\<^sub>B \<turnstile>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)"
      using MP Notnot Notr by blast
  qed
  have "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B \<top>\<^sub>B" using Top by simp
  then have "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)" 
    using MP \<open>\<top>\<^sub>B \<turnstile>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)\<close> by blast
  have "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G" using Ax by simp
  then have "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<and>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F))" 
    using ConjI \<open>F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)\<close> by blast
  have "(F \<rightarrow>\<^sub>B G) \<and>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<or>\<^sub>B G"
  proof-
    have "(\<not>\<^sub>B F) \<and>\<^sub>B (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B (\<not>\<^sub>B F)" and  "(\<not>\<^sub>B F) \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<or>\<^sub>B G"
       apply (simp add: ConjE1)
      by (simp add: DisjI1)
   then have "(\<not>\<^sub>B F) \<and>\<^sub>B (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<or>\<^sub>B G" 
     using MP by blast
   then have "(\<not>\<^sub>B F) \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B ((\<not>\<^sub>B F) \<or>\<^sub>B G)" 
     by (simp add: ImpT)
   have "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G" using Ax by simp
   then have "F \<and>\<^sub>B (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B G" 
     using ImpB MP commAnd by blast
   have "G \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<or>\<^sub>B G" 
     by (simp add: DisjI2)
   then have "F \<and>\<^sub>B (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<or>\<^sub>B G" 
     using MP \<open>F \<and>\<^sub>B (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B G\<close> by blast
   then have "F \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B ((\<not>\<^sub>B F) \<or>\<^sub>B G)"
     by (simp add: ImpT)
   have "F \<or>\<^sub>B (\<not>\<^sub>B F) \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B ((\<not>\<^sub>B F) \<or>\<^sub>B G)" 
     using \<open>F \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B ((\<not>\<^sub>B F) \<or>\<^sub>B G)\<close> \<open>(\<not>\<^sub>B F) \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B ((\<not>\<^sub>B F) \<or>\<^sub>B G)\<close> DisjE by blast
   then have "(F \<or>\<^sub>B (\<not>\<^sub>B F)) \<and>\<^sub>B (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<or>\<^sub>B G" 
     using ImpB by blast
   then show "(F \<rightarrow>\<^sub>B G) \<and>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<or>\<^sub>B G"
     using MP commAnd by blast
 qed
  show "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B(\<not>\<^sub>BF) \<or>\<^sub>B G" 
    using MP \<open>(F \<rightarrow>\<^sub>B G) \<and>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<or>\<^sub>B G\<close> \<open>F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<and>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F))\<close> by blast
qed
  
     
section"Soundness for Postulates"
    
lemma SoundPostulateCL1 : "Valid((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C \<sharp>Y ; Z)"
  apply simp
proof-
  assume "\<psi> X \<and>\<^sub>B \<psi> Y \<turnstile>\<^sub>B \<gamma> Z" 
  then have "\<psi> X \<turnstile>\<^sub>B \<psi> Y \<rightarrow>\<^sub>B \<gamma> Z" using ImpT by blast
  have "\<psi> Y \<rightarrow>\<^sub>B \<gamma> Z \<turnstile>\<^sub>B (\<not>\<^sub>B \<psi> Y) \<or>\<^sub>B \<gamma> Z" 
    by (simp add: impTodis)
  then show "\<psi> X \<and>\<^sub>B \<psi> Y \<turnstile>\<^sub>B \<gamma> Z \<Longrightarrow> \<psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B \<psi> Y) \<or>\<^sub>B \<gamma> Z" 
    using MP \<open>\<psi> X \<turnstile>\<^sub>B \<psi> Y \<rightarrow>\<^sub>B \<gamma> Z\<close> by blast
qed

lemma SoundPostulateCL1R: "Valid (X \<turnstile>\<^sub>C \<sharp>Y ; Z) \<Longrightarrow> Valid ((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z)" 
  apply simp
  using ImpB MP disToimp by blast

lemma SoundPostulateCL2 : "Valid((X \<turnstile>\<^sub>C \<sharp>Y ; Z)) \<Longrightarrow> Valid (Y ;\<^sub>A X \<turnstile>\<^sub>C Z)"
  apply simp
proof - 
  assume "\<psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B \<psi> Y) \<or>\<^sub>B \<gamma> Z"
  have " (\<not>\<^sub>B \<psi> Y) \<or>\<^sub>B \<gamma> Z \<turnstile>\<^sub>B  \<psi> Y \<rightarrow>\<^sub>B \<gamma> Z" using disToimp by simp
  then show "\<psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B \<psi> Y) \<or>\<^sub>B \<gamma> Z \<Longrightarrow> \<psi> Y \<and>\<^sub>B \<psi> X \<turnstile>\<^sub>B \<gamma> Z" using MP commAnd ImpB by blast
qed

lemma SoundPostulateCL2R :"Valid(Y ;\<^sub>A X \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid((X \<turnstile>\<^sub>C \<sharp>Y ; Z))"
  apply simp
  using ImpT MP commAnd impTodis by blast

lemma SoundPostulateCL3 : "Valid ((X \<turnstile>\<^sub>C Y ; Z)) \<Longrightarrow> Valid((X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z))"
  apply simp
proof -
  assume "\<psi> X \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<gamma> Z"
  have "\<gamma> Y \<or>\<^sub>B \<gamma> Z \<turnstile>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<rightarrow>\<^sub>B \<gamma> Z" 
    by (meson DisjE DisjI1 DisjI2 MP NotnotR disToimp)
  then show "\<psi> X \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<gamma> Z \<Longrightarrow> \<psi> X \<and>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<gamma> Z"
    using ImpB MP by blast
qed

lemma SoundPostulateCL3R: "Valid((X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z)) \<Longrightarrow> Valid ((X \<turnstile>\<^sub>C Y ; Z))"
  apply simp
proof-
  assume "\<psi> X \<and>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<gamma> Z"
  then have "\<psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<rightarrow>\<^sub>B \<gamma> Z" 
    by (simp add: ImpT)
  then have "\<psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B (\<not>\<^sub>B \<gamma> Y)) \<or>\<^sub>B \<gamma> Z " 
    using MP impTodis by blast
  have "(\<not>\<^sub>B (\<not>\<^sub>B \<gamma> Y)) \<or>\<^sub>B \<gamma> Z  \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<gamma> Z" 
    using DisjE DisjI1 DisjI2 MP Notnot by blast
  show "\<psi> X \<and>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<gamma> Z \<Longrightarrow> \<psi> X \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<gamma> Z " 
    using MP \<open>(\<not>\<^sub>B \<not>\<^sub>B \<gamma> Y) \<or>\<^sub>B \<gamma> Z \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<gamma> Z\<close> \<open>\<psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B \<not>\<^sub>B \<gamma> Y) \<or>\<^sub>B \<gamma> Z\<close> by blast
qed

lemma SoundPostulateCL4 : "Valid (X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Z ; Y)"
  apply simp
proof- 
  assume "\<psi> X \<and>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<gamma> Z" 
  then have "\<psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<rightarrow>\<^sub>B \<gamma> Z"
    by (simp add: ImpT)
  have "(\<not>\<^sub>B \<gamma> Y) \<rightarrow>\<^sub>B \<gamma> Z \<turnstile>\<^sub>B (\<not>\<^sub>B \<not>\<^sub>B \<gamma> Y) \<or>\<^sub>B \<gamma> Z" using impTodis by simp
  then have "(\<not>\<^sub>B \<not>\<^sub>B \<gamma> Y) \<or>\<^sub>B \<gamma> Z \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<gamma> Z" 
    by (meson DisjE DisjI2 MP Notnot commOR)
  then show "\<psi> X \<and>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<gamma> Z \<Longrightarrow> \<psi> X \<turnstile>\<^sub>B \<gamma> Z \<or>\<^sub>B \<gamma> Y" 
    by (meson MP \<open>(\<not>\<^sub>B \<gamma> Y) \<rightarrow>\<^sub>B \<gamma> Z \<turnstile>\<^sub>B (\<not>\<^sub>B \<not>\<^sub>B \<gamma> Y) \<or>\<^sub>B \<gamma> Z\<close> \<open>\<psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<rightarrow>\<^sub>B \<gamma> Z\<close> commOR)
qed

lemma SoundPostulateCL4R : "Valid (X \<turnstile>\<^sub>C Z ; Y) \<Longrightarrow> Valid (X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z)"
  apply simp
proof -
  assume "\<psi> X \<turnstile>\<^sub>B \<gamma> Z \<or>\<^sub>B \<gamma> Y"
  have "\<gamma> Z \<or>\<^sub>B \<gamma> Y \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<gamma> Z" 
    by (simp add: commOR)
  then have "\<psi> X \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<gamma> Z"
    using MP \<open>\<psi> X \<turnstile>\<^sub>B \<gamma> Z \<or>\<^sub>B \<gamma> Y\<close> by blast
   have "\<gamma> Y \<or>\<^sub>B \<gamma> Z \<turnstile>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<rightarrow>\<^sub>B \<gamma> Z"
     by (meson DisjE DisjI1 DisjI2 MP NotnotR disToimp)
   then have "\<psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<rightarrow>\<^sub>B \<gamma> Z" 
     using MP \<open>\<psi> X \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<gamma> Z\<close> by blast
   show "\<psi> X \<turnstile>\<^sub>B \<gamma> Z \<or>\<^sub>B \<gamma> Y \<Longrightarrow> \<psi> X \<and>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<turnstile>\<^sub>B \<gamma> Z" 
     by (simp add: ImpB \<open>\<psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B \<gamma> Y) \<rightarrow>\<^sub>B \<gamma> Z\<close>)
 qed

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

lemma SoundPostulateCL5R : "Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y)"
  apply simp
  by (meson ImpB ImpT MP Notl Notnot Notr commAnd)

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


lemma SoundPostulateCL6R : "Valid (\<sharp>\<^sub>A(\<sharp>X) \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X)"
  using SoundPostulateCL5 SoundPostulateCL5R SoundPostulateCL6 by blast

lemma SoundPostulateCL7 : "Valid (X ,\<^sub>A Y \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z)"
  apply simp
proof - 
  assume "\<psi> X *\<^sub>B \<psi> Y \<turnstile>\<^sub>B \<gamma> Z" 
  then have "\<psi> X \<turnstile>\<^sub>B \<psi> Y  \<rightarrow>\<^emph>\<^sub>B \<gamma> Z" using ImpstarT by blast
  thus "\<psi> X *\<^sub>B \<psi> Y \<turnstile>\<^sub>B \<gamma> Z \<Longrightarrow> \<psi> X \<turnstile>\<^sub>B \<psi> Y \<rightarrow>\<^emph>\<^sub>B \<gamma> Z" by simp
qed

lemma SoundPostulateCL7R : "Valid (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z) \<Longrightarrow> Valid (X ,\<^sub>A Y \<turnstile>\<^sub>C Z)"
  by (simp add: ImpstarB)

lemma SoundPostulateCL8 : "Valid (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z) \<Longrightarrow> Valid (Y ,\<^sub>A X \<turnstile>\<^sub>C Z)"
  apply simp 
proof -
  assume "\<psi> X \<turnstile>\<^sub>B \<psi> Y \<rightarrow>\<^emph>\<^sub>B \<gamma> Z"
  then have "\<psi> X *\<^sub>B \<psi> Y \<turnstile>\<^sub>B \<gamma> Z" using ImpstarB by blast
  then have "\<psi> Y *\<^sub>B \<psi> X \<turnstile>\<^sub>B \<gamma> Z" using Comm MP by blast
  thus "\<psi> X \<turnstile>\<^sub>B \<psi> Y \<rightarrow>\<^emph>\<^sub>B \<gamma> Z \<Longrightarrow> \<psi> Y *\<^sub>B \<psi> X \<turnstile>\<^sub>B \<gamma> Z" by simp
qed

lemma SoundPostulateCL8R : "Valid (Y ,\<^sub>A X \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z)"
  using SoundPostulateCL7 SoundPostulateCL8 by blast



section"Soundness for logical and structural rules"

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
      by simp
    thus ?case by simp
  qed
next
  case (TopL X)
then show ?case 
proof-
  have "\<psi> \<emptyset>\<^sub>A \<turnstile>\<^sub>B \<gamma> X" 
    using TopL.IH Valid.simps by blast
  thus ?case by simp
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
    hence "(\<not>\<^sub>B F) \<turnstile>\<^sub>B \<gamma> X"  by simp
    thus ?case by simp
    qed
next
  case (notR X F)
  then show ?case 
  proof -
    have "\<psi> X \<turnstile>\<^sub>B \<not>\<^sub>B \<psi> (formulaA F )"
      using notR.IH by auto
    hence "\<psi> X \<turnstile>\<^sub>B \<not>\<^sub>B F"  by simp
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
    have "(\<psi> X \<rightarrow>\<^sub>B \<gamma> Y)\<turnstile>\<^sub>B (\<not>\<^sub>B \<psi> X) \<or>\<^sub>B \<gamma> Y" 
      by (simp add: impTodis)
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
    using ConjE2 MP by fastforce
next
case (nilR X Y)
  then show ?case 
  proof-
    have "\<psi> X \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<bottom>\<^sub>B" using nilR.IH by auto
    have "\<gamma> Y \<turnstile>\<^sub>B \<gamma> Y" using Ax by simp
    have "\<bottom>\<^sub>B \<turnstile>\<^sub>B \<gamma> Y" using Bot by simp
    then have "\<gamma> Y \<or>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<gamma> Y" using \<open>\<gamma> Y \<turnstile>\<^sub>B \<gamma> Y\<close> DisjE by simp
    have  " \<psi> X \<turnstile>\<^sub>B \<gamma> Y" using \<open>\<psi> X \<turnstile>\<^sub>B \<gamma> Y \<or>\<^sub>B \<bottom>\<^sub>B\<close> \<open>\<gamma> Y \<or>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<gamma> Y\<close> MP by blast
    thus ?case by simp
  qed
next
  case (nilR_sym X Y)
  then show ?case 
    by (simp add: DisjI1 MP)
next
  case (AAL W X Y Z)
  then show ?case apply simp
    using MP assocAnd2 by blast
next
  case (AAL_sym W X Y Z)
  then show ?case 
    using MP assocAnd1 by fastforce
next 
  case (AAR W X Y Z)
  then show ?case apply simp
    using MP assocOr2 by blast
next
  case (AAR_sym W X Y Z)
  then show ?case 
    by (simp add: MP assocOr1)
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
  then show ?case apply simp
  proof -
    have "\<psi> X \<turnstile>\<^sub>B F" using impMultL.IH by auto
    have "F \<rightarrow>\<^emph>\<^sub>B G \<turnstile>\<^sub>B F \<rightarrow>\<^emph>\<^sub>B G " using Ax by simp 
    then have "F \<turnstile>\<^sub>B (F \<rightarrow>\<^emph>\<^sub>B G) \<rightarrow>\<^emph>\<^sub>B G" 
      using Comm ImpstarB ImpstarT MP by blast
    then have "\<psi> X \<turnstile>\<^sub>B (F \<rightarrow>\<^emph>\<^sub>B G) \<rightarrow>\<^emph>\<^sub>B G" using \<open>\<psi> X \<turnstile>\<^sub>B F\<close> MP 
      by blast
    then have "\<psi> X *\<^sub>B (F \<rightarrow>\<^emph>\<^sub>B G) \<turnstile>\<^sub>B G" 
      by (simp add: ImpstarB)
    have "G \<turnstile>\<^sub>B \<gamma> Y" using impMultL.IH by auto
    then have "\<psi> X *\<^sub>B (F \<rightarrow>\<^emph>\<^sub>B G) \<turnstile>\<^sub>B \<gamma> Y"  using  \<open>\<psi> X *\<^sub>B (F \<rightarrow>\<^emph>\<^sub>B G) \<turnstile>\<^sub>B G\<close> MP by blast
    then have "F \<rightarrow>\<^emph>\<^sub>B G \<turnstile>\<^sub>B \<psi> X \<rightarrow>\<^emph>\<^sub>B \<gamma> Y" 
      using Comm ImpstarT MP by blast
    then show " \<psi> X \<turnstile>\<^sub>B F \<Longrightarrow> G \<turnstile>\<^sub>B \<gamma> Y \<Longrightarrow> F \<rightarrow>\<^emph>\<^sub>B G \<turnstile>\<^sub>B \<psi> X \<rightarrow>\<^emph>\<^sub>B \<gamma> Y" 
      by blast
  qed
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
next 
  case (equiv X' Y' X Y)
  then show ?case 
  proof(induction rule: displayEquiv.induct)
    case (positulatesCL1 X Y Z)
    then show ?case sorry
  next
    case (positulatesCL2 X Y Z)
    then show ?case sorry
next
case (positulatesCL3 X Y Z)
  then show ?case sorry
next
  case (positulatesCL4 X Y Z)
  then show ?case sorry
next
  case (positulatesCL5 X Y)
  then show ?case sorry
next
  case (positulatesCL6 Y X)
  then show ?case sorry
next
  case (positulatesCL7 X Y Z)
  then show ?case sorry
next
  case (positulatesCL8 X Y Z)
  then show ?case sorry
next
  case (display_refl C)
  then show ?case 
    by auto
next
  case (display_symm C C')
  then show ?case sorry

next
  case (display_trans C C' C'')
  then show ?case 
    by (metis Provable.equiv Valid.cases)
qed
next 
  case (id atom)
  then show ?case 
    by (simp add: Ax)
qed


end