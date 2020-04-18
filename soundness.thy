theory soundness
  imports Main def
begin
section"Soundness"

section"shortcut lemmas"

lemma commOR :"F \<or>\<^sub>B G \<turnstile>\<^sub>B G \<or>\<^sub>B F" 
proof-
  have "F \<turnstile>\<^sub>B G \<or>\<^sub>B F" using DisjI2 by simp
  have "G \<turnstile>\<^sub>B G \<or>\<^sub>B F" using DisjI1 by simp

  note\<open>F \<turnstile>\<^sub>B G \<or>\<^sub>B F\<close>\<open>G \<turnstile>\<^sub>B G \<or>\<^sub>B F\<close>
  then show ?thesis using DisjE by simp
qed

lemma commAnd : "F \<and>\<^sub>B G \<turnstile>\<^sub>B G \<and>\<^sub>B F"
proof-
  have "F \<and>\<^sub>B G \<turnstile>\<^sub>B G" using ConjE2 by simp
  have "F \<and>\<^sub>B G \<turnstile>\<^sub>B F" using ConjE1 by simp

  note\<open>F \<and>\<^sub>B G \<turnstile>\<^sub>B G\<close>\<open>F \<and>\<^sub>B G \<turnstile>\<^sub>B F\<close>
  then show ?thesis using ConjI by simp
qed

lemma assocAnd1 : "F \<and>\<^sub>B (G \<and>\<^sub>B H) \<turnstile>\<^sub>B (F \<and>\<^sub>B G) \<and>\<^sub>B H"
proof-
  have "F \<and>\<^sub>B (G \<and>\<^sub>B H) \<turnstile>\<^sub>B F \<and>\<^sub>B G" 
    using ConjE1 ConjE2 ConjI MP by blast
  have "F \<and>\<^sub>B (G \<and>\<^sub>B H) \<turnstile>\<^sub>B H" 
    using ConjE1 ConjE2 ConjI MP by blast
  note\<open>F \<and>\<^sub>B (G \<and>\<^sub>B H) \<turnstile>\<^sub>B F \<and>\<^sub>B G\<close>\<open>F \<and>\<^sub>B (G \<and>\<^sub>B H) \<turnstile>\<^sub>B H\<close>
  then show ?thesis using ConjI by simp
qed

lemma assocAnd2 : "(F \<and>\<^sub>B G) \<and>\<^sub>B H \<turnstile>\<^sub>B F \<and>\<^sub>B (G \<and>\<^sub>B H)"
proof-
  have "(F \<and>\<^sub>B G) \<and>\<^sub>B H \<turnstile>\<^sub>B F" 
    using ConjE1 MP by blast
  have "(F \<and>\<^sub>B G) \<and>\<^sub>B H \<turnstile>\<^sub>B G \<and>\<^sub>B H"
  proof-
    have "(F \<and>\<^sub>B G) \<and>\<^sub>B H \<turnstile>\<^sub>B G"
      using ConjE1 ConjE2 MP by blast
    have "(F \<and>\<^sub>B G) \<and>\<^sub>B H \<turnstile>\<^sub>B H"
      using ConjE2 by simp
    note\<open>(F \<and>\<^sub>B G) \<and>\<^sub>B H \<turnstile>\<^sub>B G\<close>\<open>(F \<and>\<^sub>B G) \<and>\<^sub>B H \<turnstile>\<^sub>B H\<close>
    then show ?thesis 
      using ConjI by simp
  qed

  note\<open>(F \<and>\<^sub>B G) \<and>\<^sub>B H \<turnstile>\<^sub>B F\<close>\<open>(F \<and>\<^sub>B G) \<and>\<^sub>B H \<turnstile>\<^sub>B G \<and>\<^sub>B H\<close>
   then show ?thesis
     using ConjI by simp
qed

lemma assocOr1 : "F \<or>\<^sub>B (G \<or>\<^sub>B H) \<turnstile>\<^sub>B (F \<or>\<^sub>B G) \<or>\<^sub>B H" 
proof-
  have"F \<turnstile>\<^sub>B (F \<or>\<^sub>B G) \<or>\<^sub>B H"
    using DisjI1 MP by blast
  have "G \<or>\<^sub>B H \<turnstile>\<^sub>B (F \<or>\<^sub>B G) \<or>\<^sub>B H" 
    using DisjE DisjI1 DisjI2 MP by blast

  note\<open>F \<turnstile>\<^sub>B (F \<or>\<^sub>B G) \<or>\<^sub>B H\<close>\<open>G \<or>\<^sub>B H \<turnstile>\<^sub>B (F \<or>\<^sub>B G) \<or>\<^sub>B H\<close>
  then show ?thesis 
    using DisjE by simp
qed

lemma assocOr2 : "(F \<or>\<^sub>B G) \<or>\<^sub>B H \<turnstile>\<^sub>B F \<or>\<^sub>B (G \<or>\<^sub>B H)" 
proof-
  have "F \<or>\<^sub>B G \<turnstile>\<^sub>B F \<or>\<^sub>B (G \<or>\<^sub>B H)" 
    using DisjE DisjI1 DisjI2 MP by blast
  have "H \<turnstile>\<^sub>B F \<or>\<^sub>B (G \<or>\<^sub>B H)" 
    using DisjI2 MP by blast

  note\<open>F \<or>\<^sub>B G \<turnstile>\<^sub>B F \<or>\<^sub>B (G \<or>\<^sub>B H)\<close>\<open>H \<turnstile>\<^sub>B F \<or>\<^sub>B (G \<or>\<^sub>B H)\<close>
  then show ?thesis
    using DisjE by simp
qed

lemma reverseNot1: "(\<not>\<^sub>B F) \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B F" 
proof-
  have"(\<not>\<^sub>B F) \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<not>\<^sub>B (\<not>\<^sub>B F)" 
    using Notr by simp
  have "\<not>\<^sub>B (\<not>\<^sub>B F) \<turnstile>\<^sub>B F" 
    using Notnot by simp
 
  note\<open>(\<not>\<^sub>B F) \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<not>\<^sub>B (\<not>\<^sub>B F)\<close>\<open>\<not>\<^sub>B (\<not>\<^sub>B F) \<turnstile>\<^sub>B F\<close>
  then show ?thesis
    using MP by blast
qed

lemma reverseNot2: "F \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<rightarrow>\<^sub>B \<bottom>\<^sub>B"
proof-
  have"(\<not>\<^sub>B F) \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
    using Notl by simp
  then have "(\<not>\<^sub>B F) \<and>\<^sub>B F \<turnstile>\<^sub>B \<bottom>\<^sub>B" 
    using ImpB by simp
  then have "F \<and>\<^sub>B (\<not>\<^sub>B F) \<turnstile>\<^sub>B \<bottom>\<^sub>B"
    using MP commAnd by blast
  then show ?thesis 
    using ImpT by simp
qed
  
lemma NotnotR : "F \<turnstile>\<^sub>B \<not>\<^sub>B (\<not>\<^sub>B F)"
proof-
  have"(\<not>\<^sub>B F) \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<not>\<^sub>B (\<not>\<^sub>B F)" 
    using Notr by simp
  have"F \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
    using reverseNot2 by simp

  note\<open>(\<not>\<^sub>B F) \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<not>\<^sub>B (\<not>\<^sub>B F)\<close>\<open>F \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<rightarrow>\<^sub>B \<bottom>\<^sub>B\<close>
  then show ?thesis using MP by blast
qed

lemma disToimp : "(\<not>\<^sub>BF) \<or>\<^sub>B G \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G"
proof
  have "(\<not>\<^sub>B F) \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B \<bottom>\<^sub>B" using Notl by simp 
  then have "(\<not>\<^sub>B F) \<and>\<^sub>B F \<turnstile>\<^sub>B \<bottom>\<^sub>B" using ImpB by simp
  have "\<bottom>\<^sub>B \<turnstile>\<^sub>B G" using Bot by simp
  
  note\<open>(\<not>\<^sub>B F) \<and>\<^sub>B F \<turnstile>\<^sub>B \<bottom>\<^sub>B\<close>\<open>\<bottom>\<^sub>B \<turnstile>\<^sub>B G\<close>
  then have "(\<not>\<^sub>B F) \<and>\<^sub>B F  \<turnstile>\<^sub>B G" using MP by blast
  then show "(\<not>\<^sub>B F) \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G"  
    using ImpT  by blast

  show  "G \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G"
    by (simp add: ConjE1 ImpT) 
qed

lemma impTodis: "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B(\<not>\<^sub>BF) \<or>\<^sub>B G"
proof-
  have"\<not>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B F \<and>\<^sub>B (\<not>\<^sub>B F)" 
  proof-
    have "F \<turnstile>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)" using DisjI1 by simp
    then have "F \<turnstile>\<^sub>B  (\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
      using MP reverseNot2 by blast
    then have "(\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<turnstile>\<^sub>B  F \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
      using ImpB ImpT MP commAnd by blast
    then have "\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B (\<not>\<^sub>B F)" 
      using MP Notr by blast

    have"(\<not>\<^sub>B F) \<turnstile>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)"
      using DisjI2 by blast
    then have "(\<not>\<^sub>B F) \<turnstile>\<^sub>B (\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
      using MP reverseNot2 by blast
    then have "(\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
      using ImpB ImpT MP commAnd by blast
    then have "\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B F" 
      using MP reverseNot1 by blast

    note\<open>\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B F\<close>\<open>(\<not>\<^sub>B(F \<or>\<^sub>B (\<not>\<^sub>B F))) \<turnstile>\<^sub>B (\<not>\<^sub>B F)\<close> 
    then show ?thesis 
      using ConjI by simp
  qed

  have"\<top>\<^sub>B \<turnstile>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)"
  proof-
    have "F \<turnstile>\<^sub>B (\<not>\<^sub>B F) \<rightarrow>\<^sub>B \<bottom>\<^sub>B"
      using  reverseNot2 by simp
    then have "F \<and>\<^sub>B (\<not>\<^sub>B F) \<turnstile>\<^sub>B \<bottom>\<^sub>B"
      using ImpB by simp
    note\<open>\<not>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B F \<and>\<^sub>B (\<not>\<^sub>B F)\<close>\<open>F \<and>\<^sub>B (\<not>\<^sub>B F) \<turnstile>\<^sub>B \<bottom>\<^sub>B\<close>
    then have "\<not>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B \<bottom>\<^sub>B"
      using MP by blast
    have "\<bottom>\<^sub>B \<turnstile>\<^sub>B \<top>\<^sub>B \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
      using Bot by simp

    note\<open>\<not>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B \<bottom>\<^sub>B\<close>\<open>\<bottom>\<^sub>B \<turnstile>\<^sub>B \<top>\<^sub>B \<rightarrow>\<^sub>B \<bottom>\<^sub>B\<close>
    then have "\<not>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F)) \<turnstile>\<^sub>B \<top>\<^sub>B \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
      using MP by blast
    then have "\<not>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F)) \<and>\<^sub>B \<top>\<^sub>B  \<turnstile>\<^sub>B \<bottom>\<^sub>B" 
      using ImpB by blast
    then have "\<top>\<^sub>B  \<turnstile>\<^sub>B \<not>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F)) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
      using ImpT MP commAnd by blast
    then have "\<top>\<^sub>B \<turnstile>\<^sub>B \<not>\<^sub>B (\<not>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F)))" 
      using MP Notr by blast
    then show ?thesis
      using MP Notnot by blast
  qed

  have "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B \<top>\<^sub>B" 
    using Top by simp
  note\<open>F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B \<top>\<^sub>B\<close>\<open>\<top>\<^sub>B \<turnstile>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)\<close>
  then have "F \<rightarrow>\<^sub>B G  \<turnstile>\<^sub>B F \<or>\<^sub>B (\<not>\<^sub>B F)" 
    using MP by blast
  then have "F \<rightarrow>\<^sub>B G  \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<and>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F))" 
    using Ax ConjI by blast


  have "F \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B (\<not>\<^sub>B F \<or>\<^sub>B G)"
  proof-
    have "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G"
      using Ax by simp
    then have "F \<and>\<^sub>B (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B G" 
      using ImpB MP commAnd by blast
    then show ?thesis 
      using DisjI2 ImpT MP by blast
  qed

  have "\<not>\<^sub>B F \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B (\<not>\<^sub>B F \<or>\<^sub>B G)"
  proof-
    have "\<not>\<^sub>B F \<and>\<^sub>B (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B \<not>\<^sub>B F"
      using ConjE1 by simp
    have "\<not>\<^sub>B F \<turnstile>\<^sub>B \<not>\<^sub>B F  \<or>\<^sub>B G" 
      using DisjI1 by simp
    note\<open>\<not>\<^sub>B F \<and>\<^sub>B (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B \<not>\<^sub>B F\<close>\<open>\<not>\<^sub>B F \<turnstile>\<^sub>B \<not>\<^sub>B F  \<or>\<^sub>B G\<close>
    then have "\<not>\<^sub>B F \<and>\<^sub>B (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B \<not>\<^sub>B F  \<or>\<^sub>B G"
      using MP by blast
    then show ?thesis
      using ImpT by blast
  qed

  note\<open>F \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B (\<not>\<^sub>B F \<or>\<^sub>B G)\<close> \<open>\<not>\<^sub>B F \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B (\<not>\<^sub>B F \<or>\<^sub>B G)\<close>
  then have "F \<or>\<^sub>B \<not>\<^sub>B F \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B (\<not>\<^sub>B F \<or>\<^sub>B G)" 
    using DisjE by blast
  then have "(F \<or>\<^sub>B \<not>\<^sub>B F) \<and>\<^sub>B (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B \<not>\<^sub>B F \<or>\<^sub>B G" 
    using ImpB by blast
  then have "(F \<rightarrow>\<^sub>B G) \<and>\<^sub>B (F \<or>\<^sub>B \<not>\<^sub>B F) \<turnstile>\<^sub>B \<not>\<^sub>B F \<or>\<^sub>B G"
    using MP commAnd by blast

  note\<open>F \<rightarrow>\<^sub>B G  \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<and>\<^sub>B (F \<or>\<^sub>B (\<not>\<^sub>B F))\<close>\<open>(F \<rightarrow>\<^sub>B G) \<and>\<^sub>B (F \<or>\<^sub>B \<not>\<^sub>B F) \<turnstile>\<^sub>B \<not>\<^sub>B F \<or>\<^sub>B G \<close>
  then show ?thesis 
    using MP by blast
qed

section"Soundness for Postulates"
    
lemma SoundPostulateCL1 : "Valid((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C \<sharp>Y ; Z)"
  apply simp
proof-
  assume "\<Psi> X \<and>\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Upsilon> Z" 
  then have "\<Psi> X \<turnstile>\<^sub>B \<Psi> Y \<rightarrow>\<^sub>B \<Upsilon> Z" using ImpT by blast
  have "\<Psi> Y \<rightarrow>\<^sub>B \<Upsilon> Z \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> Y) \<or>\<^sub>B \<Upsilon> Z" 
    by (simp add: impTodis)
  then show "\<Psi> X \<and>\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Upsilon> Z \<Longrightarrow> \<Psi> X \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> Y) \<or>\<^sub>B \<Upsilon> Z" 
    using MP \<open>\<Psi> X \<turnstile>\<^sub>B \<Psi> Y \<rightarrow>\<^sub>B \<Upsilon> Z\<close> by blast
qed

lemma SoundPostulateCL1S: "Valid (X \<turnstile>\<^sub>C \<sharp>Y ; Z) \<Longrightarrow> Valid ((X ;\<^sub>A Y) \<turnstile>\<^sub>C Z)" 
  apply simp
  using ImpB MP disToimp by blast

lemma SoundPostulateCL2 : "Valid((X \<turnstile>\<^sub>C \<sharp>Y ; Z)) \<Longrightarrow> Valid (Y ;\<^sub>A X \<turnstile>\<^sub>C Z)"
  apply simp
proof - 
  assume "\<Psi> X \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> Y) \<or>\<^sub>B \<Upsilon> Z"
  have " \<not>\<^sub>B (\<Psi> Y) \<or>\<^sub>B \<Upsilon> Z \<turnstile>\<^sub>B  \<Psi> Y \<rightarrow>\<^sub>B \<Upsilon> Z" using disToimp by simp
  then show "\<Psi> X \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> Y) \<or>\<^sub>B \<Upsilon> Z \<Longrightarrow> \<Psi> Y \<and>\<^sub>B \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Z" using MP commAnd ImpB by blast
qed

lemma SoundPostulateCL2S :"Valid(Y ;\<^sub>A X \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid((X \<turnstile>\<^sub>C \<sharp>Y ; Z))"
  apply simp
  using ImpT MP commAnd impTodis by blast

lemma SoundPostulateCL3 : "Valid ((X \<turnstile>\<^sub>C Y ; Z)) \<Longrightarrow> Valid((X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z))"
  apply simp
proof -
  assume "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y \<or>\<^sub>B \<Upsilon> Z"
  have "\<Upsilon> Y \<or>\<^sub>B \<Upsilon> Z \<turnstile>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<rightarrow>\<^sub>B \<Upsilon> Z" 
  proof-
    have "\<Upsilon> Z \<turnstile>\<^sub>B\<not>\<^sub>B(\<not>\<^sub>B (\<Upsilon> Y)) \<or>\<^sub>B \<Upsilon> Z" 
      using DisjI2 by simp
    then have "\<Upsilon> Z \<turnstile>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<rightarrow>\<^sub>B \<Upsilon> Z"
      using MP disToimp by blast
    
    have "\<Upsilon> Y \<turnstile>\<^sub>B \<not>\<^sub>B(\<not>\<^sub>B (\<Upsilon> Y))"
      using  NotnotR by simp
    then have "\<Upsilon> Y \<turnstile>\<^sub>B \<not>\<^sub>B(\<not>\<^sub>B (\<Upsilon> Y)) \<or>\<^sub>B \<Upsilon> Z" 
      using DisjI1 MP by blast
    then have "\<Upsilon> Y \<turnstile>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<rightarrow>\<^sub>B \<Upsilon> Z" 
      using MP disToimp by blast

    note\<open>\<Upsilon> Z \<turnstile>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<rightarrow>\<^sub>B \<Upsilon> Z\<close>\<open>\<Upsilon> Y \<turnstile>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<rightarrow>\<^sub>B \<Upsilon> Z\<close>
    then show ?thesis 
      using DisjE by simp
  qed

  then show "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y \<or>\<^sub>B \<Upsilon> Z \<Longrightarrow> \<Psi> X \<and>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<Upsilon> Z"
    using ImpB MP by blast
qed

lemma SoundPostulateCL3S: "Valid((X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z)) \<Longrightarrow> Valid ((X \<turnstile>\<^sub>C Y ; Z))"
  apply simp
proof-
  assume "\<Psi> X \<and>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<Upsilon> Z"
  then have "\<Psi> X \<turnstile>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<rightarrow>\<^sub>B \<Upsilon> Z" 
    using ImpT by simp
  then have "\<Psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B (\<not>\<^sub>B (\<Upsilon> Y))) \<or>\<^sub>B \<Upsilon> Z" 
    using MP impTodis by blast
  have "(\<not>\<^sub>B (\<not>\<^sub>B (\<Upsilon> Y))) \<or>\<^sub>B \<Upsilon> Z  \<turnstile>\<^sub>B \<Upsilon> Y \<or>\<^sub>B \<Upsilon> Z" 
    using DisjE DisjI1 DisjI2 MP Notnot by blast

  note \<open>(\<not>\<^sub>B(\<not>\<^sub>B (\<Upsilon> Y))) \<or>\<^sub>B \<Upsilon> Z \<turnstile>\<^sub>B \<Upsilon> Y \<or>\<^sub>B \<Upsilon> Z\<close> \<open>\<Psi> X \<turnstile>\<^sub>B (\<not>\<^sub>B(\<not>\<^sub>B (\<Upsilon> Y))) \<or>\<^sub>B \<Upsilon> Z\<close>
  then show "\<Psi> X \<and>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<Upsilon> Z \<Longrightarrow> \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y \<or>\<^sub>B \<Upsilon> Z" 
    using MP  by blast
qed

lemma SoundPostulateCL4 : "Valid (X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Z ; Y)"
  apply simp
proof-
  assume "\<Psi> X \<and>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<Upsilon> Z" 
  then have "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y \<or>\<^sub>B \<Upsilon> Z" 
    using SoundPostulateCL3S by simp
  then show "\<Psi> X \<and>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<Upsilon> Z \<Longrightarrow> \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Z \<or>\<^sub>B \<Upsilon> Y"
    using MP commOR by blast
qed

lemma SoundPostulateCL4S : "Valid (X \<turnstile>\<^sub>C Z ; Y) \<Longrightarrow> Valid (X ;\<^sub>A \<sharp>\<^sub>AY \<turnstile>\<^sub>C Z)"
  apply simp
proof -
  assume "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Z \<or>\<^sub>B \<Upsilon> Y"
  then have "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y \<or>\<^sub>B \<Upsilon> Z" 
    using MP commOR by blast
  then show "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Z \<or>\<^sub>B \<Upsilon> Y \<Longrightarrow> \<Psi> X \<and>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<Upsilon> Z"
    using SoundPostulateCL3 by simp
qed

lemma SoundPostulateCL5 : "Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X)"
  apply simp
proof-
  assume "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y"
  have "\<Upsilon>  Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<Upsilon> Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
    using Ax by simp
  then have "\<Upsilon> Y \<turnstile>\<^sub>B (\<Upsilon> Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B) \<rightarrow>\<^sub>B \<bottom>\<^sub>B"
    using ImpT ImpB MP commAnd by blast
  then have "\<Psi> X \<turnstile>\<^sub>B (\<Upsilon> Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B) \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
    using MP \<open>\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y\<close> by blast
  then have "\<Upsilon> Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<Psi> X \<rightarrow>\<^sub>B \<bottom>\<^sub>B" 
    using ImpT ImpB MP commAnd by blast
  then have "\<Upsilon> Y \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> X) " 
    using Notr MP by blast
  then have "\<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> X)" 
    using Notl MP by blast
  then show "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y \<Longrightarrow> \<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> X)" by simp
qed

lemma SoundPostulateCL5S : "Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y)"
  apply simp
proof-
  assume "\<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> X)"
  then have "\<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<Psi> X \<rightarrow>\<^sub>B \<bottom>\<^sub>B"
    using MP Notl by blast
  then have "\<Psi> X \<turnstile>\<^sub>B \<not>\<^sub>B (\<Upsilon> Y) \<rightarrow>\<^sub>B \<bottom>\<^sub>B " 
    using ImpB ImpT MP commAnd by blast
  then have "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y"
    using MP reverseNot1 by blast
  then show "\<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> X) \<Longrightarrow> \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y"
    by blast
qed

lemma SoundPostulateCL6 : "Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X) \<Longrightarrow> Valid (\<sharp>\<^sub>A(\<sharp>X) \<turnstile>\<^sub>C Y)"
  apply simp
proof -
  assume "\<not>\<^sub>B(\<Upsilon> Y) \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> X)" 
  then have "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y" 
    using SoundPostulateCL5S by simp
  then show "\<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> X) \<Longrightarrow> \<not>\<^sub>B (\<not>\<^sub>B (\<Psi> X)) \<turnstile>\<^sub>B \<Upsilon> Y"
    using MP Notnot by blast
qed


lemma SoundPostulateCL6S : "Valid (\<sharp>\<^sub>A(\<sharp>X) \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X)"
  apply simp
proof-
  assume"\<not>\<^sub>B (\<not>\<^sub>B (\<Psi> X)) \<turnstile>\<^sub>B \<Upsilon> Y"
  then have "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y"
    using MP NotnotR by blast
  then show "\<not>\<^sub>B (\<not>\<^sub>B (\<Psi> X)) \<turnstile>\<^sub>B \<Upsilon> Y \<Longrightarrow> \<not>\<^sub>B (\<Upsilon> Y) \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> X)"
    using SoundPostulateCL5 by simp
qed

lemma SoundPostulateCL7 : "Valid (X ,\<^sub>A Y \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z)"
  apply simp
proof - 
  assume "\<Psi> X *\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Upsilon> Z" 
  then have "\<Psi> X \<turnstile>\<^sub>B \<Psi> Y  \<rightarrow>\<^emph>\<^sub>B \<Upsilon> Z" using ImpstarT by simp
  then show "\<Psi> X *\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Upsilon> Z \<Longrightarrow> \<Psi> X \<turnstile>\<^sub>B \<Psi> Y \<rightarrow>\<^emph>\<^sub>B \<Upsilon> Z" by simp
qed

lemma SoundPostulateCL7S : "Valid (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z) \<Longrightarrow> Valid (X ,\<^sub>A Y \<turnstile>\<^sub>C Z)"
  apply simp
  using ImpstarB by simp

lemma SoundPostulateCL8 : "Valid (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z) \<Longrightarrow> Valid (Y ,\<^sub>A X \<turnstile>\<^sub>C Z)"
  apply simp 
proof -
  assume "\<Psi> X \<turnstile>\<^sub>B \<Psi> Y \<rightarrow>\<^emph>\<^sub>B \<Upsilon> Z"
  then have "\<Psi> X *\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Upsilon> Z" using ImpstarB by blast
  then have "\<Psi> Y *\<^sub>B \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Z" using Comm MP by blast
  thus "\<Psi> X \<turnstile>\<^sub>B \<Psi> Y \<rightarrow>\<^emph>\<^sub>B \<Upsilon> Z \<Longrightarrow> \<Psi> Y *\<^sub>B \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Z" by simp
qed

lemma SoundPostulateCL8S : "Valid (Y ,\<^sub>A X \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Z)"
  apply simp
proof-
  assume "\<Psi> Y *\<^sub>B \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Z"
  then have "\<Psi> X *\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Upsilon> Z" 
    using Comm MP by blast
  then show "\<Psi> Y *\<^sub>B \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Z \<Longrightarrow> \<Psi> X \<turnstile>\<^sub>B \<Psi> Y \<rightarrow>\<^emph>\<^sub>B \<Upsilon> Z" 
    using ImpstarT by blast
qed


section"Soundness for logical and structural rules"

theorem Soundness: "\<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid(X \<turnstile>\<^sub>C Y)"
 proof (induction rule:Provable.induct)
  case (BotL X)
  then show ?case 
  proof-
    have "\<Psi> (formulaA \<bottom>\<^sub>B) \<turnstile>\<^sub>B \<Upsilon> X" 
      using Bot by simp
    then show ?case 
      by simp
  qed
next
  case (BotR X)
  then show ?case 
  proof - 
    note\<open>Valid (X \<turnstile>\<^sub>C \<emptyset>)\<close>
    then have " \<Psi> X \<turnstile>\<^sub>B \<bottom>\<^sub>B" 
      by simp
    then show ?case 
      by simp
  qed
next
  case (TopL X)
  then show ?case by simp
next
  case (TopR X)
  then show ?case 
    using Top by simp
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
  proof - 
    note \<open>Valid (formulaA F \<turnstile>\<^sub>C X)\<close> \<open>Valid (formulaA G \<turnstile>\<^sub>C X)\<close>
    then have "F \<or>\<^sub>B G \<turnstile>\<^sub>B \<Upsilon> X" using DisjE by simp
    thus ?case by simp
  qed
next
  case (orR X F G)
  then show ?case by simp
next
  case (andL F G X)
  then show ?case by simp
next
  case (andR X F G)
  then show ?case 
  proof - 
    note\<open>Valid (X \<turnstile>\<^sub>C formula F)\<close>\<open>Valid (X \<turnstile>\<^sub>C formula G)\<close>
    hence "\<Psi> X \<turnstile>\<^sub>B F \<and>\<^sub>B G" using ConjI by simp
    thus ?case by simp
  qed
next
  case (impL X F G Y)
  then show ?case 
  proof -
    have "(\<Psi> X \<rightarrow>\<^sub>B \<Upsilon> Y)\<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> X) \<or>\<^sub>B \<Upsilon> Y" 
      by (simp add: impTodis)
    have "F \<rightarrow>\<^sub>B G \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G" using Ax by simp
    then have "F \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B G" using ImpT ImpB MP commAnd by blast
    note \<open>Valid (X \<turnstile>\<^sub>C formula F)\<close>\<open>F \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B G\<close>
    then have "\<Psi> X \<turnstile>\<^sub>B (F \<rightarrow>\<^sub>B G) \<rightarrow>\<^sub>B G" using MP by simp
    then have "(F \<rightarrow>\<^sub>B G) \<and>\<^sub>B \<Psi> X \<turnstile>\<^sub>B G"
      using ImpB MP commAnd by blast
    note\<open>Valid (formulaA G \<turnstile>\<^sub>C Y)\<close>\<open>(F \<rightarrow>\<^sub>B G) \<and>\<^sub>B \<Psi> X \<turnstile>\<^sub>B G\<close>
    then have "(F \<rightarrow>\<^sub>B G) \<and>\<^sub>B \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y" using MP by simp
    then have "(F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B (\<Psi> X \<rightarrow>\<^sub>B \<Upsilon> Y)" using ImpT by simp
    then have "(F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>B \<not>\<^sub>B (\<Psi> X) \<or>\<^sub>B \<Upsilon> Y" 
      using MP impTodis by blast
    then show ?case 
      by simp
  qed
next
  case (impR X F G)
  then show ?case 
  proof -
    note\<open>Valid (X ;\<^sub>A formulaA F \<turnstile>\<^sub>C formula G)\<close>
    then have "\<Psi> X \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B G" using ImpT by simp
    thus ?case 
      by simp
  qed
next
  case (nilL X Y)
  then show ?case 
  proof -
    have "\<Psi> X \<turnstile>\<^sub>B \<Psi> X" 
      using Ax by simp
    have "\<Psi> X \<turnstile>\<^sub>B \<top>\<^sub>B" 
      using Top by simp
    note\<open>\<Psi> X \<turnstile>\<^sub>B\<Psi> X\<close>\<open>\<Psi> X \<turnstile>\<^sub>B \<top>\<^sub>B\<close>
    then have "\<Psi> X \<turnstile>\<^sub>B \<top>\<^sub>B \<and>\<^sub>B \<Psi> X" 
      using ConjI by simp
    note\<open>Valid (\<emptyset>\<^sub>A ;\<^sub>A X \<turnstile>\<^sub>C Y)\<close>\<open>\<Psi> X \<turnstile>\<^sub>B \<top>\<^sub>B \<and>\<^sub>B \<Psi> X\<close>
    then show ?case 
      using MP by simp
  qed  
next
  case (nilL_sym X Y)
  then show ?case 
  proof-
    have "\<top>\<^sub>B \<and>\<^sub>B \<Psi> X \<turnstile>\<^sub>B \<Psi> X" 
      using ConjE2 by simp
    note\<open>Valid (X \<turnstile>\<^sub>C Y)\<close> \<open>\<top>\<^sub>B \<and>\<^sub>B \<Psi> X \<turnstile>\<^sub>B \<Psi> X\<close>
    then show ?case using MP 
      by simp
  qed
next
case (nilR X Y)
  then show ?case 
  proof-
    have "\<Upsilon> Y \<turnstile>\<^sub>B \<Upsilon> Y" 
      using Ax by simp
    have "\<bottom>\<^sub>B \<turnstile>\<^sub>B \<Upsilon> Y" 
      using Bot by simp
    note\<open>\<Upsilon> Y \<turnstile>\<^sub>B \<Upsilon> Y\<close>\<open>\<bottom>\<^sub>B \<turnstile>\<^sub>B \<Upsilon> Y\<close>
    then have "\<Upsilon> Y \<or>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<Upsilon> Y" 
      using DisjE by simp
    note\<open>Valid (X \<turnstile>\<^sub>C Y ; \<emptyset>)\<close>\<open>\<Upsilon> Y \<or>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B \<Upsilon> Y\<close>
    then have  "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y" using  MP by simp
    thus ?case by simp
  qed
next
  case (nilR_sym X Y)
  then show ?case 
    using DisjI1 MP by simp
next
  case (AAL W X Y Z)
  then show ?case
  proof-
    note\<open>Valid (W ;\<^sub>A (X ;\<^sub>A Y) \<turnstile>\<^sub>C Z)\<close>
    then have "\<Psi> W \<and>\<^sub>B (\<Psi> X \<and>\<^sub>B \<Psi> Y) \<turnstile>\<^sub>B \<Upsilon> Z" by simp
    then have "(\<Psi> W \<and>\<^sub>B \<Psi> X) \<and>\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Upsilon> Z" 
      using MP assocAnd2 by blast
    then show ?case by simp
  qed
next
  case (AAL_sym W X Y Z)
  then show ?case 
  proof-
    note\<open>Valid ((W ;\<^sub>A X) ;\<^sub>A Y \<turnstile>\<^sub>C Z)\<close>
    then have "(\<Psi> W \<and>\<^sub>B \<Psi> X) \<and>\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Upsilon> Z" by simp
    then have "\<Psi> W \<and>\<^sub>B (\<Psi> X \<and>\<^sub>B \<Psi> Y) \<turnstile>\<^sub>B \<Upsilon> Z"
      using MP assocAnd1 by blast
    then show ?case by simp
  qed
next 
  case (AAR W X Y Z)
  then show ?case 
    using MP assocOr2 by simp
next
  case (AAR_sym W X Y Z)
  then show ?case 
    using MP assocOr1 by simp
next
  case (WkL X Z Y)
  then show ?case 
  proof -
    note\<open>Valid (X \<turnstile>\<^sub>C Z)\<close>
    then have "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Z" 
      by simp
    have "\<Psi> X \<and>\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Psi> X"
      using ConjE1 by simp
    note\<open>\<Psi> X \<and>\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Psi> X\<close>\<open>\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Z\<close>
    then show ?case 
      using MP by simp
  qed
next
  case (WkR X Z Y)
  then show ?case using DisjI2 MP 
    by simp

next
  case (CtrL X Y)
  then show ?case 
  proof -
    note\<open>Valid (X ;\<^sub>A X \<turnstile>\<^sub>C Y)\<close>
    then have "\<Psi> X \<and>\<^sub>B \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y" by simp
    then have "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y" using Ax ConjI MP by blast
    then show ?case by simp
  qed
next
  case (CtrR X Y)
  then show ?case 
  proof -
    note\<open>Valid (X \<turnstile>\<^sub>C Y ; Y)\<close>
    then have "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y \<or>\<^sub>B \<Upsilon> Y" by simp
    then have "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y "
      using Ax DisjE MP by blast
    then show ?case by simp 
  qed
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
  proof -
    note\<open>Valid (X \<turnstile>\<^sub>C formula F)\<close>
    then have "\<Psi> X \<turnstile>\<^sub>B F" by simp
    have "F \<rightarrow>\<^emph>\<^sub>B G \<turnstile>\<^sub>B F \<rightarrow>\<^emph>\<^sub>B G" using Ax by simp 
    then have "F \<turnstile>\<^sub>B (F \<rightarrow>\<^emph>\<^sub>B G) \<rightarrow>\<^emph>\<^sub>B G" 
      using Comm ImpstarB ImpstarT MP by blast
    note\<open>\<Psi> X \<turnstile>\<^sub>B F\<close>\<open>F \<turnstile>\<^sub>B (F \<rightarrow>\<^emph>\<^sub>B G) \<rightarrow>\<^emph>\<^sub>B G\<close>
    then have "\<Psi> X \<turnstile>\<^sub>B (F \<rightarrow>\<^emph>\<^sub>B G) \<rightarrow>\<^emph>\<^sub>B G" using MP 
      by blast
    then have "\<Psi> X *\<^sub>B (F \<rightarrow>\<^emph>\<^sub>B G) \<turnstile>\<^sub>B G" 
      using ImpstarB by simp
    note\<open>Valid (formulaA G \<turnstile>\<^sub>C Y)\<close>
    then have "G \<turnstile>\<^sub>B \<Upsilon> Y" by simp
    note\<open>G \<turnstile>\<^sub>B \<Upsilon> Y\<close>\<open>\<Psi> X *\<^sub>B (F \<rightarrow>\<^emph>\<^sub>B G) \<turnstile>\<^sub>B G\<close>
    then have "\<Psi> X *\<^sub>B (F \<rightarrow>\<^emph>\<^sub>B G) \<turnstile>\<^sub>B \<Upsilon> Y"  using MP by blast
    then have "F \<rightarrow>\<^emph>\<^sub>B G \<turnstile>\<^sub>B \<Psi> X \<rightarrow>\<^emph>\<^sub>B \<Upsilon> Y" 
      using Comm ImpstarT MP by blast
    then show ?case
      by simp
  qed
next
  case TopMultR
  then show ?case 
    using Ax by simp
next
  case (andMultR X F Y G)
  then show ?case 
    using ConjIstar by simp
next
  case (impMultR X F G)
  then show ?case 
    using ImpstarT by simp
next
  case (nilMultL X Y)
  then show ?case
  proof - 
    note\<open>Valid (\<oslash> ,\<^sub>A X \<turnstile>\<^sub>C Y)\<close>
    then have "\<top>\<^sup>*\<^sub>B *\<^sub>B \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y" by simp
    then have "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y" 
      using Comm MP Topr by blast
    then show ?case by simp
  qed
next
  case (nilMultL_sym X Y)
  then show ?case 
  proof - 
    note\<open>Valid (X \<turnstile>\<^sub>C Y)\<close>
    then have "\<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y" by simp
    then have "\<top>\<^sup>*\<^sub>B *\<^sub>B \<Psi> X \<turnstile>\<^sub>B \<Upsilon> Y" 
      using Comm MP Topl by blast
    then show ?case by simp
qed
next
  case (MAL W X Y Z)
  then show ?case 
  proof-
    note\<open>Valid (W ,\<^sub>A (X ,\<^sub>A Y) \<turnstile>\<^sub>C Z)\<close>
    then have "\<Psi> W *\<^sub>B (\<Psi> X *\<^sub>B \<Psi> Y) \<turnstile>\<^sub>B \<Upsilon> Z" by simp
    then have "(\<Psi> W *\<^sub>B \<Psi> X) *\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Upsilon> Z"
      using Assocr MP by blast
    then show ?case by simp
  qed
next
  case (MAL_sym W X Y Z)
  then show ?case
  proof-
    note\<open>Valid ((W ,\<^sub>A X) ,\<^sub>A Y \<turnstile>\<^sub>C Z)\<close>
    then have "(\<Psi> W *\<^sub>B \<Psi> X) *\<^sub>B \<Psi> Y \<turnstile>\<^sub>B \<Upsilon> Z" by simp
    then have "\<Psi> W *\<^sub>B (\<Psi> X *\<^sub>B \<Psi> Y) \<turnstile>\<^sub>B \<Upsilon> Z"
      using Assocl MP by blast
    then show ?case by simp
  qed
next
  case (cut X F Y)
  then show ?case 
    using MP by simp
next 
  case (equiv X' Y' X Y)
  then show ?case 
  proof(induction rule: displayEquiv.induct)
    case (positulatesCL1 X Y Z)
    then show ?case 
      using SoundPostulateCL1 by blast
  next
    case (positulatesCL1S X Y Z)
    then show ?case 
      using SoundPostulateCL1S by blast
  next
    case (positulatesCL2 X Y Z)
    then show ?case 
      using SoundPostulateCL2 by blast
  next
    case (positulatesCL2S Y X Z)
    then show ?case 
      using SoundPostulateCL2S by blast
  next
    case (positulatesCL3 X Y Z)
    then show ?case 
      using SoundPostulateCL3 by blast
  next
    case (positulatesCL3S X Y Z)
    then show ?case 
      using SoundPostulateCL3S by blast
  next
    case (positulatesCL4 X Y Z)
    then show ?case 
      using SoundPostulateCL4 by blast
  next
    case (positulatesCL4S X Z Y)
    then show ?case 
      using SoundPostulateCL4S by blast
  next
    case (positulatesCL5 X Y)
    then show ?case 
      using SoundPostulateCL5 by blast
  next
    case (positulatesCL5S Y X)
    then show ?case 
      using SoundPostulateCL5S by blast
  next
    case (positulatesCL6 Y X)
    then show ?case 
      using SoundPostulateCL6 by blast
  next
    case (positulatesCL6S X Y)
    then show ?case 
      using SoundPostulateCL6S by blast
  next
    case (positulatesCL7 X Y Z)
    then show ?case 
      using SoundPostulateCL7 by blast
  next
    case (positulatesCL7S X Y Z)
    then show ?case 
      using SoundPostulateCL7S by blast
  next
    case (positulatesCL8 X Y Z)
    then show ?case 
      using SoundPostulateCL8 by blast
  next
    case (positulatesCL8S Y X Z)
    then show ?case 
      using SoundPostulateCL8S by blast
  next
    case (display_refl C)
    then show ?case
      by simp
  next
    case (display_trans C C' C'')
    then show ?case 
    proof-
    note\<open>\<P> C\<close>\<open>C \<equiv>\<^sub>D C'\<close>
    then have "\<P> C'"
      by (metis Consecution.exhaust Provable.equiv)
    note\<open>\<P> C' \<Longrightarrow> Valid C' \<Longrightarrow> Valid C''\<close>\<open>\<P> C'\<close>\<open>\<P> C \<Longrightarrow> Valid C \<Longrightarrow> Valid C'\<close>\<open>\<P> C\<close>\<open>Valid C\<close>
    then show "Valid C''" 
      by blast
  qed
qed
next 
  case (id atom)
  then show ?case 
    using Ax by simp
qed



end