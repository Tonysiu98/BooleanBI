theory displayCalculus
  imports Main BBI Structure
begin 

(*Given that Consecution X Y is provable, show the consecution is valid. The Valid function 
transform structure to formulae*)

(* all proofs are invalid*)
lemma simp : "\<P> (X \<turnstile>\<^sub>C Y) \<Longrightarrow>  Valid (X \<turnstile>\<^sub>C Y)"
  using ConjE1 DisjI2 MP Valid.simps by blast
(*
lemma soundnessPostulates:
  assumes "(X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z  \<turnstile>\<^sub>C W)"
  shows "Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (Z  \<turnstile>\<^sub>C W)"
  sledgehammer
  using ConjE2 DisjI1 MP Valid.elims(3) by blast

*)
(*
proof -
  from positulatesCL5 have "F \<turnstile>\<^sub>B G" 
    using ConjE1 DisjI2 MP by blast
  then have"(\<not>\<^sub>BG) \<turnstile>\<^sub>B (\<not>\<^sub>BF)"
    using ConjE1 DisjI2 MP by blast
*)


lemma "Valid (X ;\<^sub>A (formulaA F) \<turnstile>\<^sub>C formula G) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula (F \<rightarrow>\<^sub>B  G))"
proof -
  assume "Valid (X ;\<^sub>A (formulaA F) \<turnstile>\<^sub>C formula G)" 
  have "Valid (X \<turnstile>\<^sub>C formula (F \<rightarrow>\<^sub>B  G))"
    using ConjE1 DisjI2 MP Valid.simps by blast
  then show "Valid (X ;\<^sub>A (formulaA F) \<turnstile>\<^sub>C formula G) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula (F \<rightarrow>\<^sub>B  G))"
    by blast
qed


  
lemma "Valid (X \<turnstile>\<^sub>C formula F ; formula G) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula (F \<or>\<^sub>B G))"
proof -
  assume "Valid (X \<turnstile>\<^sub>C formula F ; formula G)"
  have "Valid (X \<turnstile>\<^sub>C formula (F \<or>\<^sub>B G))"
    using ConjE2 DisjI1 MP Valid.simps by blast
  then show "Valid (X \<turnstile>\<^sub>C formula F ; formula G) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula (F \<or>\<^sub>B G))"
    by blast
qed

lemma "Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X)"
proof -
  assume "Valid (X \<turnstile>\<^sub>C Y)"
  have "Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X)"
    using ConjE2 DisjI1 MP Valid.simps by blast
  then show "Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (\<sharp>\<^sub>AY \<turnstile>\<^sub>C \<sharp>X)"
    by blast
qed

  

end