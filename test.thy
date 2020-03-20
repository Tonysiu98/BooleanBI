theory test
  imports Main def completeness
begin

lemma "\<psi> X \<turnstile>\<^sub>B \<gamma> Y \<Longrightarrow> \<P>(formulaA (\<psi> X) \<turnstile>\<^sub>C formula (\<gamma> Y))" 
proof(induction rule: turnstile_BBI.induct)
case (Ax F)
  then show ?case 
    by (simp add: identity)
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

lemma formuDL:"F \<turnstile>\<^sub>B G \<Longrightarrow> \<P>(formulaA F \<turnstile>\<^sub>C formula G)"
proof(induction rule: turnstile_BBI.induct)
  case (Ax F)
  then show ?case 
    by (simp add: identity)
next
  case (Top F)
  then show ?case 
    by (simp add: TopR)
next
  case (Bot F)
  then show ?case 
    by (simp add: BotL)
next
  case (ImpT F G H)
  then show ?case 
    by (metis \<psi>.simps(1) \<psi>.simps(4) \<psi>R cut impR)
next
  case (ImpB F G H)
  then show ?case 
    by (meson andL cut display_symm equiv identity impL positulatesCL1)
next
  case (MP F G H)
then show ?case 
  using cut by blast
next
  case (Notl F)
  then show ?case 
    by (metis WkL \<gamma>.simps(3) \<gamma>Y \<psi>.simps(1) equiv impR positulatesCL1 positulatesCL2 positulatesCL4)
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
(*not rule in BBI*)
lemma "\<P>(formulaA (\<not>\<^sub>B F) \<turnstile>\<^sub>C formula (F \<rightarrow>\<^sub>B \<bottom>\<^sub>B))"
proof -
  have"\<P>(formulaA (\<not>\<^sub>B F) \<turnstile>\<^sub>C \<sharp>(formulaA F))"
    by (metis \<gamma>.simps(3) \<gamma>Y \<psi>.simps(1))
  then have "\<P>(formulaA (\<not>\<^sub>B F) \<turnstile>\<^sub>C \<sharp>(formulaA F) ; formula (\<bottom>\<^sub>B))"
    using WkL equiv positulatesCL4 by blast
  then have "\<P>(formulaA (\<not>\<^sub>B F) ;\<^sub>A formulaA (F) \<turnstile>\<^sub>C formula (\<bottom>\<^sub>B))" 
    using display_symm equiv positulatesCL1 by blast
  then have "\<P>(formulaA (\<not>\<^sub>B F) \<turnstile>\<^sub>C formula(F \<rightarrow>\<^sub>B \<bottom>\<^sub>B))" 
    by (simp add: impR)
  thus ?thesis 
    by blast
qed

end
