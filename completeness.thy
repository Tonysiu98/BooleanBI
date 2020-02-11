theory completeness
    imports Main def
begin


lemma identity: "\<P>(formulaA F \<turnstile>\<^sub>C formula F)"
proof(induction F)
case Truth
then show ?case sorry
next
case Falsity
  then show ?case sorry
next
  case Mfalsity
  then show ?case sorry
next
  case (Atom x)
  then show ?case sorry
next
  case (Neg F)
  then show ?case sorry
next
  case (Con F1 F2)
  then show ?case sorry
next
  case (MCon F1 F2)
  then show ?case sorry
next
  case (Dis F1 F2)
  then show ?case sorry
next
  case (Imp F1 F2)
  then show ?case sorry
next
  case (Mimp F1 F2)
  then show ?case sorry
qed


lemma \<psi>L: "\<P>(X \<turnstile>\<^sub>C Y) \<Longrightarrow> \<P>(formulaA (\<psi> X) \<turnstile>\<^sub>C Y)"
  sorry

lemma \<psi>R: "\<P>(X \<turnstile>\<^sub>C formula (\<psi> X))" and  \<gamma>Y : "\<P>(formulaA (\<gamma> Y) \<turnstile>\<^sub>C Y)"
proof(induction X and Y)
case (formulaA x)
  then show ?case sorry
next
case AddNilA
  then show ?case sorry
next
case (SharpA x)
then show ?case sorry
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

(*
lemma \<gamma>Y : "\<P>(formulaA (\<gamma> Y) \<turnstile>\<^sub>C Y)"
  sorry
*)

lemma \<gamma>R : "\<P>(Y \<turnstile>\<^sub>C X) \<Longrightarrow> \<P>(Y \<turnstile>\<^sub>C formula (\<gamma> X))"
  sorry


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