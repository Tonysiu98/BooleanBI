theory test
  imports Main def
begin

lemma  "pos (Inl Z) (Inl X) \<Longrightarrow> E Z X" 
      and
       "neg (Inl Z) (Inr Y) \<Longrightarrow> Q Z Y"
proof (induct rule:pos_neg.inducts) print_cases
  oops

inductive
    pos :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
and neg:: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "X = Y \<Longrightarrow> pos X Y"
| "pos X Y \<Longrightarrow> neg X Y"

lemma
  fixes A B C D :: "nat"
  shows "pos A B \<Longrightarrow> Q A B" and "neg C D \<Longrightarrow>E C D"
proof (induct rule: pos_neg.inducts) print_cases
  oops

lemma "A \<or> B \<Longrightarrow> C"
proof -
  have "A \<Longrightarrow> C" and "B \<Longrightarrow> C" sorry
  then show "A \<or> B \<Longrightarrow> C" by blast
qed

end