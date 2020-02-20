theory test
  imports Main def
begin

lemma "A \<or> B \<Longrightarrow> C"
proof -
  have "A \<Longrightarrow> C" and "B \<Longrightarrow> C" sorry
  then show "A \<or> B \<Longrightarrow> C" by blast
qed




end