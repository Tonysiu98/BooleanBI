theory test
  imports Main def
begin


inductive
    pos :: "Structure \<Rightarrow> Structure \<Rightarrow> bool"
and neg:: "Structure \<Rightarrow> Structure \<Rightarrow>  bool"
where
  "X = Y \<Longrightarrow> pos X Y"|
 "pos (Inl X) (Inl Y) \<Longrightarrow> neg (Inl X) (Inr(\<sharp>Y))"

lemma
  shows "pos Z X \<Longrightarrow> \<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))" and "neg (Inl Z) (Inr Y) \<Longrightarrow>\<exists>W.((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W))" 
proof (induct Z X and Z Y rule: pos_neg.inducts)

  print_state



end