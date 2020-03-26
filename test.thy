theory test
  imports Main def display
begin
lemma  
  assumes "(X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (X' \<turnstile>\<^sub>C Y')" and "Valid(X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid(X' \<turnstile>\<^sub>C Y')"
  shows "Valid(X' \<turnstile>\<^sub>C Y') \<Longrightarrow> Valid(X \<turnstile>\<^sub>C Y)"
proof-
  have "(X' \<turnstile>\<^sub>C Y') \<equiv>\<^sub>D (X \<turnstile>\<^sub>C Y)"
    by (simp add: assms(1) display_symm)
end
