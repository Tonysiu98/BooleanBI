theory Scratch 
  imports Main
begin
text\<open>This Isabelle file is for logging purpose and practice\<close>

section "Practice proof"

typedef three ="{0::nat,1,2}"
  apply(rule_tac x = 0 in exI)
  by simp

definition A :: three where "A \<equiv> Abs_three 0"
definition B :: three where "B \<equiv> Abs_three 1"
definition C :: three where "C \<equiv> Abs_three 2"

lemma"A \<noteq> B \<and> B \<noteq> A \<and> A \<noteq> C \<and> C \<noteq> A \<and> B \<noteq> C \<and> C \<noteq> B"
  by (simp add: Abs_three_inject A_def B_def C_def)

lemma three_cases : "\<lbrakk>P A ; P B; P C\<rbrakk> \<Longrightarrow> P x"
  apply(induct_tac x)
  apply auto
  apply (auto simp add: A_def B_def C_def)
  done

section "logging"

(* This is the initial definition of Valid. The problem with this definition is  (Consecution X Y) 
is a malformed argument This is because definition doesnt allow pattern matching *)
(*
definition Valid :: "Consecution \<Rightarrow> bool" where
"Valid (Consecution X Y) =  \<psi> X  \<turnstile>\<^sub>B \<gamma> Y"
*)

(*Then the new approach is to define two function which can output the Antecedent and Consequent 
Structures
primrec antC :: "Consecution \<Rightarrow> Antecedent_Structure" where
"antC (X \<turnstile>\<^sub>C Y) = X"

primrec ConC :: "Consecution \<Rightarrow> Consequent_Structure" where
"ConC (X \<turnstile>\<^sub>C Y) = Y"

(*Then the below definition can be evaluated succefully*)
definition Valid :: "Consecution \<Rightarrow> bool" where
"Valid C \<equiv> \<psi> (antC C) \<turnstile>\<^sub>B \<gamma> (ConC C)"
*)

(*
(*Now we try to define a symmetric relation called Display Postulates. We are using Isabelle 
predefined relation theory rel. Therefore Display_postulates is a set of relations*)
type_synonym Display_postulates = "Consecution rel"

(*Alternative we can define a type of Display_postulates which contains all pairs of DL_CL+LM  
postulates. However, we encounter an illegal operation. Please see below.*)

typedef DLDP  = "{(Consecution,Consecution)}"
  by auto


(*We now declare a new type called display equivalence without actually defining the type*)
typedecl display_equivalence 

(*What we trying to do in below inductive defintion is to experiment from a postulate can we 
define a equivalence. Which we encounter the same problem as DLDP*)
(*
inductive display_equivalence :: "Consecution \<Rightarrow> Consecution \<Rightarrow> bool" (infix "\<equiv>\<^sub>D" 100)
  where
intro: "X \<equiv>\<^sub>D  X"|
postulates:"(X ;\<^sub>A Y)\<turnstile>\<^sub>C Z \<equiv>\<^sub>D (X \<turnstile>\<^sub>C (\<sharp>Y ; Z ))"|
display: "X' \<turnstile>\<^sub>C Y'\<Longrightarrow> X \<turnstile>\<^sub>C Y \<Longrightarrow> (X' \<turnstile>\<^sub>C Y)\<equiv>\<^sub>D (X \<turnstile>\<^sub>C Y)"
*)

(*We trying to define logical and structual rules for DL. However, what we encounter is the same as 
above. We have a illegal operation, where  Structure cannot be used in Consecution. i.e. if Y is an 
Antecedent Structure, we cannot use Y again in Consequent Structure due to clash of type*)
*)

(* 6 Weeks of development
Untill now, we have come up a lot of infix symbol, we need to consider their precedence*)
end