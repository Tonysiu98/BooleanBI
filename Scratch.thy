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

(*UNION TYPE + https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2011-July/msg00116.html*)

inductive ev :: "nat \<Rightarrow> bool" where
ev0 : "ev 0"|
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"


fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True"|
"evn (Suc 0) = False"|
"evn (Suc(Suc n)) =  evn n"

lemma "ev n \<Longrightarrow> evn n"
proof(induction rule: ev.induct)
  case ev0 
  show ?case by simp
next
  case evSS
  thus ?case by simp
qed

lemma de_Morgan:
  assumes "\<not>(\<forall>x. P x)"
  shows "\<exists>x.\<not>P x"
proof (rule classical)
  assume "\<nexists>x.\<not>P x"
  have "\<forall>x. P x"
  proof
    fix x show "P x"
    proof (rule classical)
    assume "\<not> P x"
    then have "\<exists>x.\<not>P x" ..
    with \<open>\<nexists>x.\<not>P x\<close> show ?thesis by contradiction
    qed
  qed
  with \<open>\<not>(\<forall>x. P x)\<close> show ?thesis 
    by blast
qed

theorem Drinker's_Principle: "\<exists>x. drunk x --> (\<forall>x. drunk x)"
proof cases
  fix a assume "\<forall>x. drunk x"
  then have "drunk a --> (\<forall>x. drunk x)" ..
  then show ?thesis ..
next
  assume "\<not> (\<forall>x. drunk x)"
  then have "\<exists>x. \<not> drunk x" by (rule de_Morgan)
  then obtain a where a: "\<not> drunk a" ..
  have "drunk a --> (\<forall>x. drunk x)"
  proof
    assume "drunk a"
    with a show "\<forall>x. drunk x" by contradiction
  qed
  then show ?thesis ..
qed

(* Testing purpose *)
datatype testA = Q | sharp testB ("#")
and 
testB = R | percent testA ("%")

type_synonym testAB = "testA + testB"

fun sharps:: "testAB \<Rightarrow> bool" where
"sharps (Inr R) = True"|
"sharps (Inl (#x)) = False"

inductive \<F> :: "testAB \<Rightarrow> testAB \<Rightarrow> bool" where
"\<F> x x"|
"\<F> a y \<Longrightarrow> \<F> (Inl (sharp x)) y"|
"\<F> x y \<Longrightarrow> \<F> (Inl (sharp x)) y"

subsection\<open>Mutually Inductive Definitions\<close>

text\<open>
Just as there are datatypes defined by mutual recursion, there are sets defined
by mutual induction. As a trivial example we consider the even and odd
natural numbers:
\<close>

inductive_set
  Even :: "nat set" and
  Odd  :: "nat set"
where
  zero:  "0 \<in> Even"
| EvenI: "n \<in> Odd \<Longrightarrow> Suc n \<in> Even"
| OddI:  "n \<in> Even \<Longrightarrow> Suc n \<in> Odd"

text\<open>\noindent
The mutually inductive definition of multiple sets is no different from
that of a single set, except for induction: just as for mutually recursive
datatypes, induction needs to involve all the simultaneously defined sets. In
the above case, the induction rule is called @{thm[source]Even_Odd.induct}
(simply concatenate the names of the sets involved) and has the conclusion
@{text[display]"(?x \<in> Even \<longrightarrow> ?P ?x) \<and> (?y \<in> Odd \<longrightarrow> ?Q ?y)"}
If we want to prove that all even numbers are divisible by two, we have to
generalize the statement as follows:
\<close>

lemma "(m \<in> Even \<longrightarrow> 2 dvd m) \<and> (n \<in> Odd \<longrightarrow> 2 dvd (Suc n))"

apply(rule Even_Odd.induct)

(*<*)
  apply simp
 apply simp
apply(simp add: dvd_def)
apply(clarify)
apply(rule_tac x = "Suc k" in exI)
apply simp
done
(*>*)

(*
  assume "X = formulaA \<bottom>\<^sub>B" 
  have "\<P> (formulaA \<bottom>\<^sub>B \<turnstile>\<^sub>C Y)" sledgehammer
    by (simp add: BotL)
  then have "Valid(formulaA \<bottom>\<^sub>B \<turnstile>\<^sub>C Y)" 
    by (simp add: Bot)
  then have "\<P> (formulaA \<bottom>\<^sub>B \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid(formulaA \<bottom>\<^sub>B \<turnstile>\<^sub>C Y)" sledgehammer
    by blast
  then have "\<And>X. Valid (formulaA \<bottom>\<^sub>B \<turnstile>\<^sub>C X)" 
    by (simp add: Bot)

*)



end