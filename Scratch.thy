theory Scratch 
  imports Main DisplayCalculusBBI
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


text\<open>
theorem Soundness :
  assumes "\<P> (X \<turnstile>\<^sub>C Y)"
  shows "Valid (X \<turnstile>\<^sub>C Y)"
proof (rule Provable.induct)

  show "\<P> (X \<turnstile>\<^sub>C Y)" using assms by auto
next
  show "\<And>X. Valid (formulaA \<bottom>\<^sub>B \<turnstile>\<^sub>C X)"
    by (simp add: Bot)
next 
  show "\<And>X. \<P> (X \<turnstile>\<^sub>C \<emptyset>) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C \<emptyset>) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula \<bottom>\<^sub>B)"
    by simp
next
  show "\<And>X. \<P> (\<emptyset>\<^sub>A \<turnstile>\<^sub>C X) \<Longrightarrow> Valid (\<emptyset>\<^sub>A \<turnstile>\<^sub>C X) \<Longrightarrow> Valid (formulaA \<top>\<^sub>B \<turnstile>\<^sub>C X)" 
    by simp
next 
  show "\<And>X. Valid (X \<turnstile>\<^sub>C formula \<top>\<^sub>B)" 
    by (simp add: Top)
next 
  show "\<And>F X. \<P> (\<sharp>\<^sub>A (formula F) \<turnstile>\<^sub>C X) \<Longrightarrow>
           Valid (\<sharp>\<^sub>A (formula F) \<turnstile>\<^sub>C X) \<Longrightarrow> Valid (formulaA (\<not>\<^sub>B F) \<turnstile>\<^sub>C X)"
    by simp
next 
  show "\<And>X F. \<P> (X \<turnstile>\<^sub>C \<sharp> (formulaA F)) \<Longrightarrow>
           Valid (X \<turnstile>\<^sub>C \<sharp> (formulaA F)) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula (\<not>\<^sub>B F))"
    by auto
next 
  show "\<And>F X G.
       \<P> (formulaA F \<turnstile>\<^sub>C X) \<Longrightarrow>
       Valid (formulaA F \<turnstile>\<^sub>C X) \<Longrightarrow>
       \<P> (formulaA G \<turnstile>\<^sub>C X) \<Longrightarrow> Valid (formulaA G \<turnstile>\<^sub>C X) \<Longrightarrow> Valid (formulaA (F \<or>\<^sub>B G) \<turnstile>\<^sub>C X)"
    by (simp add: DisjE)
next 
  show "\<And>X F G. \<P> (X \<turnstile>\<^sub>C formula F ; formula G) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula F ; formula G) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula (F \<or>\<^sub>B G))"
    by simp
next 
  show "\<And>F G X. \<P> (formulaA F ;\<^sub>A formulaA G \<turnstile>\<^sub>C X) \<Longrightarrow> Valid (formulaA F ;\<^sub>A formulaA G \<turnstile>\<^sub>C X) \<Longrightarrow> Valid (formulaA (F \<and>\<^sub>B G) \<turnstile>\<^sub>C X)"
    by simp
next 
  show "\<And>X F G.
       \<P> (X \<turnstile>\<^sub>C formula F) \<Longrightarrow>
       Valid (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> \<P> (X \<turnstile>\<^sub>C formula G) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula G) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula (F \<and>\<^sub>B G))" 
    by (simp add: ConjI)
next
  show "\<And>X F G Y.
       \<P> (X \<turnstile>\<^sub>C formula F) \<Longrightarrow>
       Valid (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> \<P> (formulaA G \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (formulaA G \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (formulaA (F \<rightarrow>\<^sub>B G) \<turnstile>\<^sub>C \<sharp> X ; Y)"
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  show "\<And>X F G. \<P> (X ;\<^sub>A formulaA F \<turnstile>\<^sub>C formula G) \<Longrightarrow> Valid (X ;\<^sub>A formulaA F \<turnstile>\<^sub>C formula G) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula (F \<rightarrow>\<^sub>B G))"
    by (simp add: Imp)
next 
  show "\<And>X Y. \<P> (\<emptyset>\<^sub>A ;\<^sub>A X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (\<emptyset>\<^sub>A ;\<^sub>A X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y)" 
    using ConjE2 DisjI1 MP Valid.simps by blast
next 
  show "\<And>X Y. \<P> (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (\<emptyset>\<^sub>A ;\<^sub>A X \<turnstile>\<^sub>C Y)"
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  show "\<And>X Y. \<P> (X \<turnstile>\<^sub>C Y ; \<emptyset>) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y ; \<emptyset>) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y)"
    using ConjE1 DisjI2 MP Valid.simps by blast
next
  show "\<And>X Y. \<P> (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y ; \<emptyset>)"
    using ConjE2 DisjI1 MP Valid.simps by blast
next 
  show "\<And>W X Y Z. \<P> (W ;\<^sub>A (X ;\<^sub>A Y) \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (W ;\<^sub>A (X ;\<^sub>A Y) \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid ((W ;\<^sub>A X) ;\<^sub>A Y \<turnstile>\<^sub>C Z)"
    using ConjE1 DisjI2 MP Valid.simps by blast
next
  show "\<And>W X Y Z. \<P> ((W ;\<^sub>A X) ;\<^sub>A Y \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid ((W ;\<^sub>A X) ;\<^sub>A Y \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (W ;\<^sub>A (X ;\<^sub>A Y) \<turnstile>\<^sub>C Z)"
    using ConjE2 DisjI1 MP Valid.simps by blast
next 
  show "\<And>W X Y Z. \<P> (W \<turnstile>\<^sub>C (X ; Y) ; Z) \<Longrightarrow> Valid (W \<turnstile>\<^sub>C (X ; Y) ; Z) \<Longrightarrow> Valid (W \<turnstile>\<^sub>C X ; (Y ; Z))"
    using ConjE1 DisjI2 MP Valid.simps by blast
next
  show "\<And>W X Y Z. \<P> (W \<turnstile>\<^sub>C X ; (Y ; Z)) \<Longrightarrow> Valid (W \<turnstile>\<^sub>C X ; (Y ; Z)) \<Longrightarrow> Valid (W \<turnstile>\<^sub>C (X ; Y) ; Z)"
    using ConjE1 DisjI2 MP Valid.simps by blast
next
  show "\<And>X Z Y. \<P> (X \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X ;\<^sub>A Y \<turnstile>\<^sub>C Z)"
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  show "\<And>X Z Y. \<P> (X \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y ; Z)"
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  show "\<And>X Y. \<P> (X ;\<^sub>A X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (X ;\<^sub>A X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y)"
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  show "\<And>X Y. \<P> (X \<turnstile>\<^sub>C Y ; Y) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y ; Y) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y)"
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  show "\<And>X. \<P> (\<oslash> \<turnstile>\<^sub>C X) \<Longrightarrow> Valid (\<oslash> \<turnstile>\<^sub>C X) \<Longrightarrow> Valid (formulaA \<top>\<^sup>*\<^sub>B \<turnstile>\<^sub>C X)"
    by simp
next
  show "\<And>F G X. \<P> (formulaA F ,\<^sub>A formulaA G \<turnstile>\<^sub>C X) \<Longrightarrow> Valid (formulaA F ,\<^sub>A formulaA G \<turnstile>\<^sub>C X) \<Longrightarrow> Valid (formulaA (F *\<^sub>B G) \<turnstile>\<^sub>C X)"
    by simp
next
  show "\<And>X F G Y.
       \<P> (X \<turnstile>\<^sub>C formula F) \<Longrightarrow>
       Valid (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> \<P> (formulaA G \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (formulaA G \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (formulaA (F \<rightarrow>\<^emph>\<^sub>B G) \<turnstile>\<^sub>C X \<rightarrow>\<circ> Y)"
    using ConjE2 DisjI1 MP Valid.simps by blast
next 
  show "Valid (\<oslash> \<turnstile>\<^sub>C formula \<top>\<^sup>*\<^sub>B)"
    by (simp add: Ax)
next 
  show "\<And>X F Y G.
       \<P> (X \<turnstile>\<^sub>C formula F) \<Longrightarrow>
       Valid (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> \<P> (Y \<turnstile>\<^sub>C formula G) \<Longrightarrow> Valid (Y \<turnstile>\<^sub>C formula G) \<Longrightarrow> Valid (X ,\<^sub>A Y \<turnstile>\<^sub>C formula (F *\<^sub>B G))"
    by (simp add: ConjIstar)
next
  show "\<And>X F G. \<P> (X ,\<^sub>A formulaA F \<turnstile>\<^sub>C formula G) \<Longrightarrow> Valid (X ,\<^sub>A formulaA F \<turnstile>\<^sub>C formula G) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula (F \<rightarrow>\<^emph>\<^sub>B G))"
    by (simp add: Impstar)
next
  show "\<And>X Y. \<P> (\<oslash> ,\<^sub>A X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (\<oslash> ,\<^sub>A X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y)"
    using ConjE1 DisjI2 MP Valid.simps by blast
next 
  show "\<And>X Y. \<P> (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (\<oslash> ,\<^sub>A X \<turnstile>\<^sub>C Y)"
    using ConjE1 DisjI2 MP Valid.simps by blast
next 
  show "\<And>W X Y Z. \<P> (W ,\<^sub>A (X ,\<^sub>A Y) \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (W ,\<^sub>A (X ,\<^sub>A Y) \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid ((W ,\<^sub>A X) ,\<^sub>A Y \<turnstile>\<^sub>C Z)"
    using ConjE2 DisjI1 MP Valid.simps by blast
next
  show "\<And>W X Y Z. \<P> ((W ,\<^sub>A X) ,\<^sub>A Y \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid ((W ,\<^sub>A X) ,\<^sub>A Y \<turnstile>\<^sub>C Z) \<Longrightarrow> Valid (W ,\<^sub>A (X ,\<^sub>A Y) \<turnstile>\<^sub>C Z)"
    using ConjE1 DisjI2 MP Valid.simps by blast
next
  show "\<And>X F Y. \<P> (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C formula F) \<Longrightarrow> \<P> (formulaA F \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (formulaA F \<turnstile>\<^sub>C Y) \<Longrightarrow> Valid (X \<turnstile>\<^sub>C Y)"
    using ConjE1 DisjI2 MP Valid.simps by blast
qed
\<close>

lemma display :
  assumes "ant_part (Inl Z) (X \<turnstile>\<^sub>C Y)"
  shows "(\<exists>W. ((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)))"
proof -
  from assms have "((pos (Inl Z) (Inl X)) \<or> (neg (Inl Z) (Inr Y)))" by simp
  have "(pos (Inl Z) (Inl X)) \<Longrightarrow> (\<exists>W. ((X \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z  \<turnstile>\<^sub>C W)))" 
  proof (rule displayEquiv.induct)
               defer
    show "\<And>Xa Y Za. pos (Inl Z) (Inl X) \<Longrightarrow> \<exists>W. (Xa \<turnstile>\<^sub>C \<sharp> Y ; Za) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)" 
      by (meson display_symm equiv)
  next
    show "\<And>Xa Y Za. pos (Inl Z) (Inl X) \<Longrightarrow> \<exists>W. (Y ;\<^sub>A Xa \<turnstile>\<^sub>C Za) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)"
      using display_symm equiv by blast
  next
    show "\<And>Xa Y Za. pos (Inl Z) (Inl X) \<Longrightarrow> \<exists>W. (Xa ;\<^sub>A \<sharp>\<^sub>A Y \<turnstile>\<^sub>C Za) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)"
      using display_symm equiv by blast
  next
    show "\<And>Xa Y Za. pos (Inl Z) (Inl X) \<Longrightarrow> \<exists>W. (Xa \<turnstile>\<^sub>C Za ; Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)"
      using display_symm equiv by blast
  next
    show "\<And>Xa Y. pos (Inl Z) (Inl X) \<Longrightarrow> \<exists>W. (\<sharp>\<^sub>A Y \<turnstile>\<^sub>C \<sharp> Xa) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)"
      using display_symm equiv by blast
  next 
    show "\<And>Y Xa. pos (Inl Z) (Inl X) \<Longrightarrow> \<exists>W. (\<sharp>\<^sub>A (\<sharp> Xa) \<turnstile>\<^sub>C Y) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)"
      using display_symm equiv by blast
  next
    show "\<And>Xa Y Za. pos (Inl Z) (Inl X) \<Longrightarrow> \<exists>W. (Xa \<turnstile>\<^sub>C Y \<rightarrow>\<circ> Za) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)"
      using display_symm equiv by blast
  next
    show "\<And>Xa Y Za. pos (Inl Z) (Inl X) \<Longrightarrow> \<exists>W. (Y ,\<^sub>A Xa \<turnstile>\<^sub>C Za) \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)" 
      using display_symm equiv by blast
  next
    show "\<And>C. pos (Inl Z) (Inl X) \<Longrightarrow> \<exists>W. C \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)"
      using display_symm equiv by blast
  next 
    show "\<And>C C'. pos (Inl Z) (Inl X) \<Longrightarrow> C \<equiv>\<^sub>D C' \<Longrightarrow> \<exists>W. C' \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W) \<Longrightarrow> \<exists>W. C \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)" 
      using display_trans by blast
  next 
    show "\<And>C C' C''. pos (Inl Z) (Inl X) \<Longrightarrow> C \<equiv>\<^sub>D C' \<Longrightarrow> \<exists>W. C' \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W) \<Longrightarrow> C' \<equiv>\<^sub>D C'' \<Longrightarrow> \<exists>W. C'' \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W) \<Longrightarrow> \<exists>W. C'' \<equiv>\<^sub>D (Z \<turnstile>\<^sub>C W)"
      by blast
  next 
    fix x
    show " pos (Inl Z) (Inl X) \<Longrightarrow> x \<equiv>\<^sub>D (X \<turnstile>\<^sub>C Y)"
      using display_symm equiv by blast
  qed
  show ?thesis 
    by (meson display_symm equiv)
qed

section "Notes"
text \<open> In this theory, we are defining syntax for Boolean BI formula and its rules and axioms.
The logic system is syntax and without any semantic at this level\<close>
text \<open>Initially, we define a variable which is indexed by natural number. 
In this way we can genereate/assuming  inifinte atomic proposition varaiables\<close>
text \<open>BBI is CL + IL. In our definition we include both syntax in the definition.
With inifinte proposition variables we can now define a BBI formula datatype.
It is a recursive definition which includes symbols (both prefix and infix).
The natural number next to the symbol indicate its precedence Isabell recommended range is >= 100\<close>
text \<open>Now we define axioms and rules for BBI-formula.
"inductive" keyword allows us to formalise a more readable proof system in Isabelle.
This is a common techique to define a Hilbert's style proof system as "BBI_form \<Rightarrow> BBI_form \<Rightarrow> bool"
isnt necessarily a semantic meaning"
In Isabelle, when defining an axioms, e.g.MP:  A -> B  ==> A  ==> B, it means that 
Assume A implies B is true and A is true will prove B is true.
Using this notation we can define a inductive proof system\<close>
text \<open>Apart from inductive keyword, other keywords are considerated: type_synonym, axiomatization, definition.
However, those methods seems not to help us to define the turnstile.
A pre-defined structural proof system is in Isabelle which is using notepad, assumes, fix and proof keywords.
But this does not help us to define local axioms.\<close>
text \<open>In here, we define an extra symbol: double turnstile as extra syntax.
The definition is based on the inductive definition of turnstile\<close>
text \<open> We imported BBI formula definition in this thy file. And now we will be defining 
Structure connectives and rules (A higher hierarchy abstract) for our display calculus\<close>
text \<open> We define structures in terms of Antecedent and consequent. This is done through mutual 
recursion dataype definition. As BBI is CL + LM, our connectives are based on DL of CL & LM.\<close>
text \<open> With basic definition of Antecedent Structure and Consequent Structure, we now define 
formula meaning in Structures. If we using the same datatype pattern for Antecedent and Consequent,
there will be a clash of type in Isabelle\<close>
text \<open>With above Structure definitions, we can now define Consecution which is a datatype that 
takes a pair of Antecedent and Consequent Structures in the syntax of X \<turnstile> Y\<close>
text \<open>Now we define a display calculius of BBI. We use an inductive definition to define Displaying.
i.e. Display equivalence. Our intro rules are Display Positulates for CL + LM. We also define this 
definition to be reflexive and transistive with symmetric Display Positulates.\<close> 
text \<open>We define the meaning of a valid Consecution is. X \<turnstile> Y is said to be valid iff  \<psi> X  \<turnstile> \<gamma> Y in logic \<L> \<close>

text \<open> We then define logical and Structural rules for our display calculus. We use the symbol \<P>
to show that the consecution is provable. 
Again we use an inductive definition for proving our future theorem\<close>

  


end