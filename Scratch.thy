theory Scratch 
  imports Main
begin
text\<open>This Isabelle file is for logging purpose and practice\<close>
  


section "Practice proof"
(*
typedef three ="{0::nat,1,2}"
  apply(rule_tac x = 0 in exI)
  by simp

definition A :: three where "A \<equiv> Abs_three 0"
definition B :: three where "B \<equiv> Abs_three 1"
definition C :: three where "C \<equiv> Abs_three 2"

lemma"A \<noteq> B \<and> B \<noteq> A \<and> A \<noteq> C \<and> C \<noteq> A \<and> B \<noteq> C \<and> C \<noteq> B"
  by (simp add: Abs_three_inject A_def B_def C_def)

lemma three_cases : "\<lbrakk>Y A ; Y B; Y C\<rbrakk> \<Longrightarrow> Y x"
  apply(induct_tac x)
  apply auto
  apply (auto simp add: A_def B_def C_def)
  done
*)
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


subsection\<open>Mutually Inductive Definitions\<close>

text\<open>
Just as there are datatypes defined by mutual recursion, there are sets defined
by mutual induction. As a trivial example we consider the even and odd
natural numbers:
\<close>
(*
inductive_set
  Even :: "nat set" and
  Odd  :: "nat set"
where
  zero:  "0 \<in> Even"
| EvenI: "n \<in> Odd \<Longrightarrow> Suc n \<in> Even"
| OddI:  "n \<in> Even \<Longrightarrow> Suc n \<in> Odd"




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

*)

lemma  "A \<longrightarrow> B \<Longrightarrow> \<not>A \<or> B"
proof -
  assume "A \<longrightarrow> B"
  have "\<not>\<not>(\<not>A \<or> B)"
  proof
    assume "\<not>(\<not>A \<or> B)"
    have "\<not>\<not> A"
    proof
      assume "\<not> A"
      show False
      proof - 
        have "\<not>A \<or> B" 
          by (simp add: \<open>\<not> A\<close>)
        show False 
          using \<open>\<not> (\<not> A \<or> B)\<close> \<open>\<not> A\<close> by auto
      qed
    qed
    from \<open>\<not>\<not> A\<close> have A by blast
    then have B using \<open>A \<longrightarrow> B\<close> by blast
    hence "\<not>A \<or> B" by (rule disjI2)
    thus False using \<open>\<not> (\<not> A \<or> B)\<close> by blast
  qed
  then have "\<not>A \<or> B" using \<open>\<not>\<not>(\<not>A \<or> B)\<close> by blast
  thus ?thesis 
    by blast
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


inductive Even :: "nat \<Rightarrow> bool" where
  zero: "Even 0"
| double: "Even (2 * n)" if "Even n" for n

thm Even.induct
print_statement Even.induct

lemma "Even n \<Longrightarrow>  2 dvd n"
proof (induct rule: Even.induct)
case zero
then show ?case by auto
next
  case (double n)
  then show ?case
    by simp
qed



end