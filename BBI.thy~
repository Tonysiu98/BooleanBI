(*  Title:      BBI.thy
    Author:     Tony Siu
*)

theory BBI
  imports Main
begin

text \<open> In this theory, we are defining syntax for Boolean BI formula and its rules and axioms.
The logic system is syntax and without any semantic at this level\<close>

section "BBI formula definiton"

text \<open>Initially, we define a variable which is indexed by natural number. 
In this way we can genereate/assuming  inifinte atomic proposition varaiables\<close>

datatype atom = P nat

text \<open>BBI is CL + IL. In our definition we include both syntax in the definition.
With inifinte proposition variables we can now define a BBI formula datatype.
It is a recursive definition which includes symbols (both prefix and infix).
The natural number next to the symbol indicate its precedence Isabell recommended range is >= 100\<close>

datatype BBI_form = 
  Truth                     ("\<top>\<^sub>B")
  | Falsity                 ("\<bottom>\<^sub>B")
  | Mfalsity                ("\<top>\<^sup>*\<^sub>B")
  | Atom atom
  | Neg BBI_form            ("\<not>\<^sub>B _" 100)
  | Con BBI_form BBI_form   (infix "\<and>\<^sub>B" 101)
  | MCon BBI_form BBI_form  (infix "*\<^sub>B" 101)
  | Dis BBI_form BBI_form   (infix "\<or>\<^sub>B" 101)
  | Imp  BBI_form BBI_form  (infix "\<rightarrow>\<^sub>B" 101)
  | Mimp  BBI_form BBI_form (infix "\<rightarrow>\<^emph>\<^sub>B" 101)

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

section "BBI formula Axioms"

(* Initial attempt of turnstile, this includes both CL and LM*)
inductive turnstile_BBI :: "BBI_form \<Rightarrow> BBI_form \<Rightarrow> bool" (infix "\<turnstile>\<^sub>B" 55)
  where 
Ax : "F \<turnstile>\<^sub>B F"|
Top : "F \<turnstile>\<^sub>B \<top>\<^sub>B"|
Bot : "\<bottom>\<^sub>B \<turnstile>\<^sub>B F"|
Imp : "F \<and>\<^sub>B G \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B G \<rightarrow>\<^sub>B H"|
MP : "F \<turnstile>\<^sub>B G \<Longrightarrow> G \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B H"|
Notl: "(\<not>\<^sub>B F) \<turnstile>\<^sub>B F \<rightarrow>\<^sub>B \<bottom>\<^sub>B" |
Notr: "F \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>B (\<not>\<^sub>B F)"|
Notnot : "(\<not>\<^sub>B \<not>\<^sub>B F) \<turnstile>\<^sub>B F" |
ConjI : "F \<turnstile>\<^sub>B G \<Longrightarrow> F \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B G \<and>\<^sub>B H" |
DisjE : "F \<turnstile>\<^sub>B H \<Longrightarrow> G \<turnstile>\<^sub>B H \<Longrightarrow> F \<or>\<^sub>B G \<turnstile>\<^sub>B H"|
ConjE1 : "F \<and>\<^sub>B H \<turnstile>\<^sub>B F"|
ConjE2 : "F \<and>\<^sub>B H \<turnstile>\<^sub>B H" |
DisjI1 : "F \<turnstile>\<^sub>B F \<and>\<^sub>B H" |
DisjI2 : "H \<turnstile>\<^sub>B F \<and>\<^sub>B H"|
Topl : "(F *\<^sub>B \<top>\<^sup>*\<^sub>B) \<turnstile>\<^sub>B F"|
Topr : "F \<turnstile>\<^sub>B (F *\<^sub>B \<top>\<^sup>*\<^sub>B)"|
Impstar : "F *\<^sub>B G \<turnstile>\<^sub>B H \<Longrightarrow> F \<turnstile>\<^sub>B (G \<rightarrow>\<^emph>\<^sub>B H)"|
Assocl: "F *\<^sub>B (G *\<^sub>B H) \<turnstile>\<^sub>B (F *\<^sub>B G) *\<^sub>B H"|
Assocr: "(F *\<^sub>B G) *\<^sub>B H \<turnstile>\<^sub>B F *\<^sub>B (G *\<^sub>B H)"|
Comm : "(F *\<^sub>B G) \<turnstile>\<^sub>B (G *\<^sub>B F)"|
ConjIstar : "F1  \<turnstile>\<^sub>B G1 \<Longrightarrow> F2  \<turnstile>\<^sub>B G2 \<Longrightarrow> (F1 *\<^sub>B F2) \<turnstile>\<^sub>B (G1 *\<^sub>B G2)"

text \<open>In here, we define an extra symbol: double turnstile as extra syntax.
The definition is based on the inductive definition of turnstile\<close>

definition double_turnstile_CL :: "BBI_form \<Rightarrow> BBI_form \<Rightarrow> bool" (infix "\<stileturn>\<turnstile>\<^sub>B" 55)
  where " F \<stileturn>\<turnstile>\<^sub>B G \<equiv> (F \<turnstile>\<^sub>B G) \<and> (G \<turnstile>\<^sub>B F) "

end