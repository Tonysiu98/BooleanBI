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
inductive  keyword allows us to formalise a more readable proof system in Isabelle.
This is a common techique to define a Hilbert's style proof system as "=> bool isnt necessarily 
a semantic meaning"
In Isabelle, when defining an axioms, e.g.MP:  A -> B  ==> A  ==> B, it means that 
Assume A implies B is true and A is true will prove B is true.
Using this notation we can define a inductive proof system\<close>

subsection "IL + CL Axioms"

(* Initial attemp of turnstile *)
inductive turnstile_CL :: "BBI_form \<Rightarrow> BBI_form \<Rightarrow> bool" (infix "\<turnstile>\<^sub>c" 55)
  where 
Ax : "F \<turnstile>\<^sub>c F"|
Top : "F \<turnstile>\<^sub>c \<top>\<^sub>B"|
Bot : "\<bottom>\<^sub>B \<turnstile>\<^sub>c F"|
imp : "F \<and>\<^sub>B G \<turnstile>\<^sub>c H \<Longrightarrow> F \<turnstile>\<^sub>c G \<rightarrow>\<^sub>B H"|
MP : "F \<turnstile>\<^sub>c G \<Longrightarrow> G \<turnstile>\<^sub>c H \<Longrightarrow> F \<turnstile>\<^sub>c H"|
notl: "(\<not>\<^sub>B F) \<turnstile>\<^sub>c F \<rightarrow>\<^sub>B \<bottom>\<^sub>B" |
notr: "F \<rightarrow>\<^sub>B \<bottom>\<^sub>B \<turnstile>\<^sub>c (\<not>\<^sub>B F)"|
notnot : "(\<not>\<^sub>B \<not>\<^sub>B F) \<turnstile>\<^sub>c F" |
ConjI : "F \<turnstile>\<^sub>c G \<Longrightarrow> F \<turnstile>\<^sub>c H \<Longrightarrow> F \<turnstile>\<^sub>c G \<and>\<^sub>B H" |
DisjE : "F \<turnstile>\<^sub>c H \<Longrightarrow> G \<turnstile>\<^sub>c H \<Longrightarrow> F \<or>\<^sub>B G \<turnstile>\<^sub>c H"|
ConjE1 : "F \<and>\<^sub>B H \<turnstile>\<^sub>c F"|
ConjE2 : "F \<and>\<^sub>B H \<turnstile>\<^sub>c H" |
DisjI1 : "F \<turnstile>\<^sub>c F \<and>\<^sub>B H" |
DisjI2 : "H \<turnstile>\<^sub>c F \<and>\<^sub>B H"

text \<open>In here, we define an extra symbole: double turnstile for future usage.
The definition is based on the inductive definition of turnstile
\<close>

definition double_turnstile_CL :: "BBI_form \<Rightarrow> BBI_form \<Rightarrow> bool" (infix "\<stileturn>\<turnstile>\<^sub>c" 55)
  where "double_turnstile_CL F G \<equiv> (F \<turnstile>\<^sub>c G) \<and> (G \<turnstile>\<^sub>c F) "

subsection "LM axioms"

text \<open> LM axioms are defined using same techique from CL\<close>

inductive turnstile_LM ::"BBI_form \<Rightarrow> BBI_form \<Rightarrow> bool" (infix "\<turnstile>\<^sub>l" 55)
  where
Ax : "F \<turnstile>\<^sub>l F"|
Topl : "(F *\<^sub>B \<top>\<^sub>B) \<turnstile>\<^sub>l F"|
Topr : "F \<turnstile>\<^sub>l (F *\<^sub>B \<top>\<^sub>B)"|
imp : "F *\<^sub>B G \<turnstile>\<^sub>l H \<Longrightarrow> F \<turnstile>\<^sub>l (G \<rightarrow>\<^emph>\<^sub>B H)"|
MP : "F \<turnstile>\<^sub>l G \<Longrightarrow> G \<turnstile>\<^sub>l H \<Longrightarrow> F \<turnstile>\<^sub>l H"|
Assocl: "F *\<^sub>B (G *\<^sub>B H) \<turnstile>\<^sub>l (F *\<^sub>B G) *\<^sub>B H"|
Assocr: "(F *\<^sub>B G) *\<^sub>B H \<turnstile>\<^sub>l F *\<^sub>B (G *\<^sub>B H)"|
Comm : "(F *\<^sub>B G) \<turnstile>\<^sub>l (G *\<^sub>B F)"|
ConjI : "F1  \<turnstile>\<^sub>l G1 \<Longrightarrow> F2  \<turnstile>\<^sub>l G2 \<Longrightarrow> (F1 *\<^sub>B F2) \<turnstile>\<^sub>l (G1 *\<^sub>B G2)"

definition double_turnstile_LM :: "BBI_form \<Rightarrow> BBI_form \<Rightarrow> bool" (infix "\<stileturn>\<turnstile>\<^sub>l" 55)
  where "double_turnstile_LM F G \<equiv> (F \<turnstile>\<^sub>l G) \<and> (G \<turnstile>\<^sub>l F)"


end