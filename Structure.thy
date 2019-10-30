(*  Title:      structure.thy
    Author:     Tony Siu
*)

theory Structure
  imports Main BBI
begin

text \<open> We imported BBI formula definition in this thy file. And now we will be defining 
Structures for sequents and consecution\<close>

(* Substructure occureences in a structure X are classified as either positive or negative*)
datatype sign = positive | negative

(* With previous syntatic definition of BBI formula, we now defining a structure *)
datatype Structure =
(* A BBI formula is an atomic Structure *)
  formula  BBI_form
(* Define addictive Structural connectives *)
| AddNil                            ("\<emptyset>")            
| Sharp Structure                 ("\<sharp> _" 100)
| Semicolon Structure Structure   (infix ";" 101)
| RightArrow Structure Structure  (infix "\<Rightarrow>\<^sub>s" 101)
(* Define multiplicative Structural Connectives *)
| MultiNil                        ("\<oslash>")     
| Flat Structure                  ("\<flat> _" 100)
| Comma Structure Structure       (infix "," 101)
| DotArrow Structure Structure    (infix "\<comment>\<circ>" 101)

(* Following code is an idea to define what is valid for structures in logic \<LL>
N.B. a different style of definition from BBI. We try to investigate the best way to define a logic 
system. We do keep in mind the system has to be consistent.
*)
type_synonym valid = "Structure \<Rightarrow> Structure" ( "\<turnstile>")

(* Need to define Antecedent and Consequent meaning using sign datatype*)
datatype consecute = Antecedent Structure | Consequent Structure

end