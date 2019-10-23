# Formalising The Boolean BI Display Calculus in Isabelle/HOL
Author: Tony Siu

## Project Aim
To formalise a display calculus proof system for the bunched logic Boolean BI in the 
proof assistant Isabelle/HOL, and to prove that system sound and complete with respect to its Hilbert axiomatisation.

### Definition of BBI-formula
Section "BBI formula definition" BBI.thy

In this section we define a variable which is indexed by natural numbers to generate infinite proposition variables.
With this definition we can define a recursive datatype called BBI_form where 

```
BBI :: Truth | Falsity | Prop | neg BBI | and BBI BBI| or BBI BBI| imply BBI BBI
```
This simple definition includes both addictive and multiplicative connectives


### Classical Logic and Lambek Multiplicative Logic Axioms and rules
Section "Axioms and Rules" BBI.thy 

In this section, we are using Isabelle auto prover and blast rule to prove both CL & LM 's axioms and rules. Since we have transform our BBI_form to a Boolean type, we can apple HOL rules to all the lemmas. Isabelle/HOL imports Isabelle/FOL which defines First order logic axioms and rules. FOL is based on Classical logic. Hence, the rules are helpful for our theorem prover.

### BBI-formula provables
Section ?
