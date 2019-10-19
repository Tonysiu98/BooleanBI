# Formalising The Boolean BI Display Calculus in Isabelle/HOL
Author: Tony Siu

## Project Aim
To formalise a display calculus proof system for the bunched logic Boolean BI in the 
proof assistant Isabelle/HOL, and to prove that system sound and complete with respect to its Hilbert axiomatisation.

### Definition of BBI-formula
Section "BBI formula"
We first define what is a propositional variable. A variable which is run over natural number to generate a infinite atomic proposition
With this definition we can define a recursive datatype called BBI_form where 

```
BBI :: prop | neg BBI | and BBI BBI| or BBI BBI| imply BBI BBI
```
This definition includes both addictive and multiplicative connectives



### Definition of BBI provable (A, B)

