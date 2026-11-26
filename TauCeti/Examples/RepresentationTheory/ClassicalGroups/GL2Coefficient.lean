/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GL2Coefficient

/-!
# The coefficient `Sym²(Std)` of `GL₂` and its contragredient

Checks of `TauCeti.RepresentationTheory.ClassicalGroups.GL2Coefficient` on
`V_(2,0) = Sym²(Std)`: it has dimension three and scalar weight two, its contragredient has
scalar weight minus two and has its highest weight `(0, -2)` as a weight, and a determinant
twist `V_(a+m,b+m)` changes the scalar weight by `2 m`.
-/

public section

open Matrix Module

namespace TauCeti.Examples

variable {k : Type} [Field k]

/-- `Sym²(Std)` has dimension three. -/
example : finrank k (GL2CoefficientSpace k 2 0) = 3 := by
  have h := finrank_gl2CoefficientRep (k := k) (a := 2) (b := 0) (by norm_num)
  omega

/-- A scalar matrix `z` acts on `Sym²(Std)` by `z ^ 2`. -/
example (z : kˣ) (x : GL2CoefficientSpace k 2 0) :
    gl2CoefficientRep k 2 0 (GeneralLinearGroup.scalar (Fin 2) z) x = ((z ^ 2 : kˣ) : k) • x := by
  simpa using gl2CoefficientRep_scalar (by norm_num) z x

/-- A scalar matrix `z` acts on the contragredient of `Sym²(Std)` by `z ^ (-2)`. -/
example (z : kˣ) (f : Dual k (GL2CoefficientSpace k 2 0)) :
    (gl2CoefficientRep k 2 0).dual (GeneralLinearGroup.scalar (Fin 2) z) f =
      ((z ^ (-2 : ℤ) : kˣ) : k) • f := by
  simpa using gl2CoefficientRep_dual_scalar (by norm_num) z f

/-- `(0, -2)`, the highest weight of the contragredient of `Sym²(Std)`, is a weight of it, over
an infinite field. -/
example [Infinite k] :
    weightSpace (gl2CoefficientRep k 2 0).dual ![0, -2] ≠ ⊥ := by
  simpa using weightSpace_dual_gl2CoefficientRep_highest_ne_bot (k := k) weightChar_injective
    (a := 2) (b := 0) (by norm_num)

/-- A determinant twist `V_(a+m,b+m)` changes the scalar weight by twice its exponent. -/
example {a b : ℤ} (hab : b ≤ a) (m : ℤ) (z : kˣ) (x : GL2CoefficientSpace k (a + m) (b + m)) :
    gl2CoefficientRep k (a + m) (b + m) (GeneralLinearGroup.scalar (Fin 2) z) x =
      ((z ^ (a + b + 2 * m) : kˣ) : k) • x := by
  rw [gl2CoefficientRep_scalar (by omega)]
  congr 3
  ring

end TauCeti.Examples
