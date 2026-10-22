/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponentials of self-adjoint elements

Let `A` be a complete normed complex algebra with a continuous star structure and `h` a
self-adjoint element of `A`. The adjoint of the unitary `selfAdjoint.expUnitary h` is
`expUnitary (-h)`, `selfAdjoint.star_expUnitary`, whose underlying element is `exp (-(I • h))`.

Hence conjugation by `exp (izh)`, the inner dynamics of the Hamiltonian `h`, extends to an entire
function of the complex time `z`, `TauCeti.differentiable_exp_smul_mul_mul_exp_neg_smul`. This is
the exponential input to the inner dynamics of a bounded self-adjoint Hamiltonian.

## Main declarations

* `selfAdjoint.star_expUnitary`: the adjoint of `expUnitary`.
* `TauCeti.differentiable_exp_smul_mul_mul_exp_neg_smul`: `z ↦ exp (izh) a exp (-izh)` is entire.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second edition,
Section 2.5.3, for the one-parameter group `t ↦ exp (ith)` of a self-adjoint element.
-/

public section

noncomputable section

open Complex NormedSpace

namespace TauCeti

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- Conjugation by `exp (izh)` is an entire function of the complex time `z`:
`z ↦ exp (izh) a exp (-izh)`. -/
theorem differentiable_exp_smul_mul_mul_exp_neg_smul (h a : A) :
    Differentiable ℂ fun z : ℂ => exp ((I * z) • h) * a * exp (-(I * z) • h) := by
  have hd : Differentiable ℂ fun z : ℂ => exp (z • h) := differentiable_exp_smul_const (𝕂 := ℂ) h
  exact ((hd.comp (differentiable_id.const_mul I)).mul (differentiable_const a)).mul
    (hd.comp (differentiable_id.const_mul I).neg)

end TauCeti

namespace selfAdjoint

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- The adjoint of `expUnitary` is `expUnitary` of the negative. -/
@[simp]
theorem star_expUnitary (b : selfAdjoint A) : star (expUnitary b) = expUnitary (-b) := by
  rw [Unitary.star_eq_inv, inv_eq_of_mul_eq_one_right]
  rw [← Commute.expUnitary_add (Commute.refl (b : A)).neg_right, add_neg_cancel, expUnitary_zero]

end selfAdjoint
