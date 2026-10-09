/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Multiplication by `i` on a complex seminormed space

Multiplication by `i` is a real continuous linear automorphism of any complex seminormed space, with
inverse multiplication by `-i`.  It is the conjugating operator by which complex linearity of a
real-linear map is tested.

## Main definitions and results

* `Complex.I_smul_neg_I_smul` and `Complex.neg_I_smul_I_smul`: multiplication by `i` and by `-i`
  are mutually inverse on any type with a complex multiplication action.
* `Complex.smulIEquiv`: multiplication by `i` as a real continuous linear equivalence, with
  `smulIEquiv_apply` and `smulIEquiv_symm_apply`.
* `ContinuousLinearMap.conj_smul_apply_one_add_I_smul_apply_I`: for a real continuous linear map
  `L` from `ℂ`, the defect `e ↦ L e + i • L (i * e)` from complex linearity is `conj e` times its
  value `L 1 + i • L i` at `1`.
-/

public section

namespace Complex

section MulAction

variable {X : Type*} [MulAction ℂ X]

theorem I_smul_neg_I_smul (x : X) : I • (-I • x) = x := by
  rw [smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]

theorem neg_I_smul_I_smul (x : X) : -I • (I • x) = x := by
  rw [smul_smul, neg_mul, I_mul_I, neg_neg, one_smul]

end MulAction

section Seminormed

variable (X : Type*) [SeminormedAddCommGroup X] [NormedSpace ℂ X]

/-- Multiplication by `i` as a real continuous linear equivalence of a complex seminormed space. -/
noncomputable def smulIEquiv : X ≃L[ℝ] X :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 I I_ne_zero)

variable {X}

@[simp]
theorem smulIEquiv_apply (x : X) : smulIEquiv X x = I • x := by
  simp [smulIEquiv, Units.smul_def]

@[simp]
theorem smulIEquiv_symm_apply (x : X) : (smulIEquiv X).symm x = -I • x := by
  rw [ContinuousLinearEquiv.symm_apply_eq, smulIEquiv_apply, I_smul_neg_I_smul]

end Seminormed

end Complex

namespace ContinuousLinearMap

open Complex ComplexConjugate

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]

/-- Rotating `L 1 + I • L I` by the conjugate of `e` gives the derivative of `L` along `e` plus
`I` times its derivative along `I * e`: the map `e ↦ L e + I • L (I * e)` is conjugate-linear. For
`L` the derivative of a map `u` at `w + r e^{iθ}` and `e = e^{iθ}`, these are the radial derivative
and `r⁻¹` times the angular derivative of `(r, θ) ↦ u (w + r e^{iθ})`. -/
theorem conj_smul_apply_one_add_I_smul_apply_I (L : ℂ →L[ℝ] F) (e : ℂ) :
    conj e • (L 1 + I • L I) = L e + I • L (I * e) := by
  have hL : ∀ z : ℂ, L z = (z.re : ℂ) • L 1 + (z.im : ℂ) • L I := fun z => by
    have hz : z = z.re • (1 : ℂ) + z.im • I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]
  have he : conj e = (e.re : ℂ) - e.im * I := by
    apply Complex.ext <;> simp
  rw [hL e, hL (I * e), he]
  simp only [mul_re, I_re, I_im, mul_im, zero_mul, one_mul, zero_sub, zero_add, ofReal_neg]
  match_scalars
  · ring
  · linear_combination -(e.im : ℂ) * I_sq

end ContinuousLinearMap

end
