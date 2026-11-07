/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import TauCeti.Algebra.Lie.Killing.DualBasis
public import TauCeti.Algebra.Lie.GeneralLinear.Radical
public import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# The Killing form of `sl₂`

The Killing form of `sl (Fin 2) R` is four times the trace form of the standard representation, so
on the standard basis `e = E₀₁`, `f = E₁₀`, `h = E₀₀ - E₁₁` its nonzero values are `κ(e, f) = 4` and
`κ(h, h) = 8`. Over a field of characteristic zero the basis dual to `(e, f, h)` is therefore
`(f / 4, e / 4, h / 8)`; this fixes the normalization of the Casimir element of `sl₂`.

## Main results

* `TauCeti.killingForm_slFinTwo_apply`: `κ(x, y) = 4 tr(x y)`.
* `TauCeti.killingForm_slFinTwoBasis`: the values of the Killing form on the standard basis.
* `TauCeti.killingDualBasis_slFinTwoBasis`: the Killing-dual of the standard basis.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5.1.
-/

public section

open LieAlgebra LieModule

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {R : Type*} [CommRing R]

/-- **The Killing form of `sl₂`** is four times the trace form of the standard representation. -/
theorem killingForm_slFinTwo_apply (x y : SpecialLinear.sl (Fin 2) R) :
    killingForm R (SpecialLinear.sl (Fin 2) R) x y = 4 * (x.val * y.val).trace := by
  rw [killingForm, LieModule.traceForm_apply_apply,
    LinearMap.trace_eq_matrix_trace R (Module.Basis.ofEquivFun (slFinTwoEquivFun R)),
    Matrix.trace_fin_three]
  simp only [LinearMap.toMatrix_apply, Module.Basis.ofEquivFun_repr_apply, LinearMap.comp_apply,
    LieModule.toEnd_apply_apply, slFinTwoEquivFun_apply]
  -- The trace is now a sum of three matrix entries of double brackets; expand them.
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Module.Basis.ofEquivFun,
    LieRing.of_associative_ring_bracket, Matrix.vecMul, dotProduct]
  ring

/-- The Killing form on the standard basis `(e, f, h)` of `sl₂`: `κ(e, f) = κ(f, e) = 4`,
`κ(h, h) = 8`, and all other pairings vanish. -/
theorem killingForm_slFinTwoBasis (i j : Fin 3) :
    killingForm R (SpecialLinear.sl (Fin 2) R) (slFinTwoBasis R i) (slFinTwoBasis R j) =
      ![![0, 4, 0], ![4, 0, 0], ![0, 0, 8]] i j := by
  rw [killingForm_slFinTwo_apply, slFinTwoBasis_apply, slFinTwoBasis_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

end CommRing

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The Killing-dual of the standard basis `(e, f, h)` of `sl₂` is `(f / 4, e / 4, h / 8)`. -/
theorem killingDualBasis_slFinTwoBasis :
    ⇑(killingDualBasis (slFinTwoBasis K)) = ![(4 : K)⁻¹ • slFinTwoBasis K 1,
      (4 : K)⁻¹ • slFinTwoBasis K 0, (8 : K)⁻¹ • slFinTwoBasis K 2] := by
  have key (j : Fin 3) := LinearMap.BilinForm.sum_apply_smul_dualBasis
    (LieAlgebra.IsKilling.killingForm_nondegenerate K _) (slFinTwoBasis K) (slFinTwoBasis K j)
  simp only [Fin.sum_univ_three, killingForm_slFinTwoBasis] at key
  have h₀ := key 1
  have h₁ := key 0
  have h₂ := key 2
  simp only [Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    Matrix.cons_val, zero_smul, zero_add, add_zero] at h₀ h₁ h₂
  funext i
  fin_cases i
  · simpa using (eq_inv_smul_iff₀ (OfNat.ofNat_ne_zero (R := K) 4)).mpr h₀
  · simpa using (eq_inv_smul_iff₀ (OfNat.ofNat_ne_zero (R := K) 4)).mpr h₁
  · simpa using (eq_inv_smul_iff₀ (OfNat.ofNat_ne_zero (R := K) 8)).mpr h₂

end Field

end TauCeti
