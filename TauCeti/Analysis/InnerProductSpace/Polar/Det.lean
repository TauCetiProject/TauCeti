/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import TauCeti.Analysis.InnerProductSpace.Spectrum

/-!
# The determinant of the polar factor

Let `T = U |T|` be the polar decomposition of an endomorphism `T` of a finite-dimensional real
inner product space. If `T` is injective, the polar factor `U` is an isometry, so `det U = ±1`,
and the modulus `|T|` is positive, so `det |T| > 0`. Otherwise `U` has the same nonzero kernel
as `T`, so both determinants vanish. In either case the sign of `det T` is `det U`: the polar
factor preserves orientation exactly when `T` does.

For a matrix `A` this says that `A (Aᵀ A)^{-1/2}` lies in the special orthogonal group exactly
when `det A > 0`. This is the form in which the orthogonal part of the linearized change between
two coordinate systems records whether they induce the same orientation.

## Main results

* `ContinuousLinearMap.det_polarFactor_mul_det_modulus`: `det U * det |T| = det T`.
* `ContinuousLinearMap.abs_det_polarFactor`: `|det U| = 1` for injective `T`.
* `ContinuousLinearMap.det_polarFactor_eq_sign`: `det U` is the sign of `det T`.
* `ContinuousLinearMap.det_polarFactor_eq_one_iff`: `det U = 1 ↔ 0 < det T`.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 7.3.1.
-/

public section

open Function

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {T : E →L[ℝ] E}

variable (T) in
/-- The determinant is multiplicative along the polar decomposition `T = U |T|`. -/
theorem det_polarFactor_mul_det_modulus : T.polarFactor.det * T.modulus.det = T.det := by
  conv_rhs => rw [← T.polarFactor_comp_modulus]
  exact (LinearMap.det_comp _ _).symm

/-- The polar factor of an injective endomorphism is an isometry, so its determinant has
absolute value one. -/
theorem abs_det_polarFactor (hT : Injective T) : |T.polarFactor.det| = 1 := by
  let U : E →ₗᵢ[ℝ] E :=
    { toLinearMap := T.polarFactor.toLinearMap
      norm_map' := T.norm_polarFactor_apply_of_injective hT }
  rw [ContinuousLinearMap.det, ← LinearMap.normDet_eq_abs_det]
  exact U.normDet_eq_one

/-- The determinant of the polar factor of an endomorphism is the sign of its determinant. -/
theorem det_polarFactor_eq_sign : T.polarFactor.det = SignType.sign T.det := by
  by_cases hT : Injective T
  swap
  · have hker : T.ker ≠ ⊥ := mt LinearMap.ker_eq_bot.1 hT
    have h0 : T.det = 0 := LinearMap.det_eq_zero_iff_ker_ne_bot.2 hker
    have h1 : T.polarFactor.det = 0 :=
      LinearMap.det_eq_zero_iff_ker_ne_bot.2 (T.ker_polarFactor ▸ hker)
    simp [h0, h1]
  have hP : 0 < T.modulus.det :=
    T.isPositive_modulus.toLinearMap.det_pos (T.ker_modulus.trans (LinearMap.ker_eq_bot.2 hT))
  rw [← T.det_polarFactor_mul_det_modulus, sign_mul, sign_pos hP, mul_one]
  rcases (abs_eq zero_le_one).1 (abs_det_polarFactor hT) with h | h <;> simp [h]

/-- The polar factor of an endomorphism has determinant one exactly when the endomorphism
preserves orientation. -/
theorem det_polarFactor_eq_one_iff : T.polarFactor.det = 1 ↔ 0 < T.det := by
  rw [det_polarFactor_eq_sign]
  rcases lt_trichotomy T.det 0 with h | h | h
  · norm_num [sign_neg h, h.not_gt]
  · simp [h]
  · simp [sign_pos h, h]

end ContinuousLinearMap
