/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov

/-!
# Metric inequality for positive-definite functions on groups

For any positive-definite function `φ : G → 𝕜` on a group, valued in an `RCLike` field `𝕜`, the
Kolmogorov feature map satisfies `‖Φ a - Φ b‖² = 2 (re (φ 1) - re (φ (a⁻¹ * b)))`. Applying the
triangle inequality in the Kolmogorov Hilbert space gives subadditivity of
`g ↦ √(re (φ 1) - re (φ g))`.

## Main declarations

* `Matrix.PosSemidef.sqrt_re_one_sub_re_mul_le`: subadditivity (triangle inequality) of
  `g ↦ √(re (φ 1) - re (φ g))` for positive-definite functions on a group.
* `Matrix.PosSemidef.le_sqrt_re_one_sub_re_inv_mul_mul`: lower bound for
  `√(re (φ 1) - re (φ (a⁻¹ * g * b)))` in terms of `g`, `a`, and `b`.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §16.1.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Appendix C.
-/

public section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace Matrix.PosSemidef

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G]

/-- **Triangle inequality for positive-definite functions.** For any positive-definite function
`φ : G → 𝕜`, `g ↦ √(re (φ 1) - re (φ g))` is subadditive:
`√(re (φ 1) - re (φ (g * h))) ≤ √(re (φ 1) - re (φ g)) + √(re (φ 1) - re (φ h))`. -/
theorem sqrt_re_one_sub_re_mul_le {φ : G → 𝕜}
    (hφ : (of fun x y : G ↦ φ (x⁻¹ * y)).PosSemidef) (g h : G) :
    Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ (g * h))) ≤
      Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ g)) +
        Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ h)) := by
  have hdist (a b : G) :
      dist (hφ.kolmogorovFeature a) (hφ.kolmogorovFeature b) =
        Real.sqrt 2 * Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ (a⁻¹ * b))) := by
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _),
      hφ.norm_kolmogorovFeature_sub_sq_of_diag_eq (c := φ 1) (by simp) (by simp),
      of_apply, Real.sqrt_mul (by norm_num)]
  have htri := dist_triangle (hφ.kolmogorovFeature 1) (hφ.kolmogorovFeature g)
    (hφ.kolmogorovFeature (g * h))
  rw [hdist 1 (g * h), hdist 1 g, hdist g (g * h)] at htri
  simp only [inv_one, one_mul, inv_mul_cancel_left] at htri
  rw [← mul_add] at htri
  exact le_of_mul_le_mul_left htri (by positivity)

/-- **Double-translate displacement lower bound.** For any positive-definite function `φ : G → 𝕜`,
`√(re (φ 1) - re (φ g)) - √(re (φ 1) - re (φ a)) - √(re (φ 1) - re (φ b))` is at most
`√(re (φ 1) - re (φ (a⁻¹ * g * b)))`. -/
theorem le_sqrt_re_one_sub_re_inv_mul_mul {φ : G → 𝕜}
    (hφ : (of fun x y : G ↦ φ (x⁻¹ * y)).PosSemidef) (a g b : G) :
    Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ g)) -
        Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ a)) -
        Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ b)) ≤
      Real.sqrt (RCLike.re (φ 1) - RCLike.re (φ (a⁻¹ * g * b))) := by
  have htri₁ := hφ.sqrt_re_one_sub_re_mul_le (a * (a⁻¹ * g * b)) b⁻¹
  have htri₂ := hφ.sqrt_re_one_sub_re_mul_le a (a⁻¹ * g * b)
  have hinv : RCLike.re (φ b⁻¹) = RCLike.re (φ b) := by
    have h := congrArg RCLike.re (hφ.isHermitian.apply b 1).symm
    simpa [RCLike.star_def] using h
  have hprod : a * (a⁻¹ * g * b) * b⁻¹ = g := by group
  rw [hprod, hinv] at htri₁
  linarith

end Matrix.PosSemidef

end
