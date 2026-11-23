/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.Analysis.PositiveDefinite.Kernel.Bounds
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
* `Matrix.PosSemidef.sq_div_eight_le_one_sub_re_inv_mul_mul`: quantitative `ε² / 8` lower bound on
  `1 - re (φ (a⁻¹ * g * b))` when `φ` is close to `1` at `a` and `b` and separated from `1` at `g`.

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
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), hφ.norm_kolmogorovFeature_sub_sq a b]
    simp only [of_apply, inv_mul_cancel]
    have hmul :
        RCLike.re (φ 1) - 2 * RCLike.re (φ (a⁻¹ * b)) + RCLike.re (φ 1) =
          2 * (RCLike.re (φ 1) - RCLike.re (φ (a⁻¹ * b))) := by ring
    rw [hmul, Real.sqrt_mul (by norm_num)]
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

/-- For a normalized positive-definite function `φ : G → 𝕜`, if `‖φ a - 1‖ ≤ ε ^ 2 / 32`,
`‖φ b - 1‖ ≤ ε ^ 2 / 32`, and `ε ≤ ‖φ g - 1‖` with `0 ≤ ε`, then
`ε ^ 2 / 8 ≤ 1 - re (φ (a⁻¹ * g * b))`. -/
theorem sq_div_eight_le_one_sub_re_inv_mul_mul {φ : G → 𝕜}
    (hφ : (of fun x y : G ↦ φ (x⁻¹ * y)).PosSemidef) (h1 : φ 1 = 1)
    {a g b : G} {ε : ℝ} (hε : 0 ≤ ε)
    (ha : ‖φ a - 1‖ ≤ ε ^ 2 / 32) (hb : ‖φ b - 1‖ ≤ ε ^ 2 / 32)
    (hg : ε ≤ ‖φ g - 1‖) :
    ε ^ 2 / 8 ≤ 1 - RCLike.re (φ (a⁻¹ * g * b)) := by
  let u : ℝ := Real.sqrt (ε ^ 2 / 32)
  have hu2 : u ^ 2 = ε ^ 2 / 32 := Real.sq_sqrt (by positivity)
  have htri := hφ.le_sqrt_re_one_sub_re_inv_mul_mul a g b
  simp only [h1, RCLike.one_re] at htri
  have hre_a : 1 - RCLike.re (φ a) ≤ ε ^ 2 / 32 :=
    le_trans (by simpa [norm_sub_rev] using RCLike.re_le_norm (1 - φ a)) ha
  have hre_b : 1 - RCLike.re (φ b) ≤ ε ^ 2 / 32 :=
    le_trans (by simpa [norm_sub_rev] using RCLike.re_le_norm (1 - φ b)) hb
  have hsq_g : (4 * u) ^ 2 ≤ 1 - RCLike.re (φ g) := by
    have hnorm : ‖φ g - 1‖ ^ 2 ≤ 2 * (1 - RCLike.re (φ g)) := hφ.norm_sub_one_sq_le h1 g
    have hε_sq : ε ^ 2 ≤ ‖φ g - 1‖ ^ 2 := pow_le_pow_left₀ hε hg 2
    nlinarith
  have hsqrt_g : 4 * u ≤ Real.sqrt (1 - RCLike.re (φ g)) := Real.le_sqrt_of_sq_le hsq_g
  have hsqrt_a : Real.sqrt (1 - RCLike.re (φ a)) ≤ u := Real.sqrt_le_sqrt hre_a
  have hsqrt_b : Real.sqrt (1 - RCLike.re (φ b)) ≤ u := Real.sqrt_le_sqrt hre_b
  have hsqrt_mid : 2 * u ≤ Real.sqrt (1 - RCLike.re (φ (a⁻¹ * g * b))) := by linarith
  have hsq_mid : (2 * u) ^ 2 ≤ (Real.sqrt (1 - RCLike.re (φ (a⁻¹ * g * b)))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsqrt_mid 2
  rw [Real.sq_sqrt (hφ.one_sub_re_nonneg h1 _)] at hsq_mid
  nlinarith

end Matrix.PosSemidef

end
