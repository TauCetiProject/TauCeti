/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Weighted bounds and integrability of Schwartz functions

A Schwartz function is bounded and decays faster than any power. Pointwise, it absorbs any
polynomial weight `⟨c x⟩ ^ m = (1 + ‖c x‖²) ^ (m / 2)` and still decays like `(1 + ‖x‖) ^ (-k)`.
Consequently `‖x‖ ^ k ‖f x‖²` is
integrable against any measure of temperate growth. This is the integrability input for weighted
`L²` estimates such as the weighted Plancherel identity. Likewise the pointwise inner product of two
Schwartz functions is integrable, which justifies splitting `L²` pairings of Schwartz functions.

## Main declarations

* `SchwartzMap.one_add_norm_smul_sq_rpow_mul_norm_le`: `⟨c x⟩ ^ m ‖f x‖` is bounded by a finite
  supremum of Schwartz seminorms of `f` times `(1 + ‖x‖) ^ (-k)`.
* `SchwartzMap.integrable_norm_pow_mul_norm_sq`: `‖x‖ ^ k ‖f x‖²` is integrable.
* `SchwartzMap.integrable_inner`: `⟪f x, g x⟫` is integrable.
* `SchwartzMap.integral_norm_sq_eq_zero_iff`: a Schwartz function vanishes exactly when the
  integral of its squared norm does, for a measure charging every nonempty open set.
-/

public section

open MeasureTheory

namespace SchwartzMap

open scoped SchwartzMap InnerProductSpace

section Weight

variable {𝕜 E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- A Schwartz function absorbs the polynomial weight `⟨c x⟩ ^ m = (1 + ‖c x‖²) ^ (m / 2)` and
still decays like `(1 + ‖x‖) ^ (-k)`, with a constant given by a finite supremum of Schwartz
seminorms. -/
theorem one_add_norm_smul_sq_rpow_mul_norm_le (c m : ℝ) (k : ℕ) (f : 𝓢(E, F)) (x : E) :
    (1 + ‖c • x‖ ^ 2) ^ (m / 2) * ‖f x‖ ≤
      max 1 |c| ^ ⌈m⌉₊ * 2 ^ (⌈m⌉₊ + k) *
        (Finset.Iic (⌈m⌉₊ + k, 0)).sup (fun n ↦ SchwartzMap.seminorm 𝕜 n.1 n.2) f *
        (1 + ‖x‖) ^ (-(k : ℝ)) := by
  set K := ⌈m⌉₊
  set S := (Finset.Iic (K + k, 0)).sup (fun n ↦ SchwartzMap.seminorm 𝕜 n.1 n.2) f
  set t := ‖c • x‖
  have ht : t = |c| * ‖x‖ := by
    simp [t, norm_smul]
  have hx : 0 < 1 + ‖x‖ := by positivity
  -- The bracket of order `m` is dominated by a polynomial weight of degree `K = ⌈m⌉₊`.
  have hweight : (1 + t ^ 2) ^ (m / 2) ≤ max 1 |c| ^ K * (1 + ‖x‖) ^ K := by
    calc (1 + t ^ 2) ^ (m / 2) ≤ (1 + t ^ 2) ^ ((K : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith)
            (by gcongr; exact Nat.le_ceil m)
      _ ≤ ((1 + t) ^ 2) ^ ((K : ℝ) / 2) := by
          gcongr
          nlinarith [norm_nonneg (c • x)]
      _ = (1 + t) ^ K := by
          rw [← Real.rpow_natCast (1 + t) 2, ← Real.rpow_mul (by positivity),
            show ((2 : ℕ) : ℝ) * ((K : ℝ) / 2) = (K : ℝ) by push_cast; ring, Real.rpow_natCast]
      _ ≤ (max 1 |c| * (1 + ‖x‖)) ^ K := by
          gcongr
          rw [ht]
          nlinarith [le_max_left 1 |c|, le_max_right 1 |c|, norm_nonneg x]
      _ = max 1 |c| ^ K * (1 + ‖x‖) ^ K := mul_pow _ _ _
  -- The Schwartz function decays like `(1 + ‖x‖) ^ (-(K + k))`.
  have hdecay : (1 + ‖x‖) ^ (K + k) * ‖f x‖ ≤ 2 ^ (K + k) * S := by
    simpa using f.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (K + k, 0)) le_rfl le_rfl x
  have hsplit : (1 + ‖x‖) ^ K = (1 + ‖x‖) ^ (-(k : ℝ)) * (1 + ‖x‖) ^ (K + k) := by
    rw [Real.rpow_neg hx.le, Real.rpow_natCast, pow_add]
    field_simp
  calc (1 + t ^ 2) ^ (m / 2) * ‖f x‖ ≤ max 1 |c| ^ K * (1 + ‖x‖) ^ K * ‖f x‖ := by gcongr
    _ = max 1 |c| ^ K * (1 + ‖x‖) ^ (-(k : ℝ)) * ((1 + ‖x‖) ^ (K + k) * ‖f x‖) := by
        rw [hsplit]; ring
    _ ≤ max 1 |c| ^ K * (1 + ‖x‖) ^ (-(k : ℝ)) * (2 ^ (K + k) * S) := by gcongr
    _ = _ := by ring

end Weight

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.HasTemperateGrowth]

/-- For a Schwartz function `f`, the function `‖x‖ ^ k ‖f x‖²` is integrable. -/
theorem integrable_norm_pow_mul_norm_sq (f : 𝓢(E, F)) (k : ℕ) :
    Integrable (fun x ↦ ‖x‖ ^ k * ‖f x‖ ^ 2) μ := by
  refine ((f.integrable_pow_mul μ k).const_mul (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    (by fun_prop) (.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), sq, ← mul_assoc, mul_comm _ ‖f x‖]
  gcongr
  exact f.norm_le_seminorm ℝ x

/-- A Schwartz function vanishes if and only if the integral of its squared norm does, against a
measure of temperate growth that charges every nonempty open set. -/
theorem integral_norm_sq_eq_zero_iff [μ.IsOpenPosMeasure] {f : 𝓢(E, F)} :
    ∫ x, ‖f x‖ ^ 2 ∂μ = 0 ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hint : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    simpa using f.integrable_norm_pow_mul_norm_sq (μ := μ) 0
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖f x‖) hint).mp h
  have hcont : Continuous fun x => ‖f x‖ ^ 2 := by fun_prop
  have := (hcont.ae_eq_iff_eq μ continuous_zero).mp hae
  exact SchwartzMap.ext fun x => by simpa using congrFun this x

/-- For Schwartz functions `f` and `g` with values in a real inner product space, the pointwise
inner product `⟪f x, g x⟫` is integrable. -/
theorem integrable_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f g : 𝓢(E, H)) : Integrable (fun x ↦ ⟪f x, g x⟫_ℝ) μ := by
  convert (pairing (innerSL ℝ) f g).integrable (μ := μ) using 1
  ext x
  rw [pairing_apply_apply, innerSL_apply_apply]

end SchwartzMap
