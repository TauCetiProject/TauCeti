/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# The Cauchy–Schwarz inequality for interval integrals

For a function `g` on `[a, b]` whose square is integrable,
`∫ₐᵇ g ≤ √(b - a) √(∫ₐᵇ g²)` (`TauCeti.integral_le_sqrt_mul_sqrt_integral_sq`). This is the
estimate that turns an `L²` bound on a derivative into a uniform Hölder modulus of continuity
`|f(t₂) - f(t₁)| ≤ √(t₂ - t₁) ‖f'‖_{L²}`, as in the Sobolev embedding `W^{1,2} ⊆ C^{1/2}` in one
dimension.

It is the set-integral Cauchy–Schwarz inequality
`TauCeti.sq_setIntegral_le_measureReal_mul_setIntegral_sq` on `(a, b]`, restated for interval
integrals and with square roots taken.

Its consequence `TauCeti.integral_norm_sq_le_of_forall_norm_le_mul` passes from a pointwise bound
`‖w t‖ ≤ B ∫₀ᵈ ‖f‖` on `[0, d]` to the `L²` bound `∫₀ᵈ ‖w‖² ≤ d² B² ∫₀ᵈ ‖f‖²`, as used for the
`L²` estimates of linear differential equations.
-/

public section

open Set MeasureTheory

namespace TauCeti

/-- **The Cauchy–Schwarz inequality on an interval.** For a function `g` on `[a, b]` with `g²`
integrable, `∫ₐᵇ g ≤ √(b - a) √(∫ₐᵇ g²)`. -/
theorem integral_le_sqrt_mul_sqrt_integral_sq {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg2 : IntervalIntegrable (fun t ↦ g t ^ 2) volume a b) :
    ∫ t in a..b, g t ≤ √(b - a) * √(∫ t in a..b, g t ^ 2) := by
  have h := sq_setIntegral_le_measureReal_mul_setIntegral_sq (μ := volume) g (Ioc a b)
    measure_Ioc_lt_top.ne hg2.1
  rw [Real.volume_real_Ioc_of_le hab, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le hab] at h
  rw [← Real.sqrt_mul (sub_nonneg.2 hab)]
  exact Real.le_sqrt_of_sq_le h

/-- **From a pointwise to an `L²` bound.** If `‖w t‖ ≤ B ∫₀ᵈ ‖f‖` for every `t ∈ [0, d]`, then
`∫₀ᵈ ‖w‖² ≤ d² B² ∫₀ᵈ ‖f‖²`, by the Cauchy–Schwarz inequality `(∫₀ᵈ ‖f‖)² ≤ d ∫₀ᵈ ‖f‖²`. -/
theorem integral_norm_sq_le_of_forall_norm_le_mul {X : Type*} [NormedAddCommGroup X] {d B : ℝ}
    (hd : 0 ≤ d) {w f : ℝ → X} (hw : Continuous w) (hf : Continuous f)
    (h : ∀ t ∈ Icc 0 d, ‖w t‖ ≤ B * ∫ s in 0..d, ‖f s‖) :
    ∫ t in 0..d, ‖w t‖ ^ 2 ≤ d ^ 2 * B ^ 2 * ∫ t in 0..d, ‖f t‖ ^ 2 := by
  set F := ∫ s in 0..d, ‖f s‖
  have hCS : F ^ 2 ≤ d * ∫ s in 0..d, ‖f s‖ ^ 2 := by
    have h := TauCeti.sq_setIntegral_le_measureReal_mul_setIntegral_sq
      (μ := volume) (fun s ↦ ‖f s‖) (Ioc 0 d) measure_Ioc_lt_top.ne
      ((hf.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    rwa [Real.volume_real_Ioc_of_le hd, sub_zero, ← intervalIntegral.integral_of_le hd,
      ← intervalIntegral.integral_of_le hd] at h
  calc ∫ t in 0..d, ‖w t‖ ^ 2 ≤ ∫ _ in 0..d, (B * F) ^ 2 :=
        intervalIntegral.integral_mono_on hd ((hw.norm.pow 2).intervalIntegrable _ _)
          intervalIntegrable_const fun t ht ↦ pow_le_pow_left₀ (norm_nonneg _) (h t ht) 2
    _ = d * B ^ 2 * F ^ 2 := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ d * B ^ 2 * (d * ∫ s in 0..d, ‖f s‖ ^ 2) := by gcongr
    _ = d ^ 2 * B ^ 2 * ∫ s in 0..d, ‖f s‖ ^ 2 := by ring

end TauCeti
