/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Oscillatory

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.ExpDecay
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Laplace

/-!
# Abelian Laplace-moment limits for oscillatory functions

This file specializes the general Abelian Laplace-moment and Laplace-derivative theorems from
`TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Laplace` to functions locally integrable on
`[0, ∞)` satisfying `TauCeti.HasOscillatoryDecay c q α₀ f` with `c ≠ 0`, `1 ≤ q`, and
`0 < α₀ + q - 1`.

## Main results

* `TauCeti.HasOscillatoryDecay.integrableOn_exp_neg_mul_mul`: every locally integrable function on
  `[a, ∞)` satisfying `HasOscillatoryDecay c q α₀ f` has a Bochner-integrable Laplace integral on
  `(a, ∞)` for every `p > 0`.
* `TauCeti.HasOscillatoryDecay.tendsto_integral_exp_neg_mul_mul_pow_mul_nhdsGT_zero`:
  `∫ t in Ioi 0, exp (-(p * t)) * t ^ n * f t → n ! * iteratedTailIntegral f (n + 1) 0` as
  `p → 0⁺`.
* `TauCeti.HasOscillatoryDecay.tendsto_iteratedDeriv_integral_exp_neg_mul_mul_nhdsGT_zero`:
  `iteratedDeriv n (fun r ↦ ∫ t in Ioi 0, exp (-(r * t)) * f t) p →
    (-1) ^ n * n ! * iteratedTailIntegral f (n + 1) 0` as `p → 0⁺`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped Topology

namespace HasOscillatoryDecay

/-- Every locally integrable function on `[a, ∞)` satisfying `HasOscillatoryDecay c q α₀ f` has a
Bochner-integrable Laplace integral on `(a, ∞)` for every `p > 0`. -/
theorem integrableOn_exp_neg_mul_mul {c q α₀ a p : ℝ} {f : ℝ → ℝ}
    (hf : HasOscillatoryDecay c q α₀ f) (hloc : LocallyIntegrableOn f (Ici a)) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-(p * t)) * f t) (Ioi a) := by
  have hexp : f =O[atTop] fun t : ℝ ↦ Real.exp ((p / 2) * t) :=
    hf.isBigO_rpow_neg.trans (isLittleO_rpow_exp_pos_mul_atTop (-α₀) (half_pos hp)).isBigO
  have hIci := integrableOn_exp_neg_mul_of_isBigO_exp hloc hexp (half_lt_self hp)
  simpa only [neg_mul] using hIci.mono_set Ioi_subset_Ici_self

/-- **Oscillatory Abelian Laplace-moment theorem.** If `f` is locally integrable on `[0, ∞)` and
satisfies `HasOscillatoryDecay c q α₀ f` with `c ≠ 0`, `1 ≤ q`, and `0 < α₀ + q - 1`, then for
every `n : ℕ`,
`∫ t in Ioi 0, exp (-(p * t)) * t ^ n * f t → n ! * iteratedTailIntegral f (n + 1) 0` as `p → 0⁺`.
-/
theorem tendsto_integral_exp_neg_mul_mul_pow_mul_nhdsGT_zero {c q α₀ : ℝ} {f : ℝ → ℝ}
    (hc : c ≠ 0) (hq : 1 ≤ q) (hα : 0 < α₀ + q - 1)
    (hf : HasOscillatoryDecay c q α₀ f) (hloc : LocallyIntegrableOn f (Ici 0)) (n : ℕ) :
    Tendsto (fun p : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(p * t)) * t ^ n * f t) (𝓝[>] 0)
      (𝓝 ((n.factorial : ℝ) * TauCeti.iteratedTailIntegral f (n + 1) 0)) := by
  simpa only [smul_eq_mul] using tendsto_integral_exp_neg_mul_mul_pow_smul_nhdsGT_zero
    (fun p hp ↦ hf.integrableOn_exp_neg_mul_mul hloc hp)
    (fun m _ ↦ ⟨_, hf.tendsto_intervalIntegral_iteratedTailIntegral hc hq hα m 0⟩)

/-- **Oscillatory Abelian Laplace-derivative theorem.** Under the hypotheses of
`HasOscillatoryDecay.tendsto_integral_exp_neg_mul_mul_pow_mul_nhdsGT_zero`, the `n`-th derivative of
the Laplace integral `r ↦ ∫ t in Ioi 0, exp (-(r * t)) * f t` tends to
`(-1) ^ n * n ! * iteratedTailIntegral f (n + 1) 0` as `p → 0⁺`. -/
theorem tendsto_iteratedDeriv_integral_exp_neg_mul_mul_nhdsGT_zero {c q α₀ : ℝ} {f : ℝ → ℝ}
    (hc : c ≠ 0) (hq : 1 ≤ q) (hα : 0 < α₀ + q - 1)
    (hf : HasOscillatoryDecay c q α₀ f) (hloc : LocallyIntegrableOn f (Ici 0)) (n : ℕ) :
    Tendsto (fun p : ℝ ↦
        iteratedDeriv n (fun r : ℝ ↦ ∫ t in Ioi 0, Real.exp (-(r * t)) * f t) p)
      (𝓝[>] 0) (𝓝 ((-1 : ℝ) ^ n * n.factorial * TauCeti.iteratedTailIntegral f (n + 1) 0)) := by
  simpa only [smul_eq_mul] using tendsto_iteratedDeriv_integral_exp_neg_mul_smul_nhdsGT_zero
    (fun p hp ↦ hf.integrableOn_exp_neg_mul_mul hloc hp)
    (fun m _ ↦ ⟨_, hf.tendsto_intervalIntegral_iteratedTailIntegral hc hq hα m 0⟩)

end HasOscillatoryDecay

end TauCeti
