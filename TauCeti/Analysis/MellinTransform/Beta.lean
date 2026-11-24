/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Mellin transform of the Beta weight

For `0 < Re (s + a)` and `-1 < Re b`, the function `t ↦ t^a (1 - t)^b` on `(0, 1]`, extended by
zero to the rest of `(0, ∞)`, has a convergent Mellin transform at `s`, and

`∫₀^1 t^{s - 1} t^a (1 - t)^b dt = B(s + a, b + 1)`,

where `B = Complex.betaIntegral` is Euler's Beta integral of the first kind (DLMF 5.12.1).

## Main results

* `Complex.hasMellin_indicator_cpow_mul_one_sub_cpow`: the Mellin transform of the Beta weight
  `t^a (1 - t)^b` on `(0, 1]` is `B(s + a, b + 1)`.

## References

* NIST Digital Library of Mathematical Functions, equation 5.12.1.
-/

public section

open Set MeasureTheory

namespace Complex

/-- **The Mellin transform of the Beta weight.** For `0 < Re (s + a)` and `-1 < Re b`, the
function `t ↦ t^a (1 - t)^b` on `(0, 1]`, extended by zero, has Mellin transform `B(s + a, b + 1)`
at `s`. -/
theorem hasMellin_indicator_cpow_mul_one_sub_cpow {a b s : ℂ} (hsa : 0 < (s + a).re)
    (hb : -1 < b.re) :
    HasMellin ((Ioc 0 1).indicator fun t : ℝ ↦ (t : ℂ) ^ a * (1 - (t : ℂ)) ^ b) s
      (betaIntegral (s + a) (b + 1)) := by
  have hbeta := betaIntegral_convergent (u := s + a) (v := b + 1) hsa
    (by simp only [add_re, one_re]; linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hbeta
  -- multiplying by `t^{s - 1}` shifts the first parameter of the Beta weight
  have heq : EqOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) •
        (Ioc 0 1).indicator (fun t : ℝ ↦ (t : ℂ) ^ a * (1 - (t : ℂ)) ^ b) t)
      ((Ioc 0 1).indicator fun t : ℝ ↦ (t : ℂ) ^ (s + a - 1) * (1 - (t : ℂ)) ^ (b + 1 - 1))
      (Ioi 0) := by
    intro t ht
    dsimp only
    by_cases h : t ∈ Ioc 0 1
    · rw [indicator_of_mem h, indicator_of_mem h, smul_eq_mul, add_sub_cancel_right,
        show s + a - 1 = s - 1 + a by ring,
        cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt ht)), mul_assoc]
    · rw [indicator_of_notMem h, indicator_of_notMem h, smul_zero]
  refine ⟨(integrableOn_congr_fun heq measurableSet_Ioi).mpr
    ((integrable_indicator_iff measurableSet_Ioc).mpr hbeta).integrableOn, ?_⟩
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi heq,
    setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le zero_le_one, betaIntegral]

end Complex
