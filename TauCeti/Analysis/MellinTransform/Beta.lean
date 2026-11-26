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

* `TauCeti.hasMellin_cpow_mul_one_sub_cpow_Ioc`: the Mellin transform of the Beta weight
  `t^a (1 - t)^b` on `(0, 1]` is `B(s + a, b + 1)`.

## References

* NIST Digital Library of Mathematical Functions, equation 5.12.1.
-/

public section

open Set MeasureTheory Complex

namespace TauCeti

/-- **The Mellin transform of the Beta weight.** For `0 < Re (s + a)` and `-1 < Re b`, the
function `t ↦ t^a (1 - t)^b` on `(0, 1]`, extended by zero, has Mellin transform `B(s + a, b + 1)`
at `s`. -/
theorem hasMellin_cpow_mul_one_sub_cpow_Ioc {a b s : ℂ} (hsa : 0 < (s + a).re)
    (hb : -1 < b.re) :
    HasMellin ((Ioc 0 1).indicator fun t : ℝ ↦ (t : ℂ) ^ a * (1 - (t : ℂ)) ^ b) s
      (betaIntegral (s + a) (b + 1)) := by
  have hbeta := betaIntegral_convergent (u := s + a) (v := b + 1) hsa
    (by simp only [add_re, one_re]; linarith)
  rw [add_sub_cancel_right, intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hbeta
  -- the Mellin transform of the indicator of `(1 - t)^b` at `s + a` is the Beta integral
  have h : HasMellin ((Ioc 0 1).indicator fun t : ℝ ↦ (1 - (t : ℂ)) ^ b) (s + a)
      (betaIntegral (s + a) (b + 1)) := by
    simp_rw [HasMellin, mellin, MellinConvergent, ← indicator_smul, smul_eq_mul, IntegrableOn,
      integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
      integral_indicator measurableSet_Ioc, Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self,
      betaIntegral, add_sub_cancel_right, intervalIntegral.integral_of_le zero_le_one]
    exact ⟨hbeta, trivial⟩
  -- multiplying by `t^a` shifts the Mellin variable from `s + a` to `s`, as in `hasMellin_cpow_Ioc`
  simp_rw [HasMellin, ← MellinConvergent.cpow_smul, ← mellin_cpow_smul, ← indicator_smul,
    smul_eq_mul] at h
  exact h

end TauCeti
