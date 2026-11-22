/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import TauCeti.Analysis.SpecialFunctions.Integrals.ExpDiv

/-!
# Integral representations of the Euler–Mascheroni constant

This file complements `Mathlib.NumberTheory.Harmonic.GammaDeriv` (which proves
`γ = -∫ t in Ioi 0, log t * exp (-t)`) by establishing the split exponential-integral formula

```text
γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t
```

from the exponential-integral tail integrability and integration-by-parts identities in
`TauCeti.Analysis.SpecialFunctions.Integrals.ExpDiv`.

## Main results

* `Real.eulerMascheroniConstant_eq_integral_sub_integral`:
  `γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §5.9 (Gamma Function:
  Integral Representations) and §6.2.
-/

public section

open Filter MeasureTheory Set

namespace Real

/-- **Integral representation of the Euler–Mascheroni constant**:
`γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`. -/
theorem eulerMascheroniConstant_eq_integral_sub_integral :
    eulerMascheroniConstant =
      (∫ t in (0 : ℝ)..1, (1 - exp (-t)) / t) - ∫ t in Ioi (1 : ℝ), exp (-t) / t := by
  have h1 : (∫ t in (0 : ℝ)..1, (1 - exp (-t)) / t) =
      -(∫ t in Ioc 0 1, log t * exp (-t)) := by
    have h := one_sub_exp_neg_mul_log_eq zero_le_one
    rw [log_one, mul_zero] at h
    linarith
  have h2 : (∫ t in Ioi (1 : ℝ), exp (-t) / t) =
      ∫ t in Ioi (1 : ℝ), log t * exp (-t) := by
    have hint_log : IntegrableOn (fun t : ℝ ↦ log t * exp (-t)) (Ioi 1) :=
      integrableOn_log_mul_exp_neg_Ioi.mono_set (Ioi_subset_Ioi zero_le_one)
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := (1 : ℝ)) (f := fun t : ℝ ↦ -(exp (-t) * log t))
      (f' := fun t : ℝ ↦ log t * exp (-t) - exp (-t) / t) (m := 0)
      (fun t ht ↦ by
        have ht0 : 0 < t := zero_lt_one.trans_le ht
        have hd1 : HasDerivAt (fun u : ℝ ↦ exp (-u)) (-exp (-t)) t := by
          simpa using (hasDerivAt_neg t).exp
        exact ((hd1.mul (hasDerivAt_log ht0.ne')).neg).congr_deriv (by ring))
      (hint_log.sub (integrableOn_exp_neg_div_Ioi one_pos))
      (by simpa [mul_comm] using tendsto_log_mul_exp_neg_atTop.neg)
    rw [log_one, mul_zero, neg_zero, sub_zero,
      integral_sub hint_log (integrableOn_exp_neg_div_Ioi one_pos)] at hFTC
    linarith
  have hsplit : (∫ t in Ioi (0 : ℝ), log t * exp (-t)) =
      (∫ t in Ioc (0 : ℝ) 1, log t * exp (-t)) +
        ∫ t in Ioi (1 : ℝ), log t * exp (-t) := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (integrableOn_log_mul_exp_neg_Ioi.mono_set Ioc_subset_Ioi_self)
      (integrableOn_log_mul_exp_neg_Ioi.mono_set (Ioi_subset_Ioi zero_le_one)),
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [h1, h2, eulerMascheroniConstant_eq_neg_integral_log, hsplit]
  ring

end Real
