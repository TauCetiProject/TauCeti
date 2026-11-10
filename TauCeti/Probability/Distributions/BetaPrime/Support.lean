/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaPrime.Basic
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Support of beta-prime distributions

This file identifies the positivity set of the beta-prime density and the exact topological
support of the corresponding measure. For positive shape parameters, the density is positive
exactly on `(0, ∞)`, while the measure has support `[0, ∞)`. Thus zero belongs to the
topological support even though a beta-prime variable is almost surely strictly positive.

## Main results

* `TauCeti.Probability.betaPrimePDFReal_pos_iff` and
  `TauCeti.Probability.betaPrimePDF_pos_iff` characterize positivity of the totalized densities;
* `TauCeti.Probability.support_betaPrimePDFReal` and
  `TauCeti.Probability.support_betaPrimePDF` identify their function supports;
* `TauCeti.Probability.support_betaPrimeMeasure` gives the topological support in every
  parameter regime.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 25.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

variable {a b x : ℝ}

/-- The real beta-prime density is positive exactly at positive shape parameters and a positive
sample point. -/
@[simp]
theorem betaPrimePDFReal_pos_iff :
    0 < betaPrimePDFReal a b x ↔ 0 < a ∧ 0 < b ∧ 0 < x := by
  by_cases hab : 0 < a ∧ 0 < b
  · by_cases hx : 0 < x
    · rw [betaPrimePDFReal_of_pos hab.1 hab.2 hx]
      exact iff_of_true
        (div_pos
          (mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos (by linarith) _))
          (ProbabilityTheory.beta_pos hab.1 hab.2))
        ⟨hab.1, hab.2, hx⟩
    · rw [betaPrimePDFReal_of_nonpos (le_of_not_gt hx) a b]
      simp [hab, hx]
  · rw [betaPrimePDFReal_of_not_pos hab]
    constructor
    · intro h
      exact (lt_irrefl 0 h).elim
    · intro h
      exact (hab ⟨h.1, h.2.1⟩).elim

/-- The `ℝ≥0∞`-valued beta-prime density is positive exactly at positive shape parameters and a
positive sample point. -/
@[simp]
theorem betaPrimePDF_pos_iff :
    0 < betaPrimePDF a b x ↔ 0 < a ∧ 0 < b ∧ 0 < x := by
  rw [betaPrimePDF_eq_ofReal, ENNReal.ofReal_pos, betaPrimePDFReal_pos_iff]

/-- The function support of the totalized real beta-prime density is the positive half-line at
positive shape parameters, and empty otherwise. -/
@[simp]
theorem support_betaPrimePDFReal (a b : ℝ) :
    Function.support (betaPrimePDFReal a b) = if 0 < a ∧ 0 < b then Ioi 0 else ∅ := by
  ext x
  have hne : betaPrimePDFReal a b x ≠ 0 ↔ 0 < betaPrimePDFReal a b x :=
    ⟨fun hx ↦ lt_of_le_of_ne (betaPrimePDFReal_nonneg a b x) hx.symm, ne_of_gt⟩
  by_cases h : 0 < a ∧ 0 < b
  · rw [ite_eq_left h, Function.mem_support, mem_Ioi]
    simpa [h] using hne.trans betaPrimePDFReal_pos_iff
  · rw [ite_eq_right h]
    simp [Function.mem_support, betaPrimePDFReal_of_not_pos h]

/-- The function support of the totalized extended beta-prime density is the positive half-line
at positive shape parameters, and empty otherwise. -/
@[simp]
theorem support_betaPrimePDF (a b : ℝ) :
    Function.support (betaPrimePDF a b) = if 0 < a ∧ 0 < b then Ioi 0 else ∅ := by
  ext x
  by_cases h : 0 < a ∧ 0 < b
  · rw [ite_eq_left h, Function.mem_support, mem_Ioi]
    simpa [h] using pos_iff_ne_zero.symm.trans (@betaPrimePDF_pos_iff a b x)
  · rw [ite_eq_right h]
    simp [Function.mem_support, betaPrimePDF_eq_ofReal, betaPrimePDFReal_of_not_pos h]

/-- The topological support of a beta-prime law is the closed nonnegative half-line at positive
shape parameters, and is empty for every invalid parameter pair. -/
@[simp]
theorem support_betaPrimeMeasure (a b : ℝ) :
    (betaPrimeMeasure a b).support = if 0 < a ∧ 0 < b then Ici 0 else ∅ := by
  split_ifs with h
  · rw [betaPrimeMeasure_eq_withDensity,
      Measure.support_withDensity_eq_closure (measurable_betaPrimePDF a b) isOpen_Ioi
        (by rw [support_betaPrimePDF, ite_eq_left h]),
      closure_Ioi]
  · rw [betaPrimeMeasure_of_not_pos h, Measure.support_zero]

end TauCeti.Probability
