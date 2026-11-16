/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Exponential.Independence
public import TauCeti.Probability.Renewal.Restart.Exponential
public import TauCeti.Probability.Independence.Process.HasIndepIncrements
import TauCeti.Probability.Independence.Filtration

/-!
# The Poisson count-process law of exponential renewals

The count process of independent exponential waiting times has independent increments in
Mathlib's process-level sense. Consequently its full path law agrees with that of any
nondecreasing count process starting at zero with independent Poisson increments of the same
rate, even on a different sample space. Equality is on the product sigma-algebra of all
nonnegative time coordinates; no path continuity assumption is needed for this equality.

The natural-valued renewal count uses its existing value zero on explosive paths.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter I, §4 and Chapter XI, §1.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {T : ℕ → Ω → ℝ≥0} {r : ℝ≥0}

/-- Counts of independent exponential waiting times have independent increments, including
increments with equal endpoints. -/
theorem hasIndepIncrements_renewalCountNat_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    HasIndepIncrements (renewalCountNat T) P := by
  have := hindep.isProbabilityMeasure
  have hm (t : ℝ≥0) := (measurable_renewalCountNat hT t).stronglyMeasurable
  apply (Filtration.stronglyAdapted_natural hm).adapted.hasIndepIncrements
  intro s t hst
  rw [Filtration.natural_eq_comap]
  have hi := (indepFun_renewalCountNat_future_history_of_expMeasure hT hindep hlaw s).comp
    (measurable_pi_apply (t - s)) measurable_id
  simpa only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst, Pi.sub_def] using
    ((IndepFun_iff_Indep _ _ _).mp hi)

/-- The entire exponential-renewal count path has the law of any nondecreasing process
starting at zero with independent rate-`r` Poisson increments. This compares realizations
on arbitrary, possibly different, sample spaces. -/
theorem identDistrib_renewalCountNat_of_hasLaw_poissonMeasure
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {N : ℝ≥0 → Ω' → ℕ}
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hN : HasIndepIncrements N Q) (hmN : ∀ t, Measurable (N t))
    (h0N : ∀ᵐ ω ∂Q, N 0 ω = 0)
    (hmonoN : ∀ᵐ ω ∂Q, Monotone (fun t ↦ N t ω))
    (hlawN : ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω)
      (poissonMeasure (r * (t - s))) Q) :
    IdentDistrib (fun ω t ↦ renewalCountNat T t ω) (fun ω t ↦ N t ω) P Q := by
  have h0 : ∀ᵐ ω ∂P, renewalCountNat T 0 ω = 0 := by
    have h := hasLaw_renewalCountNat_poissonMeasure hindep hlaw 0
    simp only [mul_zero, poissonMeasure_zero] at h
    exact h.ae_eq_of_dirac
  apply (hasIndepIncrements_renewalCountNat_of_expMeasure hT hindep hlaw).identDistrib_nat
    hN (measurable_renewalCountNat hT) hmN h0 h0N
    (ae_of_all _ (monotone_renewalCountNat T)) hmonoN
  intro s t hst
  have h := hasLaw_renewalCountNat_sub_poissonMeasure hT hindep hlaw s (t - s)
  rw [add_tsub_cancel_of_le hst] at h
  exact h.identDistrib (hlawN s t hst)

end TauCeti.Probability
