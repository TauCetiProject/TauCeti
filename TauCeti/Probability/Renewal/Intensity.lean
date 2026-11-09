/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.NNReal
public import TauCeti.Probability.Renewal.ArrivalMeasure

/-!
# Intensity of exponential renewal arrivals

The expected arrival measure of an exponential renewal process of rate `r` is
`r • nnvolume`. This identifies the intensity on every measurable set, not just on
initial time intervals. The artificial arrival at time zero is excluded, and the
intensity has no atom there.

The result holds on any measurable probability realization of the independent
increments. It identifies the intensity, not the full Poisson random-measure law:
independence of counts on disjoint sets is a separate assertion.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 2 and 7, for intensities and exponential arrival constructions.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {T : ℕ → Ω → ℝ≥0} {r : ℝ≥0}

/-- The intensity measure of independent exponential renewal arrivals is rate times
half-line Lebesgue measure. No canonical choice of sample space is required. -/
theorem bind_renewalArrivalMeasure_of_expMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω => (T n ω : ℝ)) (expMeasure r) P) :
    P.bind (renewalArrivalMeasure T) = (r : ℝ≥0∞) • nnvolume := by
  have hIic (t : ℝ≥0) :
      (P.bind (renewalArrivalMeasure T)) (Iic t) = (r : ℝ≥0∞) * t := by
    rw [Measure.bind_apply measurableSet_Iic (measurable_renewalArrivalMeasure hT).aemeasurable]
    simp_rw [renewalArrivalMeasure_Iic]
    exact lintegral_renewalCount_of_expMeasure hT hindep hlaw t
  apply Measure.ext_of_generateFrom_of_iUnion (C := range (Iic : ℝ≥0 → Set ℝ≥0))
    (B := fun n : ℕ => Iic (n : ℝ≥0))
  · exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic ℝ≥0)
  · exact isPiSystem_Iic
  · exact iUnion_eq_univ_iff.2 fun t => exists_nat_ge t
  · intro n
    exact mem_range_self _
  · intro n
    rw [hIic]
    finiteness
  · rintro s ⟨t, rfl⟩
    rw [hIic, smul_apply, nnvolume_Iic, smul_eq_mul]

/-- The expected number of exponential renewal arrivals in an arbitrary measurable set
is its Lebesgue length times the rate; the equality permits infinite lengths. -/
theorem lintegral_renewalArrivalMeasure_of_expMeasure (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω => (T n ω : ℝ)) (expMeasure r) P)
    {A : Set ℝ≥0} (hA : MeasurableSet A) :
    ∫⁻ ω, renewalArrivalMeasure T ω A ∂P = (r : ℝ≥0∞) * nnvolume A := by
  rw [← Measure.bind_apply hA (measurable_renewalArrivalMeasure hT).aemeasurable,
    bind_renewalArrivalMeasure_of_expMeasure hT hindep hlaw, smul_apply, smul_eq_mul]

end TauCeti.Probability
