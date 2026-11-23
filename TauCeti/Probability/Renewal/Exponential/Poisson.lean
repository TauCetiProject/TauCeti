/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.ArrivalMeasure
public import TauCeti.Probability.PointProcess.Poisson.Construction
public import TauCeti.MeasureTheory.Measure.NNReal
import TauCeti.MeasureTheory.Measure.Typeclasses.Finite
import TauCeti.Probability.Renewal.Exponential.Process
import TauCeti.Probability.PointProcess.Poisson.Count
import TauCeti.Probability.PointProcess.Poisson.Law
import TauCeti.Probability.PointProcess.Poisson.Temporal

/-!
# Exponential renewal arrivals as a homogeneous Poisson random measure

Let `T 0, T 1, …` be measurable independent exponential waiting times of rate `r`.
Then the random arrival measure `renewalArrivalMeasure T ω = ∑_{n ≥ 0} δ_{arrival T (n + 1) ω}`
is a homogeneous Poisson random measure on `ℝ≥0` with intensity `r • nnvolume`. Its law on
`Measure ℝ≥0` therefore coincides with `((r : ℝ≥0∞) • nnvolume).poissonLaw`, and it has the
same distribution as any homogeneous Poisson random measure `M` of rate `r`, possibly defined
on a different sample space.

Transferring along measurable evaluations and extractions identifies the full count-process
laws (both natural-valued and extended-valued), the full ordered arrival-time sequence laws,
and the full interarrival-gap sequence laws between the exponential renewal construction and
any homogeneous Poisson random measure of the same rate. No separate positivity hypothesis on
`r` is required: `expMeasure 0 = 0` cannot be the law of a random variable on a probability space,
so mutual independence of `T` automatically excludes `r = 0`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4 and Chapter XI, §1.
* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 3 and 7.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} {T : ℕ → Ω → ℝ≥0} {M : Ω' → Measure ℝ≥0} {r : ℝ≥0}

/-- **Exponential renewals define a homogeneous Poisson random measure.** For measurable
independent exponential waiting times of rate `r`, the arrival measure
`∑_{n ≥ 0} δ_{arrival T (n + 1)}` is a Poisson random measure with intensity `r • nnvolume`. -/
theorem isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    IsPoissonRandomMeasure P (renewalArrivalMeasure T) ((r : ℝ≥0∞) • nnvolume) := by
  have hcount : ∀ᵐ ω ∂P, ∀ t,
      renewalArrivalMeasure T ω (Iic t) = (renewalCountNat T t ω : ℝ≥0∞) := by
    filter_upwards [ae_tendsto_arrival_atTop_of_expMeasure hindep hlaw] with ω hω t
    rw [renewalArrivalMeasure_Iic, natCast_renewalCountNat hω]
  have h0 : ∀ᵐ ω ∂P, renewalCountNat T 0 ω = 0 := by
    have h := hasLaw_renewalCountNat_poissonMeasure hindep hlaw 0
    simp only [mul_zero, poissonMeasure_zero] at h
    exact h.ae_eq_of_dirac
  refine (isPoissonRandomMeasure_smul_nnvolume_iff_count_increments
    (measurable_renewalArrivalMeasure hT) hcount).mpr
    ⟨h0, hasIndepIncrements_renewalCountNat_of_expMeasure hT hindep hlaw, fun s t hst ↦ ?_⟩
  have h := hasLaw_renewalCountNat_sub_poissonMeasure hT hindep hlaw s (t - s)
  rwa [add_tsub_cancel_of_le hst] at h

/-- **Equality of random-measure laws with the canonical Poisson construction.** The law of the
exponential renewal arrival measure equals `((r : ℝ≥0∞) • nnvolume).poissonLaw`. -/
theorem hasLaw_renewalArrivalMeasure_poissonLaw_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    HasLaw (renewalArrivalMeasure T) ((r : ℝ≥0∞) • nnvolume).poissonLaw P :=
  (isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure hT hindep hlaw).hasLaw_poissonLaw

/-- **Equality in distribution of arrival measures.** The exponential renewal arrival measure has
the same distribution as any homogeneous Poisson random measure of the same rate, possibly on a
different sample space. -/
theorem identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (renewalArrivalMeasure T) M P Q :=
  (isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure hT hindep hlaw).identDistrib hM

/-- **Equality of full natural-valued count-process laws.** The natural-valued renewal count path
has the same product-space distribution as the cumulative natural count process of any homogeneous
Poisson random measure of the same rate. -/
theorem identDistrib_renewalCountNat_nat_count_of_isPoissonRandomMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω t ↦ renewalCountNat T t ω)
      (fun ω t ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊) P Q :=
  identDistrib_renewalCountNat_of_hasLaw_poissonMeasure hT hindep hlaw
    hM.hasIndepIncrements_nat_count hM.measurable_nat_count (by simp)
    hM.ae_monotone_nat_count (fun _ _ hst ↦ hM.hasLaw_nat_count_sub_smul_nnvolume hst)

/-- **Equality of full extended count-process laws.** The extended renewal count path
`renewalCount` has the same distribution as the cumulative initial-interval masses
`t ↦ M ω (Iic t)` of any homogeneous Poisson random measure of the same rate. -/
theorem identDistrib_renewalCount_Iic_of_isPoissonRandomMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω t ↦ renewalCount T t ω) (fun ω t ↦ M ω (Iic t)) P Q := by
  have hcomp := (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    hT hindep hlaw hM).comp
    (measurable_pi_iff.mpr fun t : ℝ≥0 ↦ Measure.measurable_coe (s := Iic t) measurableSet_Iic)
  simpa only [Function.comp_def, renewalArrivalMeasure_Iic] using hcomp

/-- **Equality of full arrival-time sequence laws.** The positive-index renewal arrivals have the
same distribution as the ordered occurrence times of any homogeneous Poisson random measure of
the same rate. -/
theorem identDistrib_arrival_succ_occurrenceTime_of_isPoissonRandomMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ (arrival T (n + 1) ω : ℝ≥0∞))
      (fun ω n ↦ (M ω).occurrenceTime n) P Q := by
  have hcomp := (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    hT hindep hlaw hM).comp
    (measurable_pi_iff.mpr fun n ↦ Measure.measurable_occurrenceTime n)
  have heq : (fun ω ↦ (renewalArrivalMeasure T ω).occurrenceTime) =
      fun ω n ↦ (arrival T (n + 1) ω : ℝ≥0∞) :=
    funext fun ω ↦ funext fun n ↦ occurrenceTime_renewalArrivalMeasure T ω n
  simpa only [Function.comp_def, heq] using hcomp

/-- **Equality of full extended gap-sequence laws.** The coerced exponential waiting times have
the same distribution as the extended interarrival gaps of any homogeneous Poisson random measure
of the same rate. -/
theorem identDistrib_coe_increments_occurrenceGap_of_isPoissonRandomMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ (T n ω : ℝ≥0∞)) (fun ω n ↦ (M ω).occurrenceGap n) P Q := by
  have hcomp := (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    hT hindep hlaw hM).comp
    (measurable_pi_iff.mpr fun n ↦ Measure.measurable_occurrenceGap n)
  have heq : (fun ω ↦ (renewalArrivalMeasure T ω).occurrenceGap) =
      fun ω n ↦ (T n ω : ℝ≥0∞) :=
    funext fun ω ↦ funext fun n ↦ occurrenceGap_renewalArrivalMeasure T ω n
  simpa only [Function.comp_def, heq] using hcomp

/-- **Equality of full nonnegative gap-sequence laws.** The exponential waiting times have the
same distribution as the `ℝ≥0`-valued interarrival gaps of any homogeneous Poisson random measure
of the same rate. -/
theorem identDistrib_increments_toNNReal_occurrenceGap_of_isPoissonRandomMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ T n ω) (fun ω n ↦ ((M ω).occurrenceGap n).toNNReal) P Q := by
  have hcomp := (identDistrib_coe_increments_occurrenceGap_of_isPoissonRandomMeasure
    hT hindep hlaw hM).comp
    (measurable_pi_iff.mpr fun n ↦ ENNReal.measurable_toNNReal.comp (measurable_pi_apply n))
  simpa only [Function.comp_def, ENNReal.toNNReal_coe] using hcomp

end TauCeti.Probability
