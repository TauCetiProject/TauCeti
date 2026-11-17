/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.ArrivalMeasure
public import TauCeti.Probability.PointProcess.Poisson.Construction
public import TauCeti.Probability.PointProcess.Poisson.Count
import TauCeti.Probability.Renewal.Exponential.Process
import TauCeti.Probability.PointProcess.Poisson.Law
import TauCeti.Probability.PointProcess.Poisson.Temporal
import Mathlib.MeasureTheory.Function.Floor

/-!
# Exponential renewal arrivals as homogeneous Poisson random measures

For independent exponential interarrival times `T` of rate `r`, the arrival measure
`renewalArrivalMeasure T` is a homogeneous Poisson random measure of intensity `r • nnvolume`
on the half-line. Its distribution equals `((r : ℝ≥0∞) • nnvolume).poissonLaw`, and it agrees
in law with any homogeneous Poisson random measure `M` of the same rate, even on a different
sample space.

Composing this measure-level law equality with measurable count, occurrence-time, and gap
extractions identifies the full natural-valued count process `renewalCountNat T` with the
temporal count process `⌊(M · (Ioc 0 ·)).toNNReal⌋₊`, the positive-index arrival sequence with
`Measure.occurrenceTime`, and the increments `T` with `Measure.occurrenceGap`. Conversely, any
positive-rate homogeneous Poisson random measure almost surely equals the renewal arrival
measure of its own interarrival gaps, and its temporal `(0, t]` counts agree simultaneously at
every time with the natural renewal counts of those gaps.

As in `TauCeti.Probability.Renewal.Exponential.Basic`, no separate positivity assumption on `r`
is needed when `iIndepFun T P` and `HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P` are assumed,
since `expMeasure 0 = 0` cannot be the law of a random variable on a probability space. When
starting from a homogeneous Poisson random measure `M`, positivity `0 < r` is required because
rate zero gives the identically zero measure almost surely.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4 and Chapter XI, §1.
* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 2, 3, and 7.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} {T : ℕ → Ω → ℝ≥0} {M : Ω' → Measure ℝ≥0} {r : ℝ≥0}

/-- The arrival measure of independent exponential interarrival times of rate `r` is a
homogeneous Poisson random measure of intensity `r • nnvolume`. No separate positivity
hypothesis on `r` is needed because `expMeasure 0 = 0` is incompatible with a probability
measure. -/
theorem isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    IsPoissonRandomMeasure P (renewalArrivalMeasure T) ((r : ℝ≥0∞) • nnvolume) := by
  have hcount : ∀ᵐ ω ∂P, ∀ t,
      renewalArrivalMeasure T ω (Iic t) = (renewalCountNat T t ω : ℝ≥0∞) := by
    filter_upwards [ae_tendsto_arrival_atTop_of_expMeasure hindep hlaw] with ω hω t
    rw [renewalArrivalMeasure_Iic, natCast_renewalCountNat hω]
  have h0 : ∀ᵐ ω ∂P, renewalCountNat T 0 ω = 0 := by
    have hz := hasLaw_renewalCountNat_poissonMeasure hindep hlaw 0
    simp only [mul_zero, poissonMeasure_zero] at hz
    exact hz.ae_eq_of_dirac
  refine (isPoissonRandomMeasure_smul_nnvolume_iff_count_increments
    (measurable_renewalArrivalMeasure hT) hcount).2 ⟨h0,
    hasIndepIncrements_renewalCountNat_of_expMeasure hT hindep hlaw, fun s t hst ↦ ?_⟩
  have hsub := hasLaw_renewalCountNat_sub_poissonMeasure hT hindep hlaw s (t - s)
  rwa [add_tsub_cancel_of_le hst] at hsub

/-- The arrival measure of independent exponential interarrival times agrees in distribution
with any homogeneous Poisson random measure of the same rate, on possibly different sample
spaces. -/
theorem identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (renewalArrivalMeasure T) M P Q :=
  (isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure hT hindep hlaw).identDistrib hM

/-- The arrival measure of independent exponential interarrival times of rate `r` has the
canonical homogeneous Poisson random-measure law `((r : ℝ≥0∞) • nnvolume).poissonLaw`. -/
theorem hasLaw_renewalArrivalMeasure_poissonLaw_of_expMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    HasLaw (renewalArrivalMeasure T) (((r : ℝ≥0∞) • nnvolume).poissonLaw) P := by
  have hid := identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure hT hindep hlaw
    (((r : ℝ≥0∞) • nnvolume).isPoissonRandomMeasure_poissonLaw)
  exact ⟨hid.aemeasurable_fst, by simpa using hid.map_eq⟩

/-- For exponential increments, the floored `(0, t]` counts of the arrival measure agree with
the natural renewal counts simultaneously at every time, almost surely. -/
theorem ae_forall_nat_count_renewalArrivalMeasure_eq_of_expMeasure
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    ∀ᵐ ω ∂P, ∀ t, ⌊(renewalArrivalMeasure T ω (Ioc 0 t)).toNNReal⌋₊ = renewalCountNat T t ω := by
  filter_upwards [ae_renewalArrivalMeasure_Ioc_eq_of_expMeasure hindep hlaw] with ω hω t
  simp [hω t]

/-- The full natural-valued count process of independent exponential interarrival times has
the same path law as the temporal `(0, t]` count process of any homogeneous Poisson random
measure of the same rate, on the product σ-algebra over all nonnegative times. -/
theorem identDistrib_renewalCountNat_nat_count_of_isPoissonRandomMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω t ↦ renewalCountNat T t ω)
      (fun ω t ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊) P Q := by
  let count : Measure ℝ≥0 → ℝ≥0 → ℕ := fun μ t ↦ ⌊(μ (Ioc 0 t)).toNNReal⌋₊
  have hcount : Measurable count :=
    measurable_pi_iff.mpr fun t ↦
      ((Measure.measurable_coe measurableSet_Ioc).ennreal_toNNReal).nat_floor
  have hcomp :=
    (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure hT hindep hlaw hM).comp hcount
  have hae : count ∘ renewalArrivalMeasure T =ᵐ[P] fun ω t ↦ renewalCountNat T t ω :=
    (ae_forall_nat_count_renewalArrivalMeasure_eq_of_expMeasure hindep hlaw).mono
      fun _ hω ↦ funext hω
  exact (IdentDistrib.of_ae_eq hcomp.aemeasurable_fst hae).symm.trans hcomp

/-- The sequence of positive-index arrival times of independent exponential interarrival times
has the same law as the ordered occurrence-time sequence of any homogeneous Poisson random
measure of the same rate. -/
theorem identDistrib_arrival_occurrenceTime_of_isPoissonRandomMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ (arrival T (n + 1) ω : ℝ≥0∞))
      (fun ω ↦ (M ω).occurrenceTime) P Q := by
  have hocc : Measurable fun μ : Measure ℝ≥0 ↦ μ.occurrenceTime :=
    measurable_pi_iff.mpr Measure.measurable_occurrenceTime
  have hcomp :=
    (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure hT hindep hlaw hM).comp hocc
  have heq : (fun μ : Measure ℝ≥0 ↦ μ.occurrenceTime) ∘ renewalArrivalMeasure T =
      fun ω n ↦ (arrival T (n + 1) ω : ℝ≥0∞) := by
    funext ω n
    exact occurrenceTime_renewalArrivalMeasure T ω n
  simpa only [heq, Function.comp_def] using hcomp

/-- The full sequence of independent exponential interarrival times has the same law as the
interarrival-gap sequence of any homogeneous Poisson random measure of the same rate. -/
theorem identDistrib_increments_occurrenceGap_of_isPoissonRandomMeasure
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ T n ω) (fun ω ↦ (M ω).occurrenceGap) P Q := by
  have hcomp :=
    (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure hT hindep hlaw hM).comp
      Measure.measurable_occurrenceGap
  have heq : (fun μ : Measure ℝ≥0 ↦ μ.occurrenceGap) ∘ renewalArrivalMeasure T =
      fun ω n ↦ T n ω := by
    funext ω n
    exact occurrenceGap_renewalArrivalMeasure T ω n
  simpa only [heq, Function.comp_def] using hcomp

/-- A positive-rate homogeneous Poisson random measure almost surely equals the renewal arrival
measure formed from its own interarrival gaps. Positivity of `r` is required because rate zero
gives the zero measure, whose gaps vanish while any renewal arrival measure has infinite total
mass. -/
theorem IsPoissonRandomMeasure.ae_eq_renewalArrivalMeasure_occurrenceGap
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂Q, M ω = renewalArrivalMeasure (fun n ω ↦ (M ω).occurrenceGap n) ω := by
  filter_upwards [hM.ae_isLocallyFiniteMeasure, hM.ae_isIntegerValued,
    hM.ae_apply_univ_eq_top_smul_nnvolume hr] with ω hloc hint htop
  let := hloc
  exact (renewalArrivalMeasure_occurrenceGap M hint htop).symm

/-- For a positive-rate homogeneous Poisson random measure, the temporal `(0, t]` natural count
agrees simultaneously at every time with the natural renewal count of its interarrival gaps,
almost surely. -/
theorem IsPoissonRandomMeasure.ae_forall_nat_count_eq_renewalCountNat_occurrenceGap
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂Q, ∀ t, ⌊(M ω (Ioc 0 t)).toNNReal⌋₊ =
      renewalCountNat (fun n ω ↦ (M ω).occurrenceGap n) t ω := by
  filter_upwards [hM.ae_isLocallyFiniteMeasure, hM.ae_isIntegerValued,
    hM.ae_apply_univ_eq_top_smul_nnvolume hr,
    hM.ae_forall_measure_Iic_eq_natCast_nat_count (by simp)] with ω hloc hint htop hcount t
  let := hloc
  rw [renewalCountNat_occurrenceGap M hint htop t, hcount t, ENNReal.toNNReal_natCast,
    Nat.floor_natCast]

end TauCeti.Probability
