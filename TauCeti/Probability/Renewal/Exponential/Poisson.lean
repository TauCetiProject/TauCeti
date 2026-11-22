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
import TauCeti.Probability.PointProcess.Poisson.Temporal

/-!
# Exponential renewal arrivals as a homogeneous Poisson random measure

Let `T 0, T 1, …` be independent exponential waiting times of rate `r`.
Then the random arrival measure `renewalArrivalMeasure T ω = ∑_{n ≥ 0} δ_{arrival T (n + 1) ω}`
has law `((r : ℝ≥0∞) • nnvolume).poissonLaw` on `Measure ℝ≥0`, and when the increments are
measurable it is a homogeneous Poisson random measure with intensity `(r : ℝ≥0∞) • nnvolume`.
It therefore has the same distribution as any homogeneous Poisson random measure `M` of rate `r`,
possibly defined on a different sample space.

Transferring along measurable evaluations and extractions identifies the full count-process
laws (both natural-valued and extended-valued), the full ordered arrival-time sequence laws,
and the full interarrival-gap sequence laws between the exponential renewal construction and
any homogeneous Poisson random measure of the same rate. Strict measurability of the increments
is needed only for `IsPoissonRandomMeasure`, which requires strict measurability of the random
measure itself; the distributional identities require only the independence and exponential-law
hypotheses, which already supply almost-everywhere measurability and positivity of `r`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4 and Chapter XI, §1.
* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 3 and 7.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set Topology
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
exponential renewal arrival measure equals `((r : ℝ≥0∞) • nnvolume).poissonLaw`. Strict
measurability of the increments is not required; a.e. measurability is supplied by the law
hypotheses. -/
theorem hasLaw_renewalArrivalMeasure_poissonLaw_of_expMeasure
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    HasLaw (renewalArrivalMeasure T) ((r : ℝ≥0∞) • nnvolume).poissonLaw P := by
  have := hindep.isProbabilityMeasure
  have hr := pos_of_hasLaw_expMeasure (hlaw 0)
  have := isProbabilityMeasure_nnrealExpMeasure (NNReal.coe_pos.mpr hr)
  have hTnn (n : ℕ) : HasLaw (T n) (nnrealExpMeasure r) P :=
    hasLaw_nnrealExpMeasure_iff.mpr (hlaw n)
  have hpath : HasLaw (fun ω n ↦ T n ω)
      (Measure.infinitePi fun _ : ℕ ↦ nnrealExpMeasure r) P :=
    hindep.hasLaw_infinitePi hTnn (aemeasurable_pi_iff.2 fun n ↦ (hTnn n).aemeasurable)
  have hP₀ : IsPoissonRandomMeasure (Measure.infinitePi fun _ : ℕ ↦ nnrealExpMeasure r)
      (renewalArrivalMeasure fun n (w : ℕ → ℝ≥0) ↦ w n) ((r : ℝ≥0∞) • nnvolume) :=
    isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure
      (fun n ↦ measurable_pi_apply n)
      (iIndepFun_infinitePi (X := fun _ : ℕ ↦ (id : ℝ≥0 → ℝ≥0)) fun _ ↦ measurable_id)
      fun n ↦ hasLaw_nnrealExpMeasure_iff.mp
        (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ nnrealExpMeasure r) n).hasLaw
  have hcomp : renewalArrivalMeasure T =
      renewalArrivalMeasure (fun n (w : ℕ → ℝ≥0) ↦ w n) ∘ (fun ω n ↦ T n ω) := by
    funext ω
    exact renewalArrivalMeasure_comp (fun n (w : ℕ → ℝ≥0) ↦ w n) (fun ω n ↦ T n ω) ω
  rw [hcomp]
  exact hP₀.hasLaw_poissonLaw.comp hpath

/-- **Equality in distribution of arrival measures.** The exponential renewal arrival measure has
the same distribution as any homogeneous Poisson random measure of the same rate, possibly on a
different sample space. -/
theorem identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (renewalArrivalMeasure T) M P Q :=
  (hasLaw_renewalArrivalMeasure_poissonLaw_of_expMeasure hindep hlaw).identDistrib
    hM.hasLaw_poissonLaw

/-- **Equality of full natural-valued count-process laws.** The natural-valued renewal count path
has the same product-space distribution as the cumulative natural count process of any homogeneous
Poisson random measure of the same rate. -/
theorem identDistrib_renewalCountNat_nat_count_of_isPoissonRandomMeasure
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω t ↦ renewalCountNat T t ω)
      (fun ω t ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊) P Q := by
  have hcountMap : Measurable fun (μ : Measure ℝ≥0) (t : ℝ≥0) ↦ ⌊(μ (Ioc 0 t)).toNNReal⌋₊ :=
    measurable_pi_iff.mpr fun t ↦
      (Measure.measurable_coe measurableSet_Ioc).ennreal_toNNReal.nat_floor
  have hcomp := (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    hindep hlaw hM).comp hcountMap
  have hae : (fun ω t ↦ ⌊(renewalArrivalMeasure T ω (Ioc 0 t)).toNNReal⌋₊) =ᵐ[P]
      fun ω t ↦ renewalCountNat T t ω := by
    filter_upwards [ae_renewalArrivalMeasure_Ioc_eq_of_expMeasure hindep hlaw] with ω hω
    funext t
    simp [hω t]
  exact (IdentDistrib.of_ae_eq hcomp.aemeasurable_fst hae).symm.trans hcomp

/-- **Equality of full extended count-process laws.** The extended renewal count path
`renewalCount` has the same distribution as the cumulative initial-interval masses
`t ↦ M ω (Iic t)` of any homogeneous Poisson random measure of the same rate. -/
theorem identDistrib_renewalCount_Iic_of_isPoissonRandomMeasure
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω t ↦ renewalCount T t ω) (fun ω t ↦ M ω (Iic t)) P Q := by
  have hcomp := (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    hindep hlaw hM).comp
    (measurable_pi_iff.mpr fun t : ℝ≥0 ↦ Measure.measurable_coe (s := Iic t) measurableSet_Iic)
  simpa only [Function.comp_def, renewalArrivalMeasure_Iic] using hcomp

/-- **Equality of full arrival-time sequence laws.** The positive-index renewal arrivals have the
same distribution as the ordered occurrence times of any homogeneous Poisson random measure of
the same rate. -/
theorem identDistrib_arrival_succ_occurrenceTime_of_isPoissonRandomMeasure
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ (arrival T (n + 1) ω : ℝ≥0∞))
      (fun ω n ↦ (M ω).occurrenceTime n) P Q := by
  have hcomp := (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    hindep hlaw hM).comp
    (measurable_pi_iff.mpr fun n ↦ Measure.measurable_occurrenceTime n)
  have heq : (fun ω ↦ (renewalArrivalMeasure T ω).occurrenceTime) =
      fun ω n ↦ (arrival T (n + 1) ω : ℝ≥0∞) :=
    funext fun ω ↦ funext fun n ↦ occurrenceTime_renewalArrivalMeasure T ω n
  simpa only [Function.comp_def, heq] using hcomp

/-- Real-valued form of `identDistrib_arrival_succ_occurrenceTime_of_isPoissonRandomMeasure`:
the positive-index arrivals of an exponential renewal process have the same joint law as the
real-valued occurrence times of any homogeneous Poisson random measure of the same rate. -/
theorem identDistrib_arrival_succ_toReal_occurrenceTime_of_isPoissonRandomMeasure
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ (arrival T (n + 1) ω : ℝ))
      (fun ω n ↦ ((M ω).occurrenceTime n).toReal) P Q := by
  have htoReal : Measurable fun (x : ℕ → ℝ≥0∞) (n : ℕ) ↦ (x n).toReal :=
    measurable_pi_iff.mpr fun n ↦ ENNReal.measurable_toReal.comp (measurable_pi_apply n)
  simpa only [Function.comp_def, ENNReal.coe_toReal] using
    (identDistrib_arrival_succ_occurrenceTime_of_isPoissonRandomMeasure hindep hlaw hM).comp htoReal

/-- **Equality of full extended gap-sequence laws.** The coerced exponential waiting times have
the same distribution as the extended interarrival gaps of any homogeneous Poisson random measure
of the same rate. -/
theorem identDistrib_coe_increments_occurrenceGap_of_isPoissonRandomMeasure
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ (T n ω : ℝ≥0∞)) (fun ω n ↦ (M ω).occurrenceGap n) P Q := by
  have hcomp := (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    hindep hlaw hM).comp
    (measurable_pi_iff.mpr fun n ↦ Measure.measurable_occurrenceGap n)
  have heq : (fun ω ↦ (renewalArrivalMeasure T ω).occurrenceGap) =
      fun ω n ↦ (T n ω : ℝ≥0∞) :=
    funext fun ω ↦ funext fun n ↦ occurrenceGap_renewalArrivalMeasure T ω n
  simpa only [Function.comp_def, heq] using hcomp

/-- **Equality of full nonnegative gap-sequence laws.** The exponential waiting times have the
same distribution as the `ℝ≥0`-valued interarrival gaps of any homogeneous Poisson random measure
of the same rate. -/
theorem identDistrib_increments_toNNReal_occurrenceGap_of_isPoissonRandomMeasure
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ T n ω) (fun ω n ↦ ((M ω).occurrenceGap n).toNNReal) P Q := by
  have hcomp := (identDistrib_coe_increments_occurrenceGap_of_isPoissonRandomMeasure
    hindep hlaw hM).comp
    (measurable_pi_iff.mpr fun n ↦ ENNReal.measurable_toNNReal.comp (measurable_pi_apply n))
  simpa only [Function.comp_def, ENNReal.toNNReal_coe] using hcomp

end TauCeti.Probability
