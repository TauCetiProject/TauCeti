/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.NNReal
public import TauCeti.Probability.Renewal.ArrivalMeasure
public import TauCeti.Probability.PointProcess.Poisson.Law
import TauCeti.Probability.Renewal.Exponential.Process
import TauCeti.Probability.PointProcess.Poisson.Temporal

/-!
# Exponential renewal arrivals as homogeneous Poisson random measures

The renewal arrival measure `renewalArrivalMeasure T` formed from independent exponentially
distributed waiting times of rate `r` is a homogeneous temporal Poisson random measure of
intensity `r • nnvolume`. Consequently its law is `Measure.poissonLaw (r • nnvolume)`, and it
agrees in distribution—as a random measure, as a natural-valued counting process, as an ordered
sequence of arrival times, and as a sequence of interarrival times—with any homogeneous
temporal Poisson random measure of rate `r`, possibly defined on a different probability space.

Strict measurability of the increments is needed only for `IsPoissonRandomMeasure`, which
requires strict measurability of the random measure itself. The distributional identities and
the almost-sure arrival-rate limit require only the independence and exponential-law
hypotheses, which already supply almost-everywhere measurability and positivity of the rate.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4 and Chapter XI, §1.
* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 7, Theorem 7.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0} {r : ℝ≥0}

/-- The renewal arrival measure of measurable independent exponential waiting times of rate `r`
is a homogeneous temporal Poisson random measure of intensity `r • nnvolume`. Positivity of
`r` and the probability-measure property of `P` follow automatically from the hypotheses. -/
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
    (measurable_renewalArrivalMeasure hT) hcount).2 ⟨h0,
      hasIndepIncrements_renewalCountNat_of_expMeasure hT hindep hlaw, fun s t hst ↦ ?_⟩
  have h := hasLaw_renewalCountNat_sub_poissonMeasure hT hindep hlaw s (t - s)
  rwa [add_tsub_cancel_of_le hst] at h

/-- The renewal arrival measure of independent exponential waiting times of rate `r` has law
`Measure.poissonLaw (r • nnvolume)`. Strict measurability of the increments is not required;
a.e. measurability is supplied by the law hypotheses. -/
theorem hasLaw_renewalArrivalMeasure_poissonLaw_of_expMeasure
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    HasLaw (renewalArrivalMeasure T) (r • nnvolume).poissonLaw P := by
  have hTm (n : ℕ) : AEMeasurable (T n) P :=
    ((hlaw n).identDistrib_nnreal (hlaw 0)).aemeasurable_fst
  let T' : ℕ → Ω → ℝ≥0 := fun n => (hTm n).mk (T n)
  have hT' (n : ℕ) : Measurable (T' n) := (hTm n).measurable_mk
  have haeT (n : ℕ) : T n =ᵐ[P] T' n := (hTm n).ae_eq_mk
  have hindep' : iIndepFun T' P := hindep.congr haeT
  have hlaw' (n : ℕ) : HasLaw (fun ω ↦ (T' n ω : ℝ)) (expMeasure r) P :=
    (hlaw n).congr ((haeT n).symm.mono fun _ hω => congrArg NNReal.toReal hω)
  have hP' : IsPoissonRandomMeasure P (renewalArrivalMeasure T') (r • nnvolume) := by
    have hsmul : (r : ℝ≥0∞) • nnvolume = r • nnvolume := by
      ext s
      simp [Measure.nnreal_smul_coe_apply]
    rw [← hsmul]
    exact isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure hT' hindep' hlaw'
  have hmeas_eq : renewalArrivalMeasure T =ᵐ[P] renewalArrivalMeasure T' := by
    filter_upwards [ae_all_iff.2 haeT] with ω hω
    simp only [renewalArrivalMeasure_def, arrival_def]
    congr 1
    funext n
    congr 1
    exact Finset.sum_congr rfl fun i _ => hω i
  exact hP'.hasLaw_poissonLaw.congr hmeas_eq

/-- The renewal arrival measure of independent exponential waiting times of rate `r` has the
same distribution as any homogeneous temporal Poisson random measure of rate `r`, possibly
defined on a different sample space. -/
theorem identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {M : Ω' → Measure ℝ≥0}
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (renewalArrivalMeasure T) M P Q := by
  have hsmul : (r : ℝ≥0∞) • nnvolume = r • nnvolume := by
    ext s
    simp [Measure.nnreal_smul_coe_apply]
  rw [hsmul] at hM
  exact (hasLaw_renewalArrivalMeasure_poissonLaw_of_expMeasure hindep hlaw).identDistrib
    hM.hasLaw_poissonLaw

/-- The entire natural-valued count path of an exponential renewal process has the same law as
the natural-valued count path of any homogeneous temporal Poisson random measure of the same
rate. Equality is on the full product σ-algebra indexed by all nonnegative times. -/
theorem identDistrib_renewalCountNat_of_isPoissonRandomMeasure
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {M : Ω' → Measure ℝ≥0}
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω t ↦ renewalCountNat T t ω)
      (fun ω t ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊) P Q := by
  have hcountMap : Measurable fun (μ : Measure ℝ≥0) (t : ℝ≥0) => ⌊(μ (Ioc 0 t)).toNNReal⌋₊ :=
    measurable_pi_iff.mpr fun t =>
      (Measure.measurable_coe measurableSet_Ioc).ennreal_toNNReal.nat_floor
  have hcomp := (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure
    hindep hlaw hM).comp hcountMap
  have hae : (fun ω t ↦ ⌊(renewalArrivalMeasure T ω (Ioc 0 t)).toNNReal⌋₊) =ᵐ[P]
      fun ω t ↦ renewalCountNat T t ω := by
    filter_upwards [ae_renewalArrivalMeasure_Ioc_eq_of_expMeasure hindep hlaw] with ω hω
    funext t
    simp [hω t]
  exact (IdentDistrib.of_ae_eq hcomp.aemeasurable_fst hae).symm.trans hcomp

/-- The positive-index arrival sequence of an exponential renewal process has the same joint
law as the ordered occurrence-time sequence of any homogeneous temporal Poisson random measure
of the same rate. -/
theorem identDistrib_arrival_occurrenceTime_of_isPoissonRandomMeasure
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {M : Ω' → Measure ℝ≥0}
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ (arrival T (n + 1) ω : ℝ≥0∞))
      (fun ω n ↦ (M ω).occurrenceTime n) P Q := by
  have hocc : Measurable fun (μ : Measure ℝ≥0) (n : ℕ) => μ.occurrenceTime n :=
    measurable_pi_iff.mpr Measure.measurable_occurrenceTime
  simpa only [Function.comp_def, occurrenceTime_renewalArrivalMeasure] using
    (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure hindep hlaw hM).comp hocc

/-- Real-valued form of `identDistrib_arrival_occurrenceTime_of_isPoissonRandomMeasure`: the
positive-index arrivals of an exponential renewal process have the same joint law as the
real-valued occurrence times of any homogeneous temporal Poisson random measure of the same
rate. -/
theorem identDistrib_toReal_arrival_occurrenceTime_of_isPoissonRandomMeasure
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {M : Ω' → Measure ℝ≥0}
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ (arrival T (n + 1) ω : ℝ))
      (fun ω n ↦ ((M ω).occurrenceTime n).toReal) P Q := by
  have htoReal : Measurable fun (x : ℕ → ℝ≥0∞) (n : ℕ) => (x n).toReal :=
    measurable_pi_iff.mpr fun n => ENNReal.measurable_toReal.comp (measurable_pi_apply n)
  simpa only [Function.comp_def, ENNReal.coe_toReal] using
    (identDistrib_arrival_occurrenceTime_of_isPoissonRandomMeasure hindep hlaw hM).comp htoReal

/-- The increment sequence of an exponential renewal process has the same joint law as the
interarrival sequence of any homogeneous temporal Poisson random measure of the same rate. -/
theorem identDistrib_interarrival_of_isPoissonRandomMeasure
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {M : Ω' → Measure ℝ≥0}
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P)
    (hM : IsPoissonRandomMeasure Q M ((r : ℝ≥0∞) • nnvolume)) :
    IdentDistrib (fun ω n ↦ (T n ω : ℝ≥0∞))
      (fun ω n ↦ (M ω).interarrival n) P Q := by
  have hint : Measurable fun (μ : Measure ℝ≥0) (n : ℕ) => μ.interarrival n :=
    measurable_pi_iff.mpr Measure.measurable_interarrival
  simpa only [Function.comp_def, interarrival_renewalArrivalMeasure] using
    (identDistrib_renewalArrivalMeasure_of_isPoissonRandomMeasure hindep hlaw hM).comp hint

/-- For independent exponential increments of rate `r`, the arrival-measure mass of `(0, t]`
divided by `t` converges almost surely to `r` along all nonnegative real times. -/
theorem ae_tendsto_renewalArrivalMeasure_Ioc_div_of_expMeasure
    (hindep : iIndepFun T P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun t : ℝ≥0 ↦ (renewalArrivalMeasure T ω (Ioc 0 t)).toReal / (t : ℝ)) atTop
      (𝓝 (r : ℝ)) := by
  filter_upwards [ae_renewalArrivalMeasure_Ioc_eq_of_expMeasure hindep hlaw,
    ae_tendsto_renewalCountNat_div_of_expMeasure (fun _ _ hij => hindep.indepFun hij) hlaw]
    with ω hω hlim
  simpa only [hω, ENNReal.toReal_natCast] using hlim

end TauCeti.Probability
