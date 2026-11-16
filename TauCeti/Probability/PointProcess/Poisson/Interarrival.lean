/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Exponential.Poisson
public import TauCeti.Probability.PointProcess.Poisson.Temporal
import TauCeti.Probability.PointProcess.Poisson.OccurrenceTime
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import TauCeti.Probability.Independence.Basic
import TauCeti.Probability.Independence.InfinitePi

/-!
# Interarrival characterization of homogeneous temporal Poisson random measures

The interarrival times of any homogeneous temporal Poisson random measure of rate `r : ℝ≥0`
are mutually independent (including at rate zero, where every interarrival is almost surely
infinite). For positive rate `r > 0`, they are moreover identically distributed with the
exponential law of rate `r`, the joint law of the interarrival sequence is the infinite product
of exponential laws, every interarrival is simultaneously positive and finite almost surely, and
the random measure agrees almost surely with the renewal arrival measure of its interarrivals.

Conversely, a measurable random measure on `ℝ≥0` that is almost surely integer-valued and whose
interarrival times are independent with law `expMeasure r` is a homogeneous Poisson random
measure of intensity `r • nnvolume`. Neither local finiteness of the realizations nor positivity
of `r` need be assumed separately: positivity of `r` is forced by `expMeasure r` being a
probability law, and almost-sure local finiteness follows from divergence of the exponential
arrival sums.

Combining this equivalence with the count-increment characterization of
`TauCeti.Probability.PointProcess.Poisson.Temporal` yields the three-way equivalence between
homogeneous Poisson random measures, independent Poisson count increments, and independent
exponential interarrivals. Zero rate is treated separately: a zero-intensity Poisson random
measure vanishes almost surely, so all its occurrence times and interarrivals are infinite.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 7, Theorem 7.2.
* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4 and Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure ℝ≥0} {r : ℝ≥0}

namespace IsPoissonRandomMeasure

/-- For a positive-rate homogeneous temporal Poisson random measure, the extended-valued
interarrival sequence has the infinite product law of `(expMeasure r).map ENNReal.ofReal`. -/
theorem hasLaw_interarrival_infinitePi
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω n ↦ (N ω).interarrival n)
      (Measure.infinitePi fun _ : ℕ ↦ (expMeasure r).map ENNReal.ofReal) P := by
  let _ : IsProbabilityMeasure (nnrealExpMeasure (r : ℝ)) :=
    isProbabilityMeasure_nnrealExpMeasure (NNReal.coe_pos.mpr hr)
  let Q : Measure (ℕ → ℝ≥0) := Measure.infinitePi fun _ : ℕ ↦ nnrealExpMeasure (r : ℝ)
  have hind : ProbabilityTheory.iIndepFun (fun (n : ℕ) (w : ℕ → ℝ≥0) ↦ w n) Q :=
    iIndepFun_eval_infinitePi _
  have hlaw (n : ℕ) : HasLaw (fun w : ℕ → ℝ≥0 ↦ (w n : ℝ)) (expMeasure r) Q := by
    have heval : HasLaw (fun w : ℕ → ℝ≥0 ↦ w n) (nnrealExpMeasure r) Q :=
      ⟨(measurable_pi_apply n).aemeasurable, (measurePreserving_eval_infinitePi _ n).map_eq⟩
    simpa only [Function.comp_def, map_coe_nnrealExpMeasure] using
      (hasLaw_map measurable_coe_nnreal_real.aemeasurable).comp heval
  have hid := identDistrib_interarrival_of_isPoissonRandomMeasure hind hlaw h
  refine ⟨hid.aemeasurable_snd, hid.map_eq.symm.trans ?_⟩
  rw [Measure.infinitePi_map_pi _ (fun _ : ℕ ↦ measurable_coe_nnreal_ennreal)]
  simp only [map_ofNNReal_nnrealExpMeasure]

/-- For a positive-rate homogeneous temporal Poisson random measure, the nonnegative-real
interarrival sequence has the infinite product law of `nnrealExpMeasure r`. -/
theorem hasLaw_toNNReal_interarrival_infinitePi
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω n ↦ ((N ω).interarrival n).toNNReal)
      (Measure.infinitePi fun _ : ℕ ↦ nnrealExpMeasure r) P := by
  let _ : IsProbabilityMeasure (expMeasure (r : ℝ)) :=
    isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have htoNNReal : Measurable fun (x : ℕ → ℝ≥0∞) (n : ℕ) => (x n).toNNReal :=
    measurable_pi_iff.mpr fun n => ENNReal.measurable_toNNReal.comp (measurable_pi_apply n)
  have hmap := (hasLaw_map htoNNReal.aemeasurable).comp (h.hasLaw_interarrival_infinitePi hr)
  rw [Measure.infinitePi_map_pi _ (fun _ : ℕ ↦ ENNReal.measurable_toNNReal)] at hmap
  have hpush : ((expMeasure (r : ℝ)).map ENNReal.ofReal).map ENNReal.toNNReal =
      nnrealExpMeasure r := by
    rw [← map_ofNNReal_nnrealExpMeasure,
      Measure.map_map ENNReal.measurable_toNNReal measurable_coe_nnreal_ennreal]
    simp [Function.comp_def]
  simpa only [Function.comp_def, hpush] using hmap

/-- For a positive-rate homogeneous temporal Poisson random measure, the real-valued
interarrival sequence has the infinite product law of `expMeasure r`. -/
theorem hasLaw_toReal_interarrival_infinitePi
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω n ↦ ((N ω).interarrival n).toReal)
      (Measure.infinitePi fun _ : ℕ ↦ expMeasure r) P := by
  let _ : IsProbabilityMeasure (nnrealExpMeasure (r : ℝ)) :=
    isProbabilityMeasure_nnrealExpMeasure (NNReal.coe_pos.mpr hr)
  have hcoe : Measurable fun (w : ℕ → ℝ≥0) (n : ℕ) => (w n : ℝ) :=
    measurable_pi_iff.mpr fun n => measurable_coe_nnreal_real.comp (measurable_pi_apply n)
  have hmap := (hasLaw_map hcoe.aemeasurable).comp (h.hasLaw_toNNReal_interarrival_infinitePi hr)
  rw [Measure.infinitePi_map_pi _ (fun _ : ℕ ↦ measurable_coe_nnreal_real)] at hmap
  simp only [map_coe_nnrealExpMeasure] at hmap
  exact hmap

/-- Each extended-valued interarrival time of a positive-rate homogeneous temporal Poisson
random measure has the exponential law pushed forward to `ℝ≥0∞`. -/
theorem hasLaw_interarrival
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ (N ω).interarrival n) ((expMeasure r).map ENNReal.ofReal) P := by
  let _ := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have hlaw := (hasLaw_map (measurable_pi_apply n).aemeasurable).comp
    (h.hasLaw_interarrival_infinitePi hr)
  simpa only [Function.comp_def, Measure.infinitePi_map_eval] using hlaw

/-- The extended-valued interarrival times of a homogeneous temporal Poisson random measure are
mutually independent, including at rate zero where every interarrival is almost surely
infinite. -/
theorem iIndepFun_interarrival
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ (N ω).interarrival n) P := by
  let _ := h.isProbabilityMeasure
  rcases eq_zero_or_pos r with rfl | hr
  · rw [ENNReal.coe_zero, zero_smul] at h
    exact iIndepFun_of_ae_eq_const_outside_subsingleton (s := ∅) Set.subsingleton_empty
      fun n _ => ⟨∞, h.ae_eq_zero_measure.mono fun ω hω => by simp [hω]⟩
  · let _ := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
    have hm : AEMeasurable (fun ω n ↦ (N ω).interarrival n) P :=
      (measurable_pi_iff.mpr fun n =>
        (Measure.measurable_interarrival n).comp h.measurable).aemeasurable
    exact (iIndepFun_iff_hasLaw_Pi_infinitePi (h.hasLaw_interarrival hr) hm).mpr
      (h.hasLaw_interarrival_infinitePi hr)

/-- The nonnegative-real interarrival times of a homogeneous temporal Poisson random measure
are mutually independent, including at rate zero. -/
theorem iIndepFun_toNNReal_interarrival
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ ((N ω).interarrival n).toNNReal) P :=
  h.iIndepFun_interarrival.comp (fun _ => ENNReal.toNNReal)
    (fun _ => ENNReal.measurable_toNNReal)

/-- Each nonnegative-real interarrival time of a positive-rate homogeneous temporal Poisson
random measure has law `nnrealExpMeasure r`. -/
theorem hasLaw_toNNReal_interarrival
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ ((N ω).interarrival n).toNNReal) (nnrealExpMeasure r) P := by
  let _ := isProbabilityMeasure_nnrealExpMeasure (NNReal.coe_pos.mpr hr)
  have hlaw := (hasLaw_map (measurable_pi_apply n).aemeasurable).comp
    (h.hasLaw_toNNReal_interarrival_infinitePi hr)
  simpa only [Function.comp_def, Measure.infinitePi_map_eval] using hlaw

/-- **Interarrival independence (Last–Penrose Theorem 7.2).** The real-valued interarrival
times of a homogeneous temporal Poisson random measure are mutually independent, including
at rate zero. -/
theorem iIndepFun_toReal_interarrival
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ ((N ω).interarrival n).toReal) P :=
  h.iIndepFun_interarrival.comp (fun _ => ENNReal.toReal)
    (fun _ => ENNReal.measurable_toReal)

/-- **Exponential interarrival law (Last–Penrose Theorem 7.2).** Every real-valued interarrival
time of a positive-rate homogeneous temporal Poisson random measure has law `expMeasure r`. -/
theorem hasLaw_toReal_interarrival
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ ((N ω).interarrival n).toReal) (expMeasure r) P := by
  let _ := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have hlaw := (hasLaw_map (measurable_pi_apply n).aemeasurable).comp
    (h.hasLaw_toReal_interarrival_infinitePi hr)
  simpa only [Function.comp_def, Measure.infinitePi_map_eval] using hlaw

/-- Every interarrival time of a positive-rate homogeneous temporal Poisson random measure is
simultaneously positive and finite on one event of full probability. -/
theorem ae_forall_interarrival_pos_lt_top
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ n, 0 < (N ω).interarrival n ∧ (N ω).interarrival n < ∞ := by
  rw [ae_all_iff]
  intro n
  filter_upwards [ae_pos_of_hasLaw_expMeasure (h.hasLaw_toReal_interarrival hr n)] with ω hω
  exact ENNReal.toReal_pos_iff.mp hω

/-- Consecutive real-valued occurrence-time gaps
`((N ω).occurrenceTime (n + 1)).toReal - ((N ω).occurrenceTime n).toReal` of a homogeneous
temporal Poisson random measure are mutually independent, including at rate zero. -/
theorem iIndepFun_toReal_occurrenceTime_sub
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω ↦
      ((N ω).occurrenceTime (n + 1)).toReal - ((N ω).occurrenceTime n).toReal) P := by
  rcases eq_zero_or_pos r with rfl | hr
  · let _ := h.isProbabilityMeasure
    rw [ENNReal.coe_zero, zero_smul] at h
    exact iIndepFun_of_ae_eq_const_outside_subsingleton (s := ∅) Set.subsingleton_empty
      fun n _ => ⟨0, h.ae_eq_zero_measure.mono fun ω hω => by simp [hω]⟩
  · have hind := h.iIndepFun_toReal_interarrival.precomp Nat.succ_injective
    refine hind.congr fun n => ?_
    filter_upwards [h.ae_forall_occurrenceTime_pos_lt_top hr] with ω hω
    exact Measure.toReal_interarrival_succ (hω (n + 1)).2.ne

/-- Each consecutive real-valued occurrence-time gap of a positive-rate homogeneous temporal
Poisson random measure has law `expMeasure r`. -/
theorem hasLaw_toReal_occurrenceTime_sub
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ ((N ω).occurrenceTime (n + 1)).toReal - ((N ω).occurrenceTime n).toReal)
      (expMeasure r) P := by
  refine (h.hasLaw_toReal_interarrival hr (n + 1)).congr ?_
  filter_upwards [h.ae_forall_occurrenceTime_pos_lt_top hr] with ω hω
  exact (Measure.toReal_interarrival_succ (hω (n + 1)).2.ne).symm

/-- A positive-rate homogeneous temporal Poisson random measure agrees almost surely with the
renewal arrival measure formed from its nonnegative-real interarrival times. -/
theorem ae_eq_renewalArrivalMeasure_interarrival
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, N ω = renewalArrivalMeasure (fun n ω ↦ ((N ω).interarrival n).toNNReal) ω := by
  let _ : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued,
    h.ae_forall_interarrival_pos_lt_top hr] with ω hloc hint hfin
  let _ := hloc
  exact (renewalArrivalMeasure_toNNReal_interarrival_eq hint fun n => (hfin n).2.ne).symm

/-- For zero intensity, every occurrence time of a temporal Poisson random measure is
simultaneously infinite almost surely. -/
theorem ae_forall_occurrenceTime_eq_top_of_zero
    (h : IsPoissonRandomMeasure P N 0) :
    ∀ᵐ ω ∂P, ∀ n, (N ω).occurrenceTime n = ∞ := by
  filter_upwards [h.ae_eq_zero_measure] with ω hω n
  simp [hω]

/-- For zero intensity, every interarrival time of a temporal Poisson random measure is
simultaneously infinite almost surely. -/
theorem ae_forall_interarrival_eq_top_of_zero
    (h : IsPoissonRandomMeasure P N 0) :
    ∀ᵐ ω ∂P, ∀ n, (N ω).interarrival n = ∞ := by
  filter_upwards [h.ae_eq_zero_measure] with ω hω n
  simp [hω]

end IsPoissonRandomMeasure

/-- A measurable, almost surely integer-valued random measure on `ℝ≥0` whose real-valued
interarrival times are independent with law `expMeasure r` is a homogeneous Poisson random
measure of intensity `r • nnvolume`. Neither local finiteness of the realizations nor
positivity of `r` need be assumed separately. -/
theorem isPoissonRandomMeasure_smul_nnvolume_of_toReal_interarrival
    (hN : Measurable N) (hint : ∀ᵐ ω ∂P, (N ω).IsIntegerValued)
    (hindep : iIndepFun (fun n ω ↦ ((N ω).interarrival n).toReal) P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ ((N ω).interarrival n).toReal) (expMeasure r) P) :
    IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume) := by
  let T : ℕ → Ω → ℝ≥0 := fun n ω => ((N ω).interarrival n).toNNReal
  have hT (n : ℕ) : Measurable (T n) :=
    ENNReal.measurable_toNNReal.comp ((Measure.measurable_interarrival n).comp hN)
  have hTreal (n : ℕ) (ω : Ω) : (T n ω : ℝ) = ((N ω).interarrival n).toReal := rfl
  have hindepT : iIndepFun T P := by
    simpa only [Function.comp_def, ← hTreal, Real.toNNReal_coe] using
      hindep.comp (fun _ => Real.toNNReal) (fun _ => measurable_real_toNNReal)
  have hlawT (n : ℕ) : HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P := hlaw n
  have hR : IsPoissonRandomMeasure P (renewalArrivalMeasure T) ((r : ℝ≥0∞) • nnvolume) :=
    isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure hT hindepT hlawT
  have hpos : ∀ᵐ ω ∂P, ∀ n, 0 < ((N ω).interarrival n).toReal :=
    ae_all_iff.mpr fun n => ae_pos_of_hasLaw_expMeasure (hlaw n)
  have hae : renewalArrivalMeasure T =ᵐ[P] N := by
    filter_upwards [hint, hpos, ae_tendsto_arrival_atTop_of_expMeasure hindepT hlawT]
      with ω hωint hωpos hωtend
    have hfin (n : ℕ) : (N ω).interarrival n ≠ ∞ :=
      (ENNReal.toReal_pos_iff.mp (hωpos n)).2.ne
    have hocc : (N ω).occurrenceTime = fun n => (arrival T (n + 1) ω : ℝ≥0∞) := by
      funext n
      have hn : (N ω).occurrenceTime n ≠ ∞ := ((N ω).interarrival_eq_top_iff n).not.mp (hfin n)
      rw [arrival_def, Measure.sum_range_succ_toNNReal_interarrival hn, ENNReal.coe_toNNReal hn]
    have hloc : IsLocallyFiniteMeasure (N ω) := by
      rw [Measure.isLocallyFiniteMeasure_iff_tendsto_occurrenceTime_nhds_top, hocc,
        ENNReal.tendsto_coe_nhds_top]
      exact (Filter.tendsto_add_atTop_iff_nat (f := fun n => arrival T n ω) 1).mpr hωtend
    let _ := hloc
    exact renewalArrivalMeasure_toNNReal_interarrival_eq hωint hfin
  exact hR.congr hN hae

/-- Extended-valued form of `isPoissonRandomMeasure_smul_nnvolume_of_toReal_interarrival`:
independent extended-valued interarrivals with law `(expMeasure r).map ENNReal.ofReal` on an
almost surely integer-valued measurable random measure make it a rate-`r` Poisson random
measure. -/
theorem isPoissonRandomMeasure_smul_nnvolume_of_interarrival
    (hN : Measurable N) (hint : ∀ᵐ ω ∂P, (N ω).IsIntegerValued)
    (hindep : iIndepFun (fun n ω ↦ (N ω).interarrival n) P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (N ω).interarrival n) ((expMeasure r).map ENNReal.ofReal) P) :
    IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume) := by
  refine isPoissonRandomMeasure_smul_nnvolume_of_toReal_interarrival hN hint
    (hindep.comp (fun _ => ENNReal.toReal) (fun _ => ENNReal.measurable_toReal)) fun n => ?_
  have hcomp := (hasLaw_map ENNReal.measurable_toReal.aemeasurable).comp (hlaw n)
  rw [← map_ofNNReal_nnrealExpMeasure,
    Measure.map_map ENNReal.measurable_toReal measurable_coe_nnreal_ennreal] at hcomp
  simpa only [Function.comp_def, ENNReal.coe_toReal, map_coe_nnrealExpMeasure] using hcomp

/-- A measurable random measure on `ℝ≥0` is a positive-rate homogeneous Poisson random measure
if and only if it is almost surely integer-valued and has independent real-valued interarrival
times with law `expMeasure r`. -/
theorem isPoissonRandomMeasure_smul_nnvolume_iff_toReal_interarrival
    (hr : 0 < r) (hN : Measurable N) :
    IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, (N ω).IsIntegerValued) ∧
      iIndepFun (fun n ω ↦ ((N ω).interarrival n).toReal) P ∧
      ∀ n, HasLaw (fun ω ↦ ((N ω).interarrival n).toReal) (expMeasure r) P := by
  let _ : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  refine ⟨fun h => ⟨h.ae_isIntegerValued, h.iIndepFun_toReal_interarrival,
      h.hasLaw_toReal_interarrival hr⟩,
    fun ⟨hint, hindep, hlaw⟩ =>
      isPoissonRandomMeasure_smul_nnvolume_of_toReal_interarrival hN hint hindep hlaw⟩

/-- Extended-valued form of `isPoissonRandomMeasure_smul_nnvolume_iff_toReal_interarrival`. -/
theorem isPoissonRandomMeasure_smul_nnvolume_iff_interarrival
    (hr : 0 < r) (hN : Measurable N) :
    IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, (N ω).IsIntegerValued) ∧
      iIndepFun (fun n ω ↦ (N ω).interarrival n) P ∧
      ∀ n, HasLaw (fun ω ↦ (N ω).interarrival n) ((expMeasure r).map ENNReal.ofReal) P := by
  let _ : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  refine ⟨fun h => ⟨h.ae_isIntegerValued, h.iIndepFun_interarrival,
      h.hasLaw_interarrival hr⟩,
    fun ⟨hint, hindep, hlaw⟩ =>
      isPoissonRandomMeasure_smul_nnvolume_of_interarrival hN hint hindep hlaw⟩

/-- For a measurable temporal random measure with a natural-valued cumulative count process and
positive rate `r`, having zero initial count and independent rate-`r` Poisson count increments
is equivalent to having independent exponential interarrival times of rate `r`. -/
theorem count_increments_iff_toReal_interarrival {C : ℝ≥0 → Ω → ℕ}
    (hr : 0 < r) (hN : Measurable N)
    (hcount : ∀ᵐ ω ∂P, ∀ t, N ω (Iic t) = (C t ω : ℝ≥0∞)) :
    ((∀ᵐ ω ∂P, C 0 ω = 0) ∧ HasIndepIncrements C P ∧
      ∀ s t, s ≤ t → HasLaw (fun ω ↦ C t ω - C s ω)
        (poissonMeasure (r * (t - s))) P) ↔
      (iIndepFun (fun n ω ↦ ((N ω).interarrival n).toReal) P ∧
        ∀ n, HasLaw (fun ω ↦ ((N ω).interarrival n).toReal) (expMeasure r) P) := by
  have hint : ∀ᵐ ω ∂P, (N ω).IsIntegerValued := by
    filter_upwards [hcount] with ω hω
    apply Measure.isIntegerValued_of_restrict (s := fun n : ℕ => Iic (n : ℝ≥0))
    · ext t
      simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
      exact exists_nat_ge t
    · intro n
      let μ := (N ω).restrict (Iic (n : ℝ≥0))
      apply Measure.isIntegerValued_of_isPiSystem (μ := μ)
        (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic (α := ℝ≥0))) isPiSystem_Iic
      · rintro _ ⟨t, rfl⟩
        exact ⟨C (min t n) ω, by
          simp [μ, Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic, hω]⟩
      · exact ⟨C n ω, by simp [μ, hω]⟩
  rw [← isPoissonRandomMeasure_smul_nnvolume_iff_count_increments hN hcount,
    isPoissonRandomMeasure_smul_nnvolume_iff_toReal_interarrival hr hN]
  simp [hint]

end TauCeti.Probability
