/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Exponential.Poisson
public import TauCeti.Probability.PointProcess.Poisson.Temporal
import TauCeti.Probability.Independence.Basic
import TauCeti.Probability.Independence.InfinitePi

/-!
# Exponential interarrival characterization of homogeneous Poisson random measures

For positive rate `r > 0`, a measurable random measure `M : Ω → Measure ℝ≥0` is a homogeneous
Poisson random measure of intensity `r • nnvolume` if and only if almost every realization is
integer-valued and its interarrival gaps `Measure.occurrenceGap (M ω)` are independent with
rate-`r` exponential law. No separate local-finiteness, no-point-at-zero, or simplicity
assumption is needed for the converse: positivity of exponential gaps rules out infinite gaps
and ensures divergence of arrival times, hence local finiteness, almost surely. Independence of
the interarrival gaps (and of consecutive real-valued occurrence-time differences) also holds
at rate zero, where every occurrence time and gap is almost surely infinite.

Combining this with `isPoissonRandomMeasure_smul_nnvolume_iff_count_increments` yields the
three-way equivalence between:

1. `IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)` (homogeneous Poisson random measure),
2. stationary independent rate-`r` Poisson increments of a cumulative count process `N`
   starting at zero, and
3. independent rate-`r` exponential interarrival gaps `Measure.occurrenceGap (M ω)`.

The positive-rate hypothesis `0 < r` is essential for the exponential-gap characterization
because `expMeasure 0 = 0` is not a probability measure. Zero intensity is handled separately
in `Poisson/Basic.lean` (`isPoissonRandomMeasure_zero_iff`) and `Poisson/Temporal.lean`
(`isPoissonRandomMeasure_zero_iff_ae_count_eq_zero`): a zero-rate Poisson random measure is
simply the identically zero measure (and identically zero count process) almost surely.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4 and Chapter XI, §1.
* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 7, Theorem 7.2.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {M : Ω → Measure ℝ≥0} {N : ℝ≥0 → Ω → ℕ} {r : ℝ≥0}

/-- Exponential-law real-valued interarrival gaps are simultaneously positive and finite almost
surely. -/
private theorem ae_forall_occurrenceGap_pos_lt_top_of_hasLaw
    (hlaw : ∀ n, HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toReal) (expMeasure r) P) :
    ∀ᵐ ω ∂P, ∀ n, 0 < (M ω).occurrenceGap n ∧ (M ω).occurrenceGap n < ∞ :=
  ae_all_iff.mpr fun n ↦
    (ae_pos_of_hasLaw_expMeasure (hlaw n)).mono fun _ hω ↦ ENNReal.toReal_pos_iff.mp hω

namespace IsPoissonRandomMeasure

/-- **Joint product law of interarrival gaps.** For positive rate `r`, the `ℝ≥0`-valued
interarrival gaps of a homogeneous Poisson random measure have the countable product law
`Measure.infinitePi (fun _ ↦ nnrealExpMeasure r)`. -/
theorem hasLaw_toNNReal_occurrenceGap_infinitePi
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω n ↦ ((M ω).occurrenceGap n).toNNReal)
      (Measure.infinitePi fun _ : ℕ ↦ nnrealExpMeasure r) P := by
  have := isProbabilityMeasure_nnrealExpMeasure (NNReal.coe_pos.mpr hr)
  let Q : Measure (ℕ → ℝ≥0) := Measure.infinitePi fun _ : ℕ ↦ nnrealExpMeasure r
  let T : ℕ → (ℕ → ℝ≥0) → ℝ≥0 := fun n w ↦ w n
  have hindep : ProbabilityTheory.iIndepFun T Q := iIndepFun_eval_infinitePi _
  have hlaw : ∀ n, HasLaw (fun w ↦ (T n w : ℝ)) (expMeasure r) Q := fun n ↦ by
    dsimp only [T, Q]
    exact hasLaw_nnrealExpMeasure_iff.mp
      (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ nnrealExpMeasure r) n).hasLaw
  have hid := identDistrib_increments_toNNReal_occurrenceGap_of_isPoissonRandomMeasure
    hindep hlaw h
  exact hid.hasLaw ⟨measurable_id.aemeasurable, Measure.map_id⟩

/-- Each `ℝ≥0`-valued interarrival gap of a positive-rate homogeneous Poisson random measure has
law `nnrealExpMeasure r`. -/
theorem hasLaw_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toNNReal) (nnrealExpMeasure r) P :=
  have := isProbabilityMeasure_nnrealExpMeasure (NNReal.coe_pos.mpr hr)
  (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ nnrealExpMeasure r) n).fun_comp_hasLaw
    (h.hasLaw_toNNReal_occurrenceGap_infinitePi hr)

/-- Each real-valued interarrival gap of a positive-rate homogeneous Poisson random measure has
the exponential law `expMeasure r`. -/
theorem hasLaw_toReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toReal) (expMeasure r) P :=
  hasLaw_nnrealExpMeasure_iff.mp (h.hasLaw_toNNReal_occurrenceGap hr n)

/-- For a positive-rate homogeneous Poisson random measure, the real-valued interarrival-gap
sequence has the countable product law `Measure.infinitePi (fun _ ↦ expMeasure r)`. -/
theorem hasLaw_toReal_occurrenceGap_infinitePi
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω n ↦ ((M ω).occurrenceGap n).toReal)
      (Measure.infinitePi fun _ : ℕ ↦ expMeasure r) P := by
  have := isProbabilityMeasure_nnrealExpMeasure (NNReal.coe_pos.mpr hr)
  simpa only [nnrealExpMeasure_map_coe, ENNReal.coe_toNNReal_eq_toReal] using
    (h.hasLaw_toNNReal_occurrenceGap_infinitePi hr).infinitePi_map_pi
      (f := fun _ : ℕ ↦ ((↑) : ℝ≥0 → ℝ)) fun _ ↦ measurable_coe_nnreal_real

/-- Simultaneously for all `n`, every interarrival gap of a positive-rate homogeneous Poisson
random measure is strictly positive and finite almost surely. -/
theorem ae_forall_occurrenceGap_pos_lt_top
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ n, 0 < (M ω).occurrenceGap n ∧ (M ω).occurrenceGap n < ∞ :=
  ae_forall_occurrenceGap_pos_lt_top_of_hasLaw (h.hasLaw_toReal_occurrenceGap hr)

/-- For a positive-rate homogeneous Poisson random measure, the extended-valued interarrival-gap
sequence has the countable product law
`Measure.infinitePi (fun _ ↦ (expMeasure r).map ENNReal.ofReal)`. -/
theorem hasLaw_occurrenceGap_infinitePi
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω n ↦ (M ω).occurrenceGap n)
      (Measure.infinitePi fun _ : ℕ ↦ (expMeasure r).map ENNReal.ofReal) P := by
  have := isProbabilityMeasure_nnrealExpMeasure (NNReal.coe_pos.mpr hr)
  have hmap := (h.hasLaw_toNNReal_occurrenceGap_infinitePi hr).infinitePi_map_pi
    (f := fun _ : ℕ ↦ ((↑) : ℝ≥0 → ℝ≥0∞)) fun _ ↦ measurable_coe_nnreal_ennreal
  simp only [nnrealExpMeasure_map_coe_ennreal] at hmap
  refine hmap.congr ?_
  filter_upwards [h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hω
  funext n
  exact (ENNReal.coe_toNNReal (hω n).2.ne).symm

/-- Each extended-valued interarrival gap of a positive-rate homogeneous Poisson random measure
has law `(expMeasure r).map ENNReal.ofReal`. -/
theorem hasLaw_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ (M ω).occurrenceGap n) ((expMeasure r).map ENNReal.ofReal) P :=
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  (measurePreserving_eval_infinitePi
    (fun _ : ℕ ↦ (expMeasure r).map ENNReal.ofReal) n).fun_comp_hasLaw
    (h.hasLaw_occurrenceGap_infinitePi hr)

/-- For zero intensity, every interarrival gap of a temporal Poisson random measure is
simultaneously infinite almost surely. -/
theorem ae_forall_occurrenceGap_eq_top_of_zero
    (h : IsPoissonRandomMeasure P M 0) :
    ∀ᵐ ω ∂P, ∀ n, (M ω).occurrenceGap n = ∞ := by
  filter_upwards [h.ae_eq_zero_measure] with ω hω n
  simp [hω]

/-- The extended-valued interarrival gaps of a homogeneous Poisson random measure are mutually
independent, including at rate zero where every gap is almost surely infinite. -/
theorem iIndepFun_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ (M ω).occurrenceGap n) P := by
  have := h.isProbabilityMeasure
  rcases eq_zero_or_pos r with rfl | hr
  · rw [ENNReal.coe_zero, zero_smul] at h
    exact iIndepFun_of_ae_eq_const_outside_subsingleton (s := ∅) Set.subsingleton_empty
      fun n _ ↦ ⟨∞, h.ae_forall_occurrenceGap_eq_top_of_zero.mono fun ω hω ↦ hω n⟩
  · have hm : Measurable (fun ω n ↦ (M ω).occurrenceGap n) :=
      measurable_pi_iff.mpr fun n ↦ (Measure.measurable_occurrenceGap n).comp h.measurable
    exact (iIndepFun_iff_hasLaw_Pi_infinitePi (h.hasLaw_occurrenceGap hr)
      hm.aemeasurable).mpr (h.hasLaw_occurrenceGap_infinitePi hr)

/-- The `ℝ≥0`-valued interarrival gaps of a homogeneous Poisson random measure are mutually
independent, including at rate zero where every gap is almost surely zero. -/
theorem iIndepFun_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toNNReal) P :=
  h.iIndepFun_occurrenceGap.comp (fun _ ↦ ENNReal.toNNReal)
    (fun _ ↦ ENNReal.measurable_toNNReal)

/-- The real-valued interarrival gaps of a homogeneous Poisson random measure are mutually
independent, including at rate zero. -/
theorem iIndepFun_toReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toReal) P :=
  h.iIndepFun_occurrenceGap.comp (fun _ ↦ ENNReal.toReal)
    (fun _ ↦ ENNReal.measurable_toReal)

/-- Almost every realization of a positive-rate homogeneous Poisson random measure has strictly
increasing occurrence times. -/
theorem ae_strictMono_occurrenceTime
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, StrictMono (M ω).occurrenceTime := by
  filter_upwards [h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hω
  exact strictMono_nat_of_lt_succ fun n ↦
    (Measure.occurrenceGap_succ_pos_iff
      (((M ω).occurrenceGap_eq_top_iff n).not.mp (hω n).2.ne)).1 (hω (n + 1)).1

private theorem ae_toReal_occurrenceGap_succ_eq
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (n : ℕ) :
    (fun ω ↦ ((M ω).occurrenceGap (n + 1)).toReal) =ᵐ[P]
      fun ω ↦ ((M ω).occurrenceTime (n + 1)).toReal - ((M ω).occurrenceTime n).toReal := by
  rcases eq_zero_or_pos r with rfl | hr
  · rw [ENNReal.coe_zero, zero_smul] at h
    filter_upwards [h.ae_eq_zero_measure] with ω hω
    simp [hω]
  · filter_upwards [h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hω
    exact Measure.toReal_occurrenceGap_succ
      ((Measure.occurrenceGap_lt_top_iff _ _).mp (hω (n + 1)).2).ne

/-- Consecutive real-valued occurrence-time differences
`((M ω).occurrenceTime (n + 1)).toReal - ((M ω).occurrenceTime n).toReal` of a homogeneous
temporal Poisson random measure are mutually independent, including at rate zero. -/
theorem iIndepFun_toReal_occurrenceTime_sub
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω ↦
      ((M ω).occurrenceTime (n + 1)).toReal - ((M ω).occurrenceTime n).toReal) P :=
  (h.iIndepFun_toReal_occurrenceGap.precomp Nat.succ_injective).congr
    (ae_toReal_occurrenceGap_succ_eq h)

/-- Each consecutive real-valued occurrence-time difference of a positive-rate homogeneous
temporal Poisson random measure has law `expMeasure r`. -/
theorem hasLaw_toReal_occurrenceTime_sub
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ ((M ω).occurrenceTime (n + 1)).toReal - ((M ω).occurrenceTime n).toReal)
      (expMeasure r) P :=
  (h.hasLaw_toReal_occurrenceGap hr (n + 1)).congr (ae_toReal_occurrenceGap_succ_eq h n).symm

/-- Almost every realization of a positive-rate homogeneous Poisson random measure is the sum of
Dirac masses at the partial sums of its interarrival gaps. -/
theorem ae_eq_renewalArrivalMeasure_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, M ω = renewalArrivalMeasure (fun n ω ↦ ((M ω).occurrenceGap n).toNNReal) ω := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued,
    h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hloc hint hgap
  exact (renewalArrivalMeasure_toNNReal_occurrenceGap_eq hloc hint fun n ↦ (hgap n).2.ne).symm

end IsPoissonRandomMeasure

/-- **Recognizing a homogeneous Poisson random measure from i.i.d. exponential gaps (real form).**
A measurable random measure that is almost surely integer-valued and whose real-valued
interarrival gaps are independent rate-`r` exponentials is a homogeneous Poisson random measure
of intensity `r • nnvolume`. Neither `0 < r`, local finiteness, simplicity, nor absence of mass
at zero needs to be assumed separately. -/
theorem isPoissonRandomMeasure_smul_nnvolume_of_iIndepFun_toReal_occurrenceGap
    (hM : Measurable M) (hint : ∀ᵐ ω ∂P, (M ω).IsIntegerValued)
    (hind : iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toReal) P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toReal) (expMeasure r) P) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) := by
  let T : ℕ → Ω → ℝ≥0 := fun n ω ↦ ((M ω).occurrenceGap n).toNNReal
  have hT (n : ℕ) : Measurable (T n) :=
    ENNReal.measurable_toNNReal.comp ((Measure.measurable_occurrenceGap n).comp hM)
  have hindT : iIndepFun T P := by
    have h := hind.comp (fun _ ↦ Real.toNNReal) (fun _ ↦ measurable_real_toNNReal)
    simpa only [Function.comp_def, ← ENNReal.coe_toNNReal_eq_toReal, Real.toNNReal_coe] using h
  have hlawT (n : ℕ) : HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) P := hlaw n
  have hP := isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure hT hindT hlawT
  refine hP.congr hM ?_
  filter_upwards [hint, ae_forall_occurrenceGap_pos_lt_top_of_hasLaw hlaw,
    ae_tendsto_arrival_atTop_of_expMeasure hindT hlawT] with ω hωint hωgap hωtop
  have hfin (n : ℕ) : (M ω).occurrenceGap n ≠ ∞ := (hωgap n).2.ne
  have hfun : (M ω).occurrenceTime = fun n ↦ (arrival T (n + 1) ω : ℝ≥0∞) :=
    funext fun n ↦ (coe_arrival_succ_toNNReal_occurrenceGap (hfin n)).symm
  have hloc : IsLocallyFiniteMeasure (M ω) := by
    apply Measure.isLocallyFiniteMeasure_of_tendsto_occurrenceTime
    rw [hfun]
    exact ENNReal.tendsto_coe_nhds_top.mpr
      ((Filter.tendsto_add_atTop_iff_nat (f := fun n ↦ arrival T n ω) 1).mpr hωtop)
  exact renewalArrivalMeasure_toNNReal_occurrenceGap_eq hloc hωint hfin

/-- **Recognizing a homogeneous Poisson random measure from i.i.d. exponential gaps (`ℝ≥0` form).**
No separate `0 < r`, local-finiteness, simplicity, or absence of mass at zero is needed. -/
theorem isPoissonRandomMeasure_smul_nnvolume_of_iIndepFun_toNNReal_occurrenceGap
    (hM : Measurable M) (hint : ∀ᵐ ω ∂P, (M ω).IsIntegerValued)
    (hind : iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toNNReal) P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toNNReal) (nnrealExpMeasure r) P) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) := by
  refine isPoissonRandomMeasure_smul_nnvolume_of_iIndepFun_toReal_occurrenceGap hM hint ?_
    fun n ↦ ?_
  · simpa only [Function.comp_def, ENNReal.coe_toNNReal_eq_toReal] using
      hind.comp (fun _ ↦ ((↑) : ℝ≥0 → ℝ)) (fun _ ↦ measurable_coe_nnreal_real)
  · simpa only [ENNReal.coe_toNNReal_eq_toReal] using
      hasLaw_nnrealExpMeasure_iff.mp (hlaw n)

/-- **Recognizing a homogeneous Poisson random measure from i.i.d. exponential gaps (`ℝ≥0∞` form).**
No separate `0 < r`, local-finiteness, simplicity, or absence of mass at zero is needed. -/
theorem isPoissonRandomMeasure_smul_nnvolume_of_iIndepFun_occurrenceGap
    (hM : Measurable M) (hint : ∀ᵐ ω ∂P, (M ω).IsIntegerValued)
    (hind : iIndepFun (fun n ω ↦ (M ω).occurrenceGap n) P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ (M ω).occurrenceGap n) ((expMeasure r).map ENNReal.ofReal) P) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) := by
  refine isPoissonRandomMeasure_smul_nnvolume_of_iIndepFun_toReal_occurrenceGap hM hint
    (hind.comp (fun _ ↦ ENNReal.toReal) (fun _ ↦ ENNReal.measurable_toReal)) fun n ↦ ?_
  have h := (hasLaw_map (P := (expMeasure r).map ENNReal.ofReal)
    ENNReal.measurable_toReal.aemeasurable).comp (hlaw n)
  simpa only [expMeasure_map_ofReal_map_toReal, Function.comp_def] using h

/-- **Exponential-gap characterization of a homogeneous Poisson random measure (real form).**
For positive rate `r`, a measurable random measure on `ℝ≥0` is a homogeneous Poisson random
measure of intensity `r • nnvolume` if and only if it is almost surely integer-valued and its
real-valued interarrival gaps are independent rate-`r` exponentials. -/
theorem isPoissonRandomMeasure_smul_nnvolume_iff_iIndepFun_toReal_occurrenceGap
    (hr : 0 < r) (hM : Measurable M) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, (M ω).IsIntegerValued) ∧
      iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toReal) P ∧
      ∀ n, HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toReal) (expMeasure r) P :=
  ⟨fun h ↦ ⟨h.ae_isIntegerValued, h.iIndepFun_toReal_occurrenceGap,
      h.hasLaw_toReal_occurrenceGap hr⟩,
    fun ⟨hint, hind, hlaw⟩ ↦
      isPoissonRandomMeasure_smul_nnvolume_of_iIndepFun_toReal_occurrenceGap hM hint hind hlaw⟩

/-- **Exponential-gap characterization of a homogeneous Poisson random measure (`ℝ≥0` form).** -/
theorem isPoissonRandomMeasure_smul_nnvolume_iff_iIndepFun_toNNReal_occurrenceGap
    (hr : 0 < r) (hM : Measurable M) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, (M ω).IsIntegerValued) ∧
      iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toNNReal) P ∧
      ∀ n, HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toNNReal) (nnrealExpMeasure r) P :=
  ⟨fun h ↦ ⟨h.ae_isIntegerValued, h.iIndepFun_toNNReal_occurrenceGap,
      h.hasLaw_toNNReal_occurrenceGap hr⟩,
    fun ⟨hint, hind, hlaw⟩ ↦
      isPoissonRandomMeasure_smul_nnvolume_of_iIndepFun_toNNReal_occurrenceGap hM hint hind hlaw⟩

/-- **Exponential-gap characterization of a homogeneous Poisson random measure (`ℝ≥0∞` form).** -/
theorem isPoissonRandomMeasure_smul_nnvolume_iff_iIndepFun_occurrenceGap
    (hr : 0 < r) (hM : Measurable M) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, (M ω).IsIntegerValued) ∧
      iIndepFun (fun n ω ↦ (M ω).occurrenceGap n) P ∧
      ∀ n, HasLaw (fun ω ↦ (M ω).occurrenceGap n) ((expMeasure r).map ENNReal.ofReal) P :=
  ⟨fun h ↦ ⟨h.ae_isIntegerValued, h.iIndepFun_occurrenceGap, h.hasLaw_occurrenceGap hr⟩,
    fun ⟨hint, hind, hlaw⟩ ↦
      isPoissonRandomMeasure_smul_nnvolume_of_iIndepFun_occurrenceGap hM hint hind hlaw⟩

/-- **Equivalence between Poisson count increments and i.i.d. exponential interarrival gaps.**
For a measurable random measure with a natural-valued cumulative count process and positive
rate `r`, having a zero initial count and independent stationary rate-`r` Poisson increments is
equivalent to having independent rate-`r` exponential interarrival gaps. Combined with
`isPoissonRandomMeasure_smul_nnvolume_iff_count_increments`, both are equivalent to being a
homogeneous Poisson random measure of intensity `r • nnvolume`. -/
theorem count_increments_iff_iIndepFun_toReal_occurrenceGap
    (hr : 0 < r) (hM : Measurable M)
    (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞)) :
    ((∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (r * (t - s))) P) ↔
    (iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toReal) P ∧
      ∀ n, HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toReal) (expMeasure r) P) := by
  have hint : ∀ᵐ ω ∂P, (M ω).IsIntegerValued :=
    hcount.mono fun _ hω ↦ Measure.isIntegerValued_of_Iic fun t ↦ ⟨N t _, hω t⟩
  rw [← isPoissonRandomMeasure_smul_nnvolume_iff_count_increments hM hcount,
    isPoissonRandomMeasure_smul_nnvolume_iff_iIndepFun_toReal_occurrenceGap hr hM,
    and_iff_right hint]

end TauCeti.Probability
