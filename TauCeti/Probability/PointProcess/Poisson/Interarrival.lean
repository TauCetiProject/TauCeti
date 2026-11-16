/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Exponential.Poisson
public import TauCeti.Probability.PointProcess.Poisson.Temporal
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.Probability.Independence.InfinitePi

/-!
# Exponential interarrival characterization of homogeneous Poisson random measures

For positive rate `r > 0`, a measurable random measure `M : Ω → Measure ℝ≥0` is a homogeneous
Poisson random measure of intensity `r • nnvolume` if and only if almost every realization is
integer-valued and its interarrival gaps `Measure.occurrenceGap (M ω)` are independent with
rate-`r` exponential law. No separate local-finiteness, no-point-at-zero, or simplicity
assumption is needed for the converse: positivity of exponential gaps rules out infinite gaps
and ensures divergence of arrival times, hence local finiteness, almost surely.

Combining this with `isPoissonRandomMeasure_smul_nnvolume_iff_count_increments` yields the
three-way equivalence between:

1. `IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)` (homogeneous Poisson random measure),
2. stationary independent rate-`r` Poisson increments of a cumulative count process `N`
   starting at zero, and
3. independent rate-`r` exponential interarrival gaps `Measure.occurrenceGap (M ω)`.

The positive-rate hypothesis `0 < r` is essential for the exponential-gap characterization
because `expMeasure 0 = 0` is not a probability measure. Zero intensity is handled separately:
by `isPoissonRandomMeasure_zero_iff` and `isPoissonRandomMeasure_zero_iff_ae_count_eq_zero`, a
zero-rate Poisson random measure is simply the identically zero measure (and identically zero
count process) almost surely.

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
  have hT : ∀ n, Measurable (T n) := measurable_pi_apply
  have hindep : ProbabilityTheory.iIndepFun T Q := iIndepFun_eval_infinitePi _
  have hlaw : ∀ n, HasLaw (fun w ↦ (T n w : ℝ)) (expMeasure r) Q := fun n ↦
    hasLaw_nnrealExpMeasure_iff.mp
      ⟨(measurable_pi_apply n).aemeasurable, Measure.infinitePi_map_eval _ n⟩
  have hid := identDistrib_increments_toNNReal_occurrenceGap_of_isPoissonRandomMeasure
    hT hindep hlaw h
  exact hid.hasLaw ⟨measurable_id.aemeasurable, Measure.map_id⟩

/-- Each `ℝ≥0`-valued interarrival gap of a positive-rate homogeneous Poisson random measure has
law `nnrealExpMeasure r`. -/
theorem hasLaw_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toNNReal) (nnrealExpMeasure r) P := by
  have := isProbabilityMeasure_nnrealExpMeasure (NNReal.coe_pos.mpr hr)
  have hproj := (hasLaw_map (P := Measure.infinitePi fun _ : ℕ ↦ nnrealExpMeasure r)
    (measurable_pi_apply n).aemeasurable).comp (h.hasLaw_toNNReal_occurrenceGap_infinitePi hr)
  simpa only [Measure.infinitePi_map_eval, Function.comp_def] using hproj

/-- Each real-valued interarrival gap of a positive-rate homogeneous Poisson random measure has
the exponential law `expMeasure r`. -/
theorem hasLaw_toReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toReal) (expMeasure r) P :=
  hasLaw_nnrealExpMeasure_iff.mp (h.hasLaw_toNNReal_occurrenceGap hr n)

/-- The `ℝ≥0`-valued interarrival gaps of a positive-rate homogeneous Poisson random measure are
mutually independent. -/
theorem iIndepFun_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toNNReal) P := by
  have := h.isProbabilityMeasure
  have hm : Measurable (fun ω n ↦ ((M ω).occurrenceGap n).toNNReal) :=
    measurable_pi_iff.mpr fun n ↦
      ENNReal.measurable_toNNReal.comp ((Measure.measurable_occurrenceGap n).comp h.measurable)
  exact (iIndepFun_iff_hasLaw_Pi_infinitePi (h.hasLaw_toNNReal_occurrenceGap hr)
    hm.aemeasurable).mpr (h.hasLaw_toNNReal_occurrenceGap_infinitePi hr)

/-- The real-valued interarrival gaps of a positive-rate homogeneous Poisson random measure are
mutually independent. -/
theorem iIndepFun_toReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toReal) P :=
  (h.iIndepFun_toNNReal_occurrenceGap hr).comp (fun _ ↦ ((↑) : ℝ≥0 → ℝ))
    (fun _ ↦ measurable_coe_nnreal_real)

/-- Simultaneously for all `n`, every interarrival gap of a positive-rate homogeneous Poisson
random measure is strictly positive and finite almost surely. -/
theorem ae_forall_occurrenceGap_pos_lt_top
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ n, 0 < (M ω).occurrenceGap n ∧ (M ω).occurrenceGap n < ∞ :=
  ae_all_iff.mpr fun n ↦
    (ae_pos_of_hasLaw_expMeasure (h.hasLaw_toReal_occurrenceGap hr n)).mono fun _ hω ↦
      ENNReal.toReal_pos_iff.mp hω

/-- Each extended-valued interarrival gap of a positive-rate homogeneous Poisson random measure
has law `(expMeasure r).map ENNReal.ofReal`. -/
theorem hasLaw_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ (M ω).occurrenceGap n) ((expMeasure r).map ENNReal.ofReal) P := by
  have hcoe := (hasLaw_map (P := nnrealExpMeasure r)
    measurable_coe_nnreal_ennreal.aemeasurable).comp
    (h.hasLaw_toNNReal_occurrenceGap hr n)
  rw [nnrealExpMeasure_map_coe_ennreal] at hcoe
  refine hcoe.congr ?_
  filter_upwards [h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hω
  exact (ENNReal.coe_toNNReal (hω n).2.ne).symm

/-- The extended-valued interarrival gaps of a positive-rate homogeneous Poisson random measure
are mutually independent. -/
theorem iIndepFun_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ (M ω).occurrenceGap n) P := by
  have hcoe := (h.iIndepFun_toNNReal_occurrenceGap hr).comp
    (fun _ ↦ ((↑) : ℝ≥0 → ℝ≥0∞)) (fun _ ↦ measurable_coe_nnreal_ennreal)
  refine hcoe.congr fun n ↦ ?_
  filter_upwards [h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hω
  exact ENNReal.coe_toNNReal (hω n).2.ne

/-- Almost every realization of a positive-rate homogeneous Poisson random measure has strictly
increasing occurrence times. -/
theorem ae_strictMono_occurrenceTime
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, StrictMono (M ω).occurrenceTime := by
  filter_upwards [h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hω
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have hfin : (M ω).occurrenceTime n ≠ ∞ :=
    mt ((M ω).occurrenceGap_eq_top_iff n).mpr (hω n).2.ne
  have hgap := (hω (n + 1)).1
  rw [Measure.occurrenceGap_succ_of_ne_top hfin] at hgap
  exact tsub_pos_iff_lt.mp hgap

/-- Almost every realization of a positive-rate homogeneous Poisson random measure is the sum of
Dirac masses at the partial sums of its interarrival gaps. -/
theorem ae_eq_renewalArrivalMeasure_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, M ω = renewalArrivalMeasure (fun n ω ↦ ((M ω).occurrenceGap n).toNNReal) ω := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued,
    h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hloc hint hgap
  let := hloc
  rw [hint.eq_occurrenceTimeMeasure, renewalArrivalMeasure_eq_occurrenceTimeMeasure]
  congr 1
  funext n
  rw [← Measure.sum_range_succ_occurrenceGap, arrival_def]
  push_cast
  exact Finset.sum_congr rfl fun i _ ↦ (ENNReal.coe_toNNReal (hgap i).2.ne).symm

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
  have hgapFin : ∀ᵐ ω ∂P, ∀ n, (M ω).occurrenceGap n ≠ ∞ :=
    ae_all_iff.mpr fun n ↦
      (ae_pos_of_hasLaw_expMeasure (hlaw n)).mono fun _ hω ↦ (ENNReal.toReal_pos_iff.mp hω).2.ne
  filter_upwards [hint, hgapFin, ae_tendsto_arrival_atTop_of_expMeasure hindT hlawT]
    with ω hωint hωfin hωtop
  have htime (n : ℕ) : (M ω).occurrenceTime n = (arrival T (n + 1) ω : ℝ≥0∞) := by
    rw [← Measure.sum_range_succ_occurrenceGap, arrival_def]
    push_cast
    exact Finset.sum_congr rfl fun i _ ↦ (ENNReal.coe_toNNReal (hωfin i)).symm
  have hfun : (M ω).occurrenceTime = fun n ↦ (arrival T (n + 1) ω : ℝ≥0∞) := funext htime
  have hloc : IsLocallyFiniteMeasure (M ω) := by
    apply Measure.isLocallyFiniteMeasure_of_tendsto_occurrenceTime
    rw [hfun]
    exact ENNReal.tendsto_coe_nhds_top.mpr
      ((Filter.tendsto_add_atTop_iff_nat (f := fun n ↦ arrival T n ω) 1).mpr hωtop)
  rw [renewalArrivalMeasure_eq_occurrenceTimeMeasure, hωint.eq_occurrenceTimeMeasure, hfun]

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
      ∀ n, HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toReal) (expMeasure r) P := by
  refine ⟨fun h ↦ ?_, fun ⟨hint, hind, hlaw⟩ ↦
    isPoissonRandomMeasure_smul_nnvolume_of_iIndepFun_toReal_occurrenceGap hM hint hind hlaw⟩
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  exact ⟨h.ae_isIntegerValued, h.iIndepFun_toReal_occurrenceGap hr,
    h.hasLaw_toReal_occurrenceGap hr⟩

/-- **Exponential-gap characterization of a homogeneous Poisson random measure (`ℝ≥0∞` form).** -/
theorem isPoissonRandomMeasure_smul_nnvolume_iff_iIndepFun_occurrenceGap
    (hr : 0 < r) (hM : Measurable M) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, (M ω).IsIntegerValued) ∧
      iIndepFun (fun n ω ↦ (M ω).occurrenceGap n) P ∧
      ∀ n, HasLaw (fun ω ↦ (M ω).occurrenceGap n) ((expMeasure r).map ENNReal.ofReal) P := by
  refine ⟨fun h ↦ ?_, fun ⟨hint, hind, hlaw⟩ ↦
    isPoissonRandomMeasure_smul_nnvolume_of_iIndepFun_occurrenceGap hM hint hind hlaw⟩
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  exact ⟨h.ae_isIntegerValued, h.iIndepFun_occurrenceGap hr, h.hasLaw_occurrenceGap hr⟩

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

/-- **Zero-rate temporal Poisson characterization.** Separately from the positive-rate
exponential-gap characterization, a measurable random measure with a natural-valued cumulative
count process on a probability space has zero Poisson intensity if and only if its count process
is identically zero simultaneously at all times almost surely. -/
theorem isPoissonRandomMeasure_zero_iff_ae_count_eq_zero [IsProbabilityMeasure P]
    (hM : Measurable M) (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞)) :
    IsPoissonRandomMeasure P M (0 : Measure ℝ≥0) ↔ ∀ᵐ ω ∂P, ∀ t, N t ω = 0 := by
  rw [isPoissonRandomMeasure_zero_iff, and_iff_right hM]
  constructor
  · intro h0
    filter_upwards [h0, hcount] with ω hω hc t
    have hzero : (N t ω : ℝ≥0∞) = 0 := (hc t).symm.trans (by simp [hω])
    exact Nat.cast_eq_zero.mp hzero
  · intro h0
    filter_upwards [h0, hcount] with ω hω hc
    exact Measure.ext_of_Iic' _ _ (fun t ↦ by simp [hc t]) fun t ↦ by simp [hc t, hω t]

end TauCeti.Probability
