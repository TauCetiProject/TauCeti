/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Exponential.Poisson
public import TauCeti.Probability.PointProcess.Poisson.Temporal
import TauCeti.MeasureTheory.Measure.Typeclasses.Finite
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.Probability.Independence.InfinitePi
import TauCeti.Probability.Independence.Basic

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

At rate zero, the random measure vanishes almost surely, so every extended interarrival gap is
almost surely infinite (`ae_forall_occurrenceGap_eq_top_of_zero`). Because almost surely constant
coordinates are independent, mutual independence of the interarrival gaps holds for every rate
`r : ℝ≥0`, without a positivity side condition. Zero-rate characterization is handled separately
in `Poisson/Basic.lean` (`isPoissonRandomMeasure_zero_iff`) and `Poisson/Temporal.lean`
(`isPoissonRandomMeasure_zero_iff_ae_count_eq_zero`).

For `0 < r`, finite prefixes of `toNNReal` occurrence times have the cumulative-sum law of
`m` i.i.d. `nnrealExpMeasure r` variables (`hasLaw_toNNReal_occurrenceTime_prefix`), finite
prefixes of interarrival gaps have the product law `Measure.pi`, and the full gap sequences
have the countable product law `Measure.infinitePi`. Pathwise on one event of probability one,
a positive-rate homogeneous Poisson random measure equals `renewalArrivalMeasure` of its
`ℝ≥0` interarrival gaps, and its `(0, t]` counts agree simultaneously at all times `t` with
`renewalCount` and `renewalCountNat`.

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

/-- For a Poisson random measure on `ℝ≥0` with zero intensity, every interarrival gap is infinite
almost surely. -/
theorem ae_forall_occurrenceGap_eq_top_of_zero
    (h : IsPoissonRandomMeasure P M 0) :
    ∀ᵐ ω ∂P, ∀ n, (M ω).occurrenceGap n = ∞ := by
  filter_upwards [h.ae_eq_zero_measure] with ω hω n
  simp [hω]

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

/-- Simultaneously for all `n`, every interarrival gap of a positive-rate homogeneous Poisson
random measure is strictly positive and finite almost surely. -/
theorem ae_forall_occurrenceGap_pos_lt_top
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ n, 0 < (M ω).occurrenceGap n ∧ (M ω).occurrenceGap n < ∞ :=
  ae_forall_occurrenceGap_pos_lt_top_of_hasLaw (h.hasLaw_toReal_occurrenceGap hr)

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

/-- The extended-valued interarrival gaps of a homogeneous Poisson random measure on `ℝ≥0` are
mutually independent for every rate `r : ℝ≥0`, including rate zero. -/
theorem iIndepFun_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ (M ω).occurrenceGap n) P := by
  have := h.isProbabilityMeasure
  rcases eq_zero_or_pos r with rfl | hr
  · have hzero : IsPoissonRandomMeasure P M 0 := by simpa using h
    have hae := hzero.ae_forall_occurrenceGap_eq_top_of_zero
    exact iIndepFun_of_ae_eq_const_outside_subsingleton (s := ∅) Set.subsingleton_empty
      fun n _ ↦ ⟨∞, hae.mono fun ω hω ↦ hω n⟩
  · have hm : Measurable (fun ω n ↦ ((M ω).occurrenceGap n).toNNReal) :=
      measurable_pi_iff.mpr fun n ↦
        ENNReal.measurable_toNNReal.comp ((Measure.measurable_occurrenceGap n).comp h.measurable)
    have hind_nnreal :
        ProbabilityTheory.iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toNNReal) P :=
      (iIndepFun_iff_hasLaw_Pi_infinitePi (h.hasLaw_toNNReal_occurrenceGap hr)
        hm.aemeasurable).mpr (h.hasLaw_toNNReal_occurrenceGap_infinitePi hr)
    have hcoe := hind_nnreal.comp (fun _ ↦ ((↑) : ℝ≥0 → ℝ≥0∞))
      (fun _ ↦ measurable_coe_nnreal_ennreal)
    refine hcoe.congr fun n ↦ ?_
    filter_upwards [h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hω
    exact ENNReal.coe_toNNReal (hω n).2.ne

/-- The `ℝ≥0`-valued interarrival gaps of a homogeneous Poisson random measure are mutually
independent for every rate `r : ℝ≥0`. For `0 < r` they coincide almost surely with the finite
gaps; at `r = 0` the gaps are almost surely infinite and `toNNReal` maps them to `0`. -/
theorem iIndepFun_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toNNReal) P :=
  h.iIndepFun_occurrenceGap.comp (fun _ ↦ ENNReal.toNNReal) (fun _ ↦ ENNReal.measurable_toNNReal)

/-- The real-valued interarrival gaps of a homogeneous Poisson random measure are mutually
independent for every rate `r : ℝ≥0`. For `0 < r` they coincide almost surely with the finite
gaps; at `r = 0` the gaps are almost surely infinite and `toReal` maps them to `0`. -/
theorem iIndepFun_toReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ ((M ω).occurrenceGap n).toReal) P :=
  h.iIndepFun_occurrenceGap.comp (fun _ ↦ ENNReal.toReal) (fun _ ↦ ENNReal.measurable_toReal)

/-- The full sequence of real-valued interarrival-gap representatives of a positive-rate
homogeneous Poisson random measure has the countable product law of `expMeasure r`. -/
theorem hasLaw_toReal_occurrenceGap_infinitePi
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω n ↦ ((M ω).occurrenceGap n).toReal)
      (Measure.infinitePi fun _ : ℕ ↦ expMeasure r) P := by
  have := h.isProbabilityMeasure
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have hmeas : Measurable fun ω n ↦ ((M ω).occurrenceGap n).toReal :=
    measurable_pi_iff.mpr fun n ↦
      ENNReal.measurable_toReal.comp ((Measure.measurable_occurrenceGap n).comp h.measurable)
  exact h.iIndepFun_toReal_occurrenceGap.hasLaw_infinitePi
    (h.hasLaw_toReal_occurrenceGap hr) hmeas.aemeasurable

/-- The full sequence of extended interarrival gaps of a positive-rate homogeneous Poisson random
measure has the countable product law of `(expMeasure r).map ENNReal.ofReal`. -/
theorem hasLaw_occurrenceGap_infinitePi
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω n ↦ (M ω).occurrenceGap n)
      (Measure.infinitePi fun _ : ℕ ↦ (expMeasure r).map ENNReal.ofReal) P := by
  have := h.isProbabilityMeasure
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  have hmeas : Measurable fun ω n ↦ (M ω).occurrenceGap n :=
    measurable_pi_iff.mpr fun n ↦ (Measure.measurable_occurrenceGap n).comp h.measurable
  exact h.iIndepFun_occurrenceGap.hasLaw_infinitePi
    (h.hasLaw_occurrenceGap hr) hmeas.aemeasurable

/-- Any finite prefix of `ℝ≥0` interarrival-gap representatives of a positive-rate homogeneous
Poisson random measure has the product law of `m` independent `nnrealExpMeasure r` variables. -/
theorem hasLaw_toNNReal_occurrenceGap_prefix
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (m : ℕ) :
    HasLaw (fun ω (i : Fin m) ↦ ((M ω).occurrenceGap i).toNNReal)
      (Measure.pi fun _ : Fin m ↦ nnrealExpMeasure r) P := by
  have := h.isProbabilityMeasure
  have := isProbabilityMeasure_nnrealExpMeasure (NNReal.coe_pos.mpr hr)
  exact (iIndepFun_iff_hasLaw_pi_pi (fun (i : Fin m) ↦ h.hasLaw_toNNReal_occurrenceGap hr i)).mp
    (h.iIndepFun_toNNReal_occurrenceGap.precomp Fin.val_injective)

/-- Any finite prefix of real-valued interarrival-gap representatives of a positive-rate
homogeneous Poisson random measure has the product law of `m` independent `expMeasure r`
variables. -/
theorem hasLaw_toReal_occurrenceGap_prefix
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (m : ℕ) :
    HasLaw (fun ω (i : Fin m) ↦ ((M ω).occurrenceGap i).toReal)
      (Measure.pi fun _ : Fin m ↦ expMeasure r) P := by
  have := h.isProbabilityMeasure
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  exact (iIndepFun_iff_hasLaw_pi_pi (fun (i : Fin m) ↦ h.hasLaw_toReal_occurrenceGap hr i)).mp
    (h.iIndepFun_toReal_occurrenceGap.precomp Fin.val_injective)

/-- Any finite prefix of `ℝ≥0` occurrence-time representatives of a positive-rate homogeneous
Poisson random measure has the law of the cumulative sums of `m` independent `nnrealExpMeasure r`
variables. -/
theorem hasLaw_toNNReal_occurrenceTime_prefix
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (m : ℕ) :
    HasLaw (fun ω (i : Fin m) ↦ ((M ω).occurrenceTime i).toNNReal)
      ((Measure.pi fun _ : Fin m ↦ nnrealExpMeasure r).map
        fun x i ↦ ∑ j ∈ Finset.Iic i, x j) P := by
  have hsum : Measurable (fun (x : Fin m → ℝ≥0) (i : Fin m) ↦ ∑ j ∈ Finset.Iic i, x j) :=
    measurable_pi_iff.mpr fun i ↦ Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j
  refine ((hasLaw_map hsum.aemeasurable).comp
    (h.hasLaw_toNNReal_occurrenceGap_prefix hr m)).congr ?_
  filter_upwards [h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hω
  funext i
  have hfin : (M ω).occurrenceTime i ≠ ∞ :=
    ((M ω).occurrenceGap_ne_top_iff i).mp (hω i).2.ne
  rw [Function.comp_apply, ← Measure.sum_range_toNNReal_occurrenceGap hfin,
    Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, Finset.sum_map]
  rfl

/-- Almost every realization of a positive-rate homogeneous Poisson random measure has strictly
increasing occurrence times. -/
theorem ae_strictMono_occurrenceTime
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, StrictMono (M ω).occurrenceTime := by
  filter_upwards [h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hω
  exact strictMono_nat_of_lt_succ fun n ↦
    (Measure.occurrenceGap_succ_pos_iff
      (((M ω).occurrenceGap_eq_top_iff n).not.mp (hω n).2.ne)).1 (hω (n + 1)).1

/-- Almost every realization of a positive-rate homogeneous Poisson random measure is the sum of
Dirac masses at the partial sums of its interarrival gaps. -/
theorem ae_eq_renewalArrivalMeasure_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, M ω = renewalArrivalMeasure (fun n ω ↦ ((M ω).occurrenceGap n).toNNReal) ω := by
  filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued,
    h.ae_forall_occurrenceGap_pos_lt_top hr] with ω hloc hint hgap
  rw [renewalArrivalMeasure_comp (fun n (ν : Measure ℝ≥0) ↦ (ν.occurrenceGap n).toNNReal) M ω]
  exact eq_renewalArrivalMeasure_toNNReal_occurrenceGap hint
    fun n ↦ ((M ω).occurrenceGap_ne_top_iff n).mp (hgap n).2.ne

/-- For a positive-rate homogeneous Poisson random measure on `ℝ≥0`, almost surely and
simultaneously at all times `t`, the count on `(0, t]` equals the extended renewal count of its
`ℝ≥0` interarrival-gap representatives. -/
theorem ae_forall_Ioc_eq_renewalCount_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ t,
      M ω (Ioc 0 t) = renewalCount (fun n ω' ↦ ((M ω').occurrenceGap n).toNNReal) t ω := by
  have hzero : ∀ᵐ ω ∂P, M ω {0} = 0 := h.ae_eq_zero (A := {0}) (by simp)
  filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued,
    h.ae_forall_occurrenceGap_pos_lt_top hr, hzero] with ω hloc hint hgap h0 t
  have heq : Ioc (0 : ℝ≥0) t = Iic t \ {0} := by
    ext x
    simp [pos_iff_ne_zero, and_comm]
  rw [heq, measure_sdiff_null h0,
    apply_Iic_eq_renewalCount_toNNReal_occurrenceGap hint
      (fun n ↦ ((M ω).occurrenceGap_ne_top_iff n).mp (hgap n).2.ne) t]
  simp only [renewalCount_def, arrival_def]

/-- For a positive-rate homogeneous Poisson random measure on `ℝ≥0`, almost surely and
simultaneously at all times `t`, the count on `(0, t]` equals the natural-valued renewal count
of its `ℝ≥0` interarrival-gap representatives. -/
theorem ae_forall_Ioc_eq_renewalCountNat_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ t, M ω (Ioc 0 t) =
      (renewalCountNat (fun n ω' ↦ ((M ω').occurrenceGap n).toNNReal) t ω : ℝ≥0∞) := by
  have hzero : ∀ᵐ ω ∂P, M ω {0} = 0 := h.ae_eq_zero (A := {0}) (by simp)
  filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued,
    h.ae_forall_occurrenceGap_pos_lt_top hr, hzero] with ω hloc hint hgap h0 t
  have heq : Ioc (0 : ℝ≥0) t = Iic t \ {0} := by
    ext x
    simp [pos_iff_ne_zero, and_comm]
  rw [heq, measure_sdiff_null h0,
    apply_Iic_eq_renewalCountNat_toNNReal_occurrenceGap hint
      (fun n ↦ ((M ω).occurrenceGap_ne_top_iff n).mp (hgap n).2.ne) t,
    renewalCountNat_comp (T := fun n (ν : Measure ℝ≥0) ↦ (ν.occurrenceGap n).toNNReal) M t ω]

/-- For a positive-rate homogeneous Poisson random measure on `ℝ≥0`, almost surely and
simultaneously at all times `t`, the natural floor of the real count on `(0, t]` equals the
natural-valued renewal count of its `ℝ≥0` interarrival-gap representatives. -/
theorem ae_forall_natFloor_Ioc_eq_renewalCountNat_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ t, ⌊(M ω (Ioc 0 t)).toReal⌋₊ =
      renewalCountNat (fun n ω' ↦ ((M ω').occurrenceGap n).toNNReal) t ω := by
  filter_upwards [h.ae_forall_Ioc_eq_renewalCountNat_toNNReal_occurrenceGap hr] with ω hIoc t
  simp [hIoc t]

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
  have hfun : (M ω).occurrenceTime = fun n ↦ (arrival T (n + 1) ω : ℝ≥0∞) := funext fun n ↦ by
    rw [arrival_def, Measure.coe_sum_range_succ_toNNReal_occurrenceGap
      (((M ω).occurrenceGap_eq_top_iff n).not.mp (hωgap n).2.ne)]
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
      ∀ n, HasLaw (fun ω ↦ ((M ω).occurrenceGap n).toReal) (expMeasure r) P :=
  ⟨fun h ↦ ⟨h.ae_isIntegerValued, h.iIndepFun_toReal_occurrenceGap,
      h.hasLaw_toReal_occurrenceGap hr⟩,
    fun ⟨hint, hind, hlaw⟩ ↦
      isPoissonRandomMeasure_smul_nnvolume_of_iIndepFun_toReal_occurrenceGap hM hint hind hlaw⟩

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
