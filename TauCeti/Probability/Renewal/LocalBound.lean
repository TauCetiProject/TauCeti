/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Independence.DisjointBlocks
public import TauCeti.Probability.Renewal.Measure
import Mathlib.Algebra.Order.Floor.Semiring
import TauCeti.Probability.Independence.InfinitePi

/-!
# The local renewal bound

Let `U = ∑ n, F^{∗n}` be the renewal measure of a probability measure `F` on `ℝ≥0`, with the
artificial arrival `F^{∗0} = δ₀` included. This file proves the local renewal bound

```text
U [t, t + h] ≤ U [0, h]        for all t, h ≥ 0:
```

among the intervals of length `h`, the one starting at zero has the largest renewal mass. No
assumption is made on the atom of `F` at zero or on its mean; both sides may be infinite. In terms
of the renewal function `m`, the bound controls the renewal increments uniformly in time,
`m (t + h) ≤ m t + U [0, h]`. When `F {0} < 1` the right side is finite
(`MeasureTheory.Measure.renewalMeasure_Iic_lt_top`), so the increments of `m` over intervals of
length `h` are bounded independently of `t`. This is the a priori estimate behind Blackwell's
renewal theorem and the key renewal theorem.

## Main results

* `MeasureTheory.Measure.renewalMeasure_Icc_add_le` — the local renewal bound
  `U [t, t + h] ≤ U [0, h]`.
* `MeasureTheory.Measure.renewalFunction_add_le` — the uniform increment bound
  `m (t + h) ≤ m t + U [0, h]`.
* `MeasureTheory.Measure.renewalMeasure_Iic_le_add_one_mul` — the linear-growth bound
  `U [0, u] ≤ (u + 1) * U [0, 1]`.
* `MeasureTheory.Measure.lintegral_renewalMeasure_Iic_lt_top` — a finite-mean integrable
  envelope for backward-window masses.

## Implementation notes

The bound is proved by conditioning at the first arrival at or after `t`. Realize `F` as the law of
independent increments `T 0, T 1, …` with arrival times `S n`, so that `U s` is the expected number
of indices `n ≥ 0` with `S n ∈ s`. Let `E m` be the event that `m` is the first index with
`t ≤ S m`; it depends only on `T 0, …, T (m - 1)`. On `E m`, an index `n` with `S n ∈ [t, t + h]`
has the form `n = m + k` with `S (m + k) - S m ≤ h`, and `S (m + k) - S m` is the `k`-th arrival
time of the process restarted at the `m`-th arrival, which is independent of `E m` and has the
same law as `S k`. Summing over `m` and `k` gives `U [t, t + h] ≤ P (⋃ m, E m) * U [0, h]`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {T : ℕ → Ω → ℝ≥0} {t h : ℝ≥0}

/-- The event that `m` is the first index with `t ≤ arrival T m`. -/
private def firstArrivalGE (T : ℕ → Ω → ℝ≥0) (t : ℝ≥0) (m : ℕ) : Set Ω :=
  {ω | t ≤ arrival T m ω ∧ ∀ j < m, arrival T j ω < t}

private theorem pairwise_disjoint_firstArrivalGE :
    Pairwise (Function.onFun Disjoint (firstArrivalGE T t)) := by
  intro m m' hmm'
  refine Set.disjoint_left.2 fun ω hm hm' ↦ ?_
  rcases lt_or_gt_of_ne hmm' with hlt | hlt
  · exact (hm'.2 m hlt).not_ge hm.1
  · exact (hm.2 m' hlt).not_ge hm'.1

/-- The first index with `t ≤ arrival T m` is determined by the increments `T 0, …, T (m - 1)`. -/
private theorem measurableSet_firstArrivalGE (m : ℕ) :
    MeasurableSet[blockSigma T (Iio m)] (firstArrivalGE T t m) := by
  have harr {j : ℕ} (hj : j ≤ m) : Measurable[blockSigma T (Iio m)] (arrival T j) :=
    measurable_arrival_of_lt fun i hi ↦ measurable_blockSigma_of_mem (hi.trans_le hj)
  simp only [firstArrivalGE, ofPred_and, ofPred_forall]
  refine (measurableSet_le measurable_const (harr le_rfl)).inter ?_
  exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun hj ↦
    measurableSet_lt (harr hj.le) measurable_const

/-- Every arrival time in `[t, t + h]` comes at or after the first index with `t ≤ arrival T m`. -/
private theorem preimage_arrival_Icc_subset_iUnion_firstArrivalGE (n : ℕ) :
    arrival T n ⁻¹' Icc t (t + h) ⊆ ⋃ m, firstArrivalGE T t m := by
  intro ω hω
  have hex : ∃ m, t ≤ arrival T m ω := ⟨n, hω.1⟩
  exact mem_iUnion.2 ⟨Nat.find hex, Nat.find_spec hex, fun j hj ↦ not_le.1 (Nat.find_min hex hj)⟩

private theorem preimage_arrival_Icc_inter_firstArrivalGE_of_lt {n m : ℕ} (hn : n < m) :
    arrival T n ⁻¹' Icc t (t + h) ∩ firstArrivalGE T t m = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hω ↦ (hω.2.2 n hn).not_ge hω.1.1

/-- If `m` is the first index with `t ≤ arrival T m` and `arrival T (k + m) ≤ t + h`, then the
restarted process has its `k`-th arrival by time `h`. -/
private theorem preimage_arrival_Icc_inter_firstArrivalGE_subset (m k : ℕ) :
    arrival T (k + m) ⁻¹' Icc t (t + h) ∩ firstArrivalGE T t m ⊆
      firstArrivalGE T t m ∩ arrival (fun i ↦ T (m + i)) k ⁻¹' Iic h := by
  rintro ω ⟨hω, hE⟩
  refine ⟨hE, ?_⟩
  have hle := hω.2
  rw [Nat.add_comm k m, arrival_add] at hle
  refine le_of_add_le_add_left (a := t) ?_
  calc t + arrival (fun i ↦ T (m + i)) k ω
      ≤ arrival T m ω + arrival (fun i ↦ T (m + i)) k ω := by gcongr; exact hE.1
    _ ≤ t + h := hle

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- The local renewal bound for the law of independent, identically distributed increments. -/
private theorem renewalMeasure_map_Icc_add_le (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (t h : ℝ≥0) :
    (P.map (T 0)).renewalMeasure (Icc t (t + h)) ≤ (P.map (T 0)).renewalMeasure (Iic h) := by
  have := hindep.isProbabilityMeasure
  set F := P.map (T 0)
  set E := firstArrivalGE T t
  have hlaw (m k : ℕ) {s : Set ℝ≥0} (hs : MeasurableSet s) :
      P (arrival (fun i ↦ T (m + i)) k ⁻¹' s) = F.convolutionPower k s := by
    rw [← (hasLaw_arrival_shift hindep hid m k).map_eq,
      Measure.map_apply (measurable_arrival (fun i ↦ hT (m + i)) k) hs]
  have hEm (m : ℕ) : MeasurableSet (E m) :=
    blockSigma_le (Iio m) (fun i _ ↦ hT i) _ (measurableSet_firstArrivalGE m)
  -- The restarted process is independent of `E m`.
  have hindep_E (m k : ℕ) : P (E m ∩ arrival (fun i ↦ T (m + i)) k ⁻¹' Iic h) =
      P (E m) * F.convolutionPower k (Iic h) := by
    have hI : Indep (blockSigma T (Iio m)) (blockSigma T (Ici m)) P :=
      indep_blockSigma_of_disjoint hindep hT (Iio_disjoint_Ici le_rfl)
    have hD : Measurable[blockSigma T (Ici m)] (arrival (fun i ↦ T (m + i)) k) :=
      measurable_arrival_of_lt fun i _ ↦ measurable_blockSigma_of_mem (by simp)
    rw [(Indep_iff _ _ P).1 hI _ _ (measurableSet_firstArrivalGE m) (hD measurableSet_Iic),
      hlaw m k measurableSet_Iic]
  have hA : MeasurableSet (Icc t (t + h)) := measurableSet_Icc
  calc F.renewalMeasure (Icc t (t + h))
      = ∑' n, P (arrival T n ⁻¹' Icc t (t + h)) := by
        rw [Measure.renewalMeasure_apply _]
        exact tsum_congr fun n ↦ by simpa using (hlaw 0 n hA).symm
    -- split according to the first index `m` with `t ≤ arrival T m`
    _ = ∑' n, ∑' m, P (arrival T n ⁻¹' Icc t (t + h) ∩ E m) := by
        refine tsum_congr fun n ↦ ?_
        rw [← measure_iUnion (fun i j hij ↦ (pairwise_disjoint_firstArrivalGE hij).mono
          inter_subset_right inter_subset_right) fun m ↦ (measurable_arrival hT n hA).inter (hEm m),
          ← inter_iUnion, inter_eq_left.2 (preimage_arrival_Icc_subset_iUnion_firstArrivalGE n)]
    -- only the indices `n = k + m` contribute
    _ = ∑' m, ∑' k, P (arrival T (k + m) ⁻¹' Icc t (t + h) ∩ E m) := by
        rw [_root_.tsum_comm]
        refine tsum_congr fun m ↦ ?_
        rw [← CompleteLattice.summable.sum_add_tsum_nat_add' (k := m),
          Finset.sum_eq_zero fun n hn ↦ by
            rw [preimage_arrival_Icc_inter_firstArrivalGE_of_lt (Finset.mem_range.1 hn),
              measure_empty],
          zero_add]
    _ ≤ ∑' m, ∑' k, P (E m ∩ arrival (fun i ↦ T (m + i)) k ⁻¹' Iic h) :=
        _root_.tsum_le_tsum fun m ↦ _root_.tsum_le_tsum fun k ↦
          measure_mono (preimage_arrival_Icc_inter_firstArrivalGE_subset m k)
    _ = ∑' m, P (E m) * F.renewalMeasure (Iic h) := by
        refine tsum_congr fun m ↦ ?_
        simp_rw [hindep_E, ENNReal.tsum_mul_left, Measure.renewalMeasure_apply]
    _ = P (⋃ m, E m) * F.renewalMeasure (Iic h) := by
        rw [ENNReal.tsum_mul_right, measure_iUnion pairwise_disjoint_firstArrivalGE hEm]
    _ ≤ F.renewalMeasure (Iic h) := mul_le_of_le_one_left' prob_le_one

end TauCeti.Probability

namespace MeasureTheory.Measure

variable (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]

/-- **The local renewal bound.** For a probability measure `μ` on `ℝ≥0`, the renewal measure `U` of
`μ` gives the interval `[t, t + h]` at most the mass it gives `[0, h]`. Both sides count the point
mass `μ^{∗0} = δ₀`, and both may be infinite: no assumption is made on the atom of `μ` at zero or on
its mean. -/
theorem renewalMeasure_Icc_add_le (t h : ℝ≥0) :
    μ.renewalMeasure (Icc t (t + h)) ≤ μ.renewalMeasure (Iic h) := by
  -- Realize i.i.d. increments with law `μ` as the coordinates of the product measure.
  set P := Measure.infinitePi fun _ : ℕ ↦ μ
  have hT : ∀ n, Measurable fun w : ℕ → ℝ≥0 ↦ w n := measurable_pi_apply
  have hindep : iIndepFun _ P := TauCeti.Probability.iIndepFun_eval_infinitePi _
  have hid (n : ℕ) : IdentDistrib _ _ P P := μ.identDistrib_eval_infinitePi n 0
  have hmap : ∀ n, P.map (fun w ↦ w n) = μ := fun n ↦ infinitePi_map_eval _ n
  simpa only [hmap 0] using TauCeti.Probability.renewalMeasure_map_Icc_add_le hT hindep hid t h

/-- **Uniform bound on the renewal increments.** For a probability measure `μ` on `ℝ≥0`, the
renewal function grows by at most `U [0, h]` over any time interval of length `h`, where `U` is
the renewal measure of `μ`. When `μ {0} < 1` the bound is finite
(`MeasureTheory.Measure.renewalMeasure_Iic_lt_top`). -/
theorem renewalFunction_add_le (t h : ℝ≥0) :
    μ.renewalFunction (t + h) ≤ μ.renewalFunction t + μ.renewalMeasure (Iic h) := by
  have hsplit : Iic (t + h) ⊆ Iic t ∪ Icc t (t + h) := fun x hx ↦
    (le_total x t).imp id fun hxt ↦ ⟨hxt, hx⟩
  refine (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 ?_
  calc 1 + μ.renewalFunction (t + h) = μ.renewalMeasure (Iic (t + h)) :=
        (renewalMeasure_Iic μ _).symm
    _ ≤ μ.renewalMeasure (Iic t) + μ.renewalMeasure (Icc t (t + h)) :=
        (measure_mono hsplit).trans (measure_union_le _ _)
    _ ≤ μ.renewalMeasure (Iic t) + μ.renewalMeasure (Iic h) :=
        add_le_add le_rfl (renewalMeasure_Icc_add_le μ t h)
    _ = 1 + (μ.renewalFunction t + μ.renewalMeasure (Iic h)) := by
        rw [renewalMeasure_Iic, add_assoc]

/-- The renewal mass of `[0, u]` grows at most linearly, with bound
`U [0, u] ≤ (u + 1) * U [0, 1]`. No assumption on the atom at zero or the mean is needed;
both sides may be infinite. -/
theorem renewalMeasure_Iic_le_add_one_mul (u : ℝ≥0) :
    μ.renewalMeasure (Iic u) ≤ ((u : ℝ≥0∞) + 1) * μ.renewalMeasure (Iic 1) := by
  have hcover : Iic u ⊆ ⋃ k ∈ Finset.range (⌊u⌋₊ + 1),
      Icc (k : ℝ≥0) (k + 1) := by
    intro s hs
    simp only [mem_iUnion, Finset.mem_range, mem_Icc]
    exact ⟨⌊s⌋₊, Nat.lt_succ_of_le (Nat.floor_mono hs),
      Nat.floor_le (by positivity), (Nat.lt_floor_add_one s).le⟩
  calc
    _ ≤ ∑ k ∈ Finset.range (⌊u⌋₊ + 1),
        μ.renewalMeasure (Icc (k : ℝ≥0) (k + 1)) :=
      (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _k ∈ Finset.range (⌊u⌋₊ + 1), μ.renewalMeasure (Iic 1) :=
      Finset.sum_le_sum fun k _ ↦ μ.renewalMeasure_Icc_add_le k 1
    _ = ((⌊u⌋₊ : ℝ≥0∞) + 1) * μ.renewalMeasure (Iic 1) := by simp
    _ ≤ _ := by
      gcongr
      exact_mod_cast Nat.floor_le (a := u) (by positivity)

/-- A finite-mean gap law integrates the renewal mass of its initial intervals.
This is an integrable envelope for all backward windows of the same lengths. -/
theorem lintegral_renewalMeasure_Iic_lt_top (hμ : μ {0} < 1)
    (hmean : (∫⁻ u, (u : ℝ≥0∞) ∂μ) ≠ ∞) :
    ∫⁻ u, μ.renewalMeasure (Iic u) ∂μ < ∞ := by
  calc
    _ ≤ ∫⁻ u, ((u : ℝ≥0∞) + 1) * μ.renewalMeasure (Iic 1) ∂μ :=
      lintegral_mono μ.renewalMeasure_Iic_le_add_one_mul
    _ < ∞ := by
      rw [lintegral_mul_const _ (by fun_prop), lintegral_add_left (by fun_prop)]
      simp only [lintegral_const, measure_univ, mul_one]
      exact ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨hmean.lt_top, by simp⟩)
        (μ.renewalMeasure_Iic_lt_top hμ 1)

end MeasureTheory.Measure
