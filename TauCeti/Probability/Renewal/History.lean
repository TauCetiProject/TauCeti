/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Count

/-!
# Renewal histories from completed increments

On a path with `N t = n`, every count through time `t` is determined by
only the first `n` increments. In particular, every event in the natural count history
has, on this slice, a measurable representative in the completed increment prefix.
The representative does not need the straddling increment `T n`.

This reduction applies to the whole history, not just finite-dimensional cylinders.
It permits identities proved for completed-prefix events on each count slice to be
applied to all observed-history events, as needed in renewal restart arguments.
Zero increments and genuine arrivals at time zero are retained. Explosive paths
are included via the count's convention of being zero at every time on those paths.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*,
  vol. II, second edition, Wiley, 1971, Chapter XI.
-/

public section

noncomputable section

open MeasureTheory Filter Function Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {T : ℕ → Ω → ℝ≥0}

/-- On a fixed count slice, any measurable event of the whole count history through
`t` is the pullback of a measurable set of the first `n` increments. No assumption
on the law of the increments is needed. -/
theorem exists_measurableSet_prefix_renewalCountNat_history (t : ℝ≥0) (n : ℕ)
    {A : Set (Iic t → ℕ)} (hA : MeasurableSet A) :
    ∃ B : Set (Fin n → ℝ≥0), MeasurableSet B ∧
      ∀ ω, renewalCountNat T t ω = n →
        ((fun s : Iic t ↦ renewalCountNat T s ω) ∈ A ↔
          (fun i : Fin n ↦ T i ω) ∈ B) := by
  classical
  -- Pad a finite prefix by zeros; only arrivals with index at most n are used.
  let extend (w : Fin n → ℝ≥0) (k : ℕ) : ℝ≥0 :=
    if h : k < n then w ⟨k, h⟩ else 0
  let history (w : Fin n → ℝ≥0) (s : Iic t) : ℕ :=
    ∑ k ∈ Finset.range n, if arrival (fun k w ↦ extend w k) (k + 1) w ≤ s then 1 else 0
  have hm : Measurable history := by
    refine measurable_pi_iff.2 fun s ↦ Finset.measurable_fun_sum _ fun k _ ↦ ?_
    refine Measurable.ite (measurableSet_le (measurable_arrival ?_ _) measurable_const)
      measurable_const measurable_const
    intro k
    dsimp [extend]
    split_ifs <;> fun_prop
  refine ⟨history ⁻¹' A, hm hA, ?_⟩
  intro ω hn
  have harr (k : ℕ) (hk : k ≤ n) :
      arrival (fun k w ↦ extend w k) k (fun i : Fin n ↦ T i ω) = arrival T k ω := by
    simp only [arrival_def]
    apply Finset.sum_congr rfl
    intro i hi
    simp [extend, (Finset.mem_range.1 hi).trans_le hk]
  have heq : history (fun i : Fin n ↦ T i ω) =
      (fun s : Iic t ↦ renewalCountNat T s ω) := by
    funext s
    rw [renewalCountNat_eq_sum_range_of_le s.property, hn]
    exact Finset.sum_congr rfl fun k hk ↦ by
      rw [harr (k + 1) (by simpa using Finset.mem_range.1 hk)]
  simp only [mem_preimage, heq]

/-- Every event in the natural count history has completed-prefix representatives
on all count slices, for every path. The sigma-algebra
is explicitly the pullback of the entire history, so this includes events depending
on infinitely many observation times. -/
theorem exists_measurableSet_prefix_of_mem_renewalCountNat_history (t : ℝ≥0)
    {A : Set Ω}
    (hA : MeasurableSet[MeasurableSpace.comap
      (fun ω (s : Iic t) ↦ renewalCountNat T s ω) inferInstance] A) :
    ∃ B : (n : ℕ) → Set (Fin n → ℝ≥0), (∀ n, MeasurableSet (B n)) ∧
      ∀ ω, ω ∈ A ↔ ∃ n, renewalCountNat T t ω = n ∧ (fun i : Fin n ↦ T i ω) ∈ B n := by
  obtain ⟨C, hC, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
  choose B hB hrepr using fun n ↦
    exists_measurableSet_prefix_renewalCountNat_history (T := T) t n hC
  refine ⟨B, hB, fun ω ↦ ?_⟩
  constructor
  · intro h
    exact ⟨renewalCountNat T t ω, rfl, (hrepr _ ω rfl).1 h⟩
  · rintro ⟨n, hn, h⟩
    exact (hrepr n ω hn).2 h

/-- Factorization on every completed-prefix count slice extends to the entire natural
count history, with the same constant factor `c`. This permits identification of a
restart law before its marginal law has been established. No almost-sure path
hypothesis is needed. -/
theorem measure_inter_eq_mul_of_renewal_prefix_slices [MeasurableSpace Ω]
    {P : Measure Ω} (hT : ∀ n, Measurable (T n)) (t : ℝ≥0)
    {C : Set Ω} (hC : MeasurableSet C) (c : ℝ≥0∞)
    (hfactor : ∀ (n : ℕ) (B : Set (Fin n → ℝ≥0)), MeasurableSet B →
      P ({ω | renewalCountNat T t ω = n ∧ (fun i : Fin n ↦ T i ω) ∈ B} ∩ C) =
        P {ω | renewalCountNat T t ω = n ∧ (fun i : Fin n ↦ T i ω) ∈ B} * c)
    {A : Set Ω}
    (hA : MeasurableSet[MeasurableSpace.comap
      (fun ω (s : Iic t) ↦ renewalCountNat T s ω) inferInstance] A) :
    P (A ∩ C) = P A * c := by
  obtain ⟨B, hB, hrepr⟩ :=
    exists_measurableSet_prefix_of_mem_renewalCountNat_history t hA
  let D (n : ℕ) : Set Ω :=
    {ω | renewalCountNat T t ω = n ∧ (fun i : Fin n ↦ T i ω) ∈ B n}
  have hm (n : ℕ) : MeasurableSet (D n) :=
    ((measurable_renewalCountNat hT t) (measurableSet_singleton n)).inter
      ((measurable_pi_iff.2 fun i : Fin n ↦ hT i) (hB n))
  have hd : Pairwise (Disjoint on D) := by
    intro i j hij
    exact disjoint_left.2 fun ω hi hj ↦ hij (hi.1.symm.trans hj.1)
  have hunion : A = ⋃ n, D n := by
    ext ω
    simpa only [mem_iUnion, D, mem_ofPred_eq] using hrepr ω
  calc
    P (A ∩ C) = P ((⋃ n, D n) ∩ C) := by rw [hunion]
    _ = ∑' n, P (D n ∩ C) := by
      rw [iUnion_inter]
      exact measure_iUnion (fun i j hij ↦ (hd hij).mono inter_subset_left inter_subset_left)
        (fun n ↦ (hm n).inter hC)
    _ = ∑' n, P (D n) * c := tsum_congr fun n ↦ hfactor n (B n) (hB n)
    _ = P (⋃ n, D n) * c := by rw [ENNReal.tsum_mul_right, measure_iUnion hd hm]
    _ = P A * c := by rw [hunion]

end TauCeti.Probability
