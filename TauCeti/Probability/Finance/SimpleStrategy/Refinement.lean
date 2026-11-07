/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import Mathlib.Data.Finset.Sort
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Common trading grids

Finite sums of elementary predictable holdings can have overlapping intervals and different
trading dates. They can nevertheless be represented by one simple strategy: sort all endpoints
and add the active positions on each successive interval. Each new position is measurable at
the left endpoint of its interval, since every position contributing to it was chosen earlier.

`simpleHolding_eq_sum_Ioc` gives the representation on a supplied grid, and
`exists_simpleHolding_sum_Ioc` constructs such a grid for any finite family. The latter starts
at the bottom time and has strictly increasing dates, including when some input intervals are
empty or reversed. This bridges finite sums of predictable rectangles and finite-grid trading
strategies, so that approximation by the former can be used with elementary trading formulas.
All equalities are pointwise, including at trading dates; no measure or price process is needed.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, 2nd ed., Springer, 2005,
  §II.2.
-/

public section

noncomputable section

open Finset MeasureTheory

namespace TauCeti.Finance

variable {Ω ι κ : Type*} [LinearOrder ι]

/-- Refining finitely many intervals to a nondecreasing grid amounts to adding the
positions whose endpoint indices cover each grid interval. The input intervals may overlap,
be empty, or have their endpoints reversed. -/
theorem simpleHolding_eq_sum_Ioc (s : Finset κ) {τ : ℕ → ι} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (l u : κ → ℕ)
    (hl : ∀ i ∈ s, l i ≤ n) (hu : ∀ i ∈ s, u i ≤ n)
    (a : κ → Ω → ℝ) (t : ι) (ω : Ω) :
    simpleHolding τ n (fun j ω ↦ ∑ i ∈ s, if l i ≤ j ∧ j < u i then a i ω else 0) t ω =
      ∑ i ∈ s, (Set.Ioc (τ (l i)) (τ (u i))).indicator (fun _ ↦ a i ω) t := by
  classical
  by_cases ht : t ∈ Set.Ioc (τ 0) (τ n)
  · obtain ⟨j, hj, htj⟩ : ∃ j < n, t ∈ Set.Ioc (τ j) (τ (j + 1)) := by
      have hcover :=
        (Set.monotoneOn_iff_monotone.1 hτ).IicExtend.biUnion_Ico_Ioc_map_succ 0 n
      simp only [Set.IicExtend_apply, Nat.min_zero, min_self, Order.succ_eq_add_one,
        Set.mem_Ico, Nat.zero_le, true_and] at hcover
      rw [← hcover] at ht
      simp only [Set.mem_iUnion, exists_prop] at ht
      obtain ⟨j, hj, htj⟩ := ht
      rw [min_eq_right hj.le, min_eq_right (Nat.add_one_le_of_lt hj)] at htj
      exact ⟨j, hj, htj⟩
    rw [simpleHolding_of_mem_Ioc hτ hj htj]
    refine sum_congr rfl fun i hi ↦ ?_
    have hmem : t ∈ Set.Ioc (τ (l i)) (τ (u i)) ↔ l i ≤ j ∧ j < u i := by
      constructor
      · intro h
        constructor
        · by_contra hlj
          exact h.1.not_ge (htj.2.trans (hτ hj (hl i hi) (by omega)))
        · by_contra hju
          exact htj.1.not_ge (h.2.trans (hτ (hu i hi) hj.le (by omega)))
      · rintro ⟨hlj, hju⟩
        exact ⟨(hτ (hl i hi) hj.le hlj).trans_lt htj.1,
          htj.2.trans (hτ hj (hu i hi) hju)⟩
    by_cases h : l i ≤ j ∧ j < u i <;> simp [h, hmem]
  · rw [simpleHolding_of_notMem_Ioc hτ ht]
    symm
    refine sum_eq_zero fun i hi ↦ Set.indicator_of_notMem (fun h ↦ ht ?_) _
    exact ⟨(hτ (Nat.zero_le n) (hl i hi) (Nat.zero_le _)).trans_lt h.1,
      h.2.trans (hτ (hu i hi) Set.self_mem_Iic (hu i hi))⟩

/-- A finite family of interval positions, each known at its own left endpoint, can be put on
one strictly increasing trading grid starting at the bottom time. The resulting positions are
known at the new left endpoints, and the holding processes agree at every time and sample.
No order relation between the two endpoints of an input interval is required. -/
theorem exists_simpleHolding_sum_Ioc [OrderBot ι] {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) (s : Finset κ) (l u : κ → ι) (a : κ → Ω → ℝ)
    (ha : ∀ i ∈ s, StronglyMeasurable[ℱ (l i)] (a i)) :
    ∃ (n : ℕ) (τ : ℕ → ι) (b : ℕ → Ω → ℝ),
      τ 0 = ⊥ ∧ StrictMonoOn τ (Set.Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (b j)) ∧
      ∀ t ω, simpleHolding τ n b t ω =
        ∑ i ∈ s, (Set.Ioc (l i) (u i)).indicator (fun _ ↦ a i ω) t := by
  classical
  -- Sort the distinct endpoints, including the initial time, and freeze the grid after its end.
  let d := insert ⊥ (s.image l ∪ s.image u)
  have hd : 0 < d.card := card_pos.mpr ⟨⊥, mem_insert_self _ _⟩
  let n := d.card - 1
  have hn : n + 1 = d.card := by omega
  let e := d.orderIsoOfFin hn.symm
  let τ : ℕ → ι := fun j ↦ (e ⟨min j n, by omega⟩ : ι)
  have hτj (j : ℕ) (hj : j ≤ n) : τ j = (e ⟨j, by omega⟩ : ι) := by
    simp [τ, min_eq_left hj]
  have hτ : StrictMonoOn τ (Set.Iic n) := by
    intro i hi j hj hij
    rw [hτj i hi, hτj j hj]
    exact e.strictMono hij
  have hsurj : ∀ x ∈ d, ∃ j ≤ n, τ j = x := by
    intro x hx
    let j := e.symm ⟨x, hx⟩
    refine ⟨j, by omega, ?_⟩
    rw [hτj j (by omega)]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  have hzero : τ 0 = ⊥ := by
    obtain ⟨j, hj, heq⟩ := hsurj ⊥ (mem_insert_self _ _)
    exact le_bot_iff.mp (heq ▸ hτ.monotoneOn (Nat.zero_le n) hj (Nat.zero_le j))
  -- Locate each old endpoint on the new grid.
  have hleft : ∀ i ∈ s, ∃ j ≤ n, τ j = l i := by
    intro i hi
    exact hsurj _ (mem_insert_of_mem (mem_union_left _ (mem_image_of_mem l hi)))
  have hright : ∀ i ∈ s, ∃ j ≤ n, τ j = u i := by
    intro i hi
    exact hsurj _ (mem_insert_of_mem (mem_union_right _ (mem_image_of_mem u hi)))
  let L (i : κ) : ℕ := if hi : i ∈ s then (hleft i hi).choose else 0
  let U (i : κ) : ℕ := if hi : i ∈ s then (hright i hi).choose else 0
  have hL (i : κ) (hi : i ∈ s) : L i ≤ n ∧ τ (L i) = l i := by
    simpa [L, hi] using (hleft i hi).choose_spec
  have hU (i : κ) (hi : i ∈ s) : U i ≤ n ∧ τ (U i) = u i := by
    simpa [U, hi] using (hright i hi).choose_spec
  -- Only positions already chosen at the new left endpoint contribute to its height.
  let b (j : ℕ) (ω : Ω) := ∑ i ∈ s, if L i ≤ j ∧ j < U i then a i ω else 0
  refine ⟨n, τ, b, hzero, hτ, ?_, ?_⟩
  · intro j hj
    refine Finset.stronglyMeasurable_fun_sum _ fun i hi ↦ ?_
    by_cases hij : L i ≤ j ∧ j < U i
    · have hle : l i ≤ τ j := (hL i hi).2 ▸
        hτ.monotoneOn (hL i hi).1 hj.le hij.1
      simpa [hij] using (ha i hi).mono (ℱ.mono hle)
    · simpa [hij] using (stronglyMeasurable_const (b := (0 : ℝ)) :
        StronglyMeasurable[ℱ (τ j)] (fun _ : Ω ↦ (0 : ℝ)))
  · intro t ω
    rw [simpleHolding_eq_sum_Ioc s hτ.monotoneOn L U (fun i hi ↦ (hL i hi).1)
      (fun i hi ↦ (hU i hi).1)]
    exact sum_congr rfl fun i hi ↦ by rw [(hL i hi).2, (hU i hi).2]

end TauCeti.Finance
