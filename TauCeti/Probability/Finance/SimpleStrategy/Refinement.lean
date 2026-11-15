/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Data.Finset.Sort

/-!
# Common trading grids

Finite sums of elementary predictable holdings can have overlapping intervals and different
trading dates. They can nevertheless be represented by one simple strategy: sort all endpoints
and add the active positions on each successive interval. Each new position is measurable at
the left endpoint of its interval, since every position contributing to it was chosen earlier.

`simpleHolding_eq_sum_indicator_Ioc` and `simpleGains_eq_sum_mul_sub` give the holdings and
integrals on a supplied grid. `exists_simpleHolding_simpleGains_eq_sum` constructs one grid for
any finite family, preserving both holdings and gains against every price path. It starts at the
bottom time and has strictly increasing dates, including when some input intervals are empty or
reversed. The new heights are bounded pointwise by the sum of the original absolute heights;
thus boundedness and Lᵖ control survive refinement without additional moment assumptions.

This bridges finite sums of predictable rectangles and finite-grid trading strategies. In
particular, `exists_simpleHolding_simpleGains_add` and `exists_simpleHolding_simpleGains_sub`
evaluate sums and differences of elementary stochastic-integral approximants on one common grid
before applying an isometry or energy estimate. All equalities are pointwise, including at
trading dates, with no regularity assumption on the price path.

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
theorem simpleHolding_eq_sum_indicator_Ioc (s : Finset κ) {τ : ℕ → ι} {n : ℕ}
    (hτ : MonotoneOn τ (Set.Iic n)) (l u : κ → ℕ)
    (hl : ∀ i ∈ s, l i ≤ n) (hu : ∀ i ∈ s, u i ≤ n)
    (a : κ → Ω → ℝ) (t : ι) (ω : Ω) :
    simpleHolding τ n (fun j ω ↦ ∑ i ∈ s, if l i ≤ j ∧ j < u i then a i ω else 0) t ω =
      ∑ i ∈ s, (Set.Ioc (τ (l i)) (τ (u i))).indicator (fun _ ↦ a i ω) t := by
  classical
  by_cases ht : t ∈ Set.Ioc (τ 0) (τ n)
  · obtain ⟨j, hj, htj⟩ := exists_lt_mem_Ioc_of_mem_Ioc ht
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

/-- Refinement preserves elementary integrals against every price path. Each position covers
successive grid intervals, so its increments telescope, even at an intermediate observation
time. Reversed endpoint indices contribute zero, as do empty intervals. No monotonicity of the
grid or regularity of the price is needed for this algebraic identity. -/
theorem simpleGains_eq_sum_mul_sub (s : Finset κ) (τ : ℕ → ι) (n : ℕ)
    (l u : κ → ℕ) (hu : ∀ i ∈ s, u i ≤ n) (a : κ → Ω → ℝ)
    (X : ι → Ω → ℝ) (t : ι) (ω : Ω) :
    simpleGains τ n (fun j ω ↦ ∑ i ∈ s, if l i ≤ j ∧ j < u i then a i ω else 0) X t ω =
      ∑ i ∈ s, if l i ≤ u i then
        a i ω * (X (min (τ (u i)) t) ω - X (min (τ (l i)) t) ω) else 0 := by
  classical
  rw [simpleGains_def]
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi ↦ ?_
  have hfilter : (range n).filter (fun j ↦ l i ≤ j ∧ j < u i) = Ico (l i) (u i) := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico]
    have := hu i hi
    omega
  simp_rw [ite_mul, zero_mul]
  rw [← sum_filter, hfilter]
  by_cases hlu : l i ≤ u i
  · rw [ite_eq_left hlu, ← mul_sum,
      sum_Ico_sub (fun j ↦ X (min (τ j) t) ω) hlu]
  · simp [hlu, Ico_eq_empty_of_le (Nat.le_of_not_ge hlu)]

/-- A finite family of left-measurable interval positions has one strictly increasing common
grid, preserving holdings and gains against every price path. Its heights are bounded by the
sum of the original absolute heights, so refinement preserves boundedness and Lᵖ control.
The grid starts at the bottom time. Empty or reversed intervals contribute no holdings or gains;
for a reversed interval the displayed increment must therefore be suppressed. -/
theorem exists_simpleHolding_simpleGains_eq_sum [OrderBot ι] {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) (s : Finset κ) (l u : κ → ι) (a : κ → Ω → ℝ)
    (ha : ∀ i ∈ s, StronglyMeasurable[ℱ (l i)] (a i)) :
    ∃ (n : ℕ) (τ : ℕ → ι) (b : ℕ → Ω → ℝ),
      τ 0 = ⊥ ∧ StrictMonoOn τ (Set.Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (b j)) ∧
      (∀ j < n, ∀ ω, ‖b j ω‖ ≤ ∑ i ∈ s, ‖a i ω‖) ∧
      (∀ t ω, simpleHolding τ n b t ω =
        ∑ i ∈ s, (Set.Ioc (l i) (u i)).indicator (fun _ ↦ a i ω) t) ∧
      ∀ (X : ι → Ω → ℝ) t ω, simpleGains τ n b X t ω =
        ∑ i ∈ s, if l i ≤ u i then
          a i ω * (X (min (u i) t) ω - X (min (l i) t) ω) else 0 := by
  classical
  -- Sort the distinct endpoints, including the initial time.
  let d := insert ⊥ (s.image l ∪ s.image u)
  obtain ⟨τ, -, hτ, -, himage, -⟩ :=
    d.exists_strictMonoOn_Iic_surj ⟨⊥, mem_insert_self _ _⟩
  let n := d.card - 1
  have hsurj (x : ι) (hx : x ∈ d) : ∃ j ≤ n, τ j = x := by
    have hximage : x ∈ τ '' Set.Iic n := by
      rw [himage]
      exact hx
    exact hximage
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
  refine ⟨n, τ, b, hzero, hτ, ?_, ?_, ?_, ?_⟩
  · intro j hj
    refine Finset.stronglyMeasurable_fun_sum _ fun i hi ↦ ?_
    by_cases hij : L i ≤ j ∧ j < U i
    · have hle : l i ≤ τ j := (hL i hi).2 ▸
        hτ.monotoneOn (hL i hi).1 hj.le hij.1
      simpa [hij] using (ha i hi).mono (ℱ.mono hle)
    · simpa [hij] using (stronglyMeasurable_const (b := (0 : ℝ)) :
        StronglyMeasurable[ℱ (τ j)] (fun _ : Ω ↦ (0 : ℝ)))
  · intro j _ ω
    exact (norm_sum_le _ _).trans (sum_le_sum fun i _ ↦ by
      split_ifs <;> simp)
  · intro t ω
    rw [simpleHolding_eq_sum_indicator_Ioc s hτ.monotoneOn L U (fun i hi ↦ (hL i hi).1)
      (fun i hi ↦ (hU i hi).1)]
    exact sum_congr rfl fun i hi ↦ by rw [(hL i hi).2, (hU i hi).2]
  · intro X t ω
    rw [simpleGains_eq_sum_mul_sub s τ n L U (fun i hi ↦ (hU i hi).1)]
    refine sum_congr rfl fun i hi ↦ ?_
    have horder : L i ≤ U i ↔ l i ≤ u i := by
      rw [← (hL i hi).2, ← (hU i hi).2]
      exact hτ.le_iff_le (hL i hi).1 (hU i hi).1 |>.symm
    simp only [horder, (hL i hi).2, (hU i hi).2]

/-- Two left-measurable simple strategies admit a single strictly increasing common grid starting
at `⊥` whose holdings and gains against every price path are the pointwise sums of the original
holdings and gains. -/
theorem exists_simpleHolding_simpleGains_add [OrderBot ι] {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) {n₁ n₂ : ℕ} {τ₁ τ₂ : ℕ → ι} {a₁ a₂ : ℕ → Ω → ℝ}
    (hτ₁ : MonotoneOn τ₁ (Set.Iic n₁)) (hτ₂ : MonotoneOn τ₂ (Set.Iic n₂))
    (ha₁ : ∀ i < n₁, StronglyMeasurable[ℱ (τ₁ i)] (a₁ i))
    (ha₂ : ∀ j < n₂, StronglyMeasurable[ℱ (τ₂ j)] (a₂ j)) :
    ∃ (n : ℕ) (τ : ℕ → ι) (b : ℕ → Ω → ℝ),
      τ 0 = ⊥ ∧ StrictMonoOn τ (Set.Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (b j)) ∧
      (∀ j < n, ∀ ω, ‖b j ω‖ ≤ (∑ i ∈ range n₁, ‖a₁ i ω‖) + ∑ i ∈ range n₂, ‖a₂ i ω‖) ∧
      (∀ t ω, simpleHolding τ n b t ω =
        simpleHolding τ₁ n₁ a₁ t ω + simpleHolding τ₂ n₂ a₂ t ω) ∧
      ∀ (X : ι → Ω → ℝ) t ω, simpleGains τ n b X t ω =
        simpleGains τ₁ n₁ a₁ X t ω + simpleGains τ₂ n₂ a₂ X t ω := by
  let l : Fin n₁ ⊕ Fin n₂ → ι := Sum.elim (fun i ↦ τ₁ i.1) (fun j ↦ τ₂ j.1)
  let u : Fin n₁ ⊕ Fin n₂ → ι := Sum.elim (fun i ↦ τ₁ (i.1 + 1)) (fun j ↦ τ₂ (j.1 + 1))
  let α : Fin n₁ ⊕ Fin n₂ → Ω → ℝ := Sum.elim (fun i ↦ a₁ i.1) (fun j ↦ a₂ j.1)
  have hαm (x : Fin n₁ ⊕ Fin n₂) (_ : x ∈ (univ : Finset _)) :
      StronglyMeasurable[ℱ (l x)] (α x) := by
    cases x with
    | inl i => exact ha₁ i.1 i.2
    | inr j => exact ha₂ j.1 j.2
  obtain ⟨n, τ, b, hτ₀, hτ, hbm, hbb, hhold, hgains⟩ :=
    exists_simpleHolding_simpleGains_eq_sum ℱ univ l u α hαm
  refine ⟨n, τ, b, hτ₀, hτ, hbm, fun j hj ω ↦ ?_, fun t ω ↦ ?_, fun X t ω ↦ ?_⟩
  · rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    simpa only [Fintype.sum_sum_type, α, Sum.elim_inl, Sum.elim_inr] using hbb j hj ω
  · rw [hhold t ω, Fintype.sum_sum_type, simpleHolding_def τ₁, simpleHolding_def τ₂,
      ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    rfl
  · rw [hgains X t ω, Fintype.sum_sum_type, simpleGains_def τ₁, simpleGains_def τ₂,
      ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    congr 1
    · refine sum_congr rfl fun i _ ↦ ?_
      simp [l, u, α, hτ₁ i.2.le i.2 (Nat.le_succ _)]
    · refine sum_congr rfl fun j _ ↦ ?_
      simp [l, u, α, hτ₂ j.2.le j.2 (Nat.le_succ _)]

/-- Two left-measurable simple strategies admit a single strictly increasing common grid starting
at `⊥` whose holdings and gains against every price path are the pointwise differences of the
original holdings and gains. -/
theorem exists_simpleHolding_simpleGains_sub [OrderBot ι] {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) {n₁ n₂ : ℕ} {τ₁ τ₂ : ℕ → ι} {a₁ a₂ : ℕ → Ω → ℝ}
    (hτ₁ : MonotoneOn τ₁ (Set.Iic n₁)) (hτ₂ : MonotoneOn τ₂ (Set.Iic n₂))
    (ha₁ : ∀ i < n₁, StronglyMeasurable[ℱ (τ₁ i)] (a₁ i))
    (ha₂ : ∀ j < n₂, StronglyMeasurable[ℱ (τ₂ j)] (a₂ j)) :
    ∃ (n : ℕ) (τ : ℕ → ι) (b : ℕ → Ω → ℝ),
      τ 0 = ⊥ ∧ StrictMonoOn τ (Set.Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (b j)) ∧
      (∀ j < n, ∀ ω, ‖b j ω‖ ≤ (∑ i ∈ range n₁, ‖a₁ i ω‖) + ∑ i ∈ range n₂, ‖a₂ i ω‖) ∧
      (∀ t ω, simpleHolding τ n b t ω =
        simpleHolding τ₁ n₁ a₁ t ω - simpleHolding τ₂ n₂ a₂ t ω) ∧
      ∀ (X : ι → Ω → ℝ) t ω, simpleGains τ n b X t ω =
        simpleGains τ₁ n₁ a₁ X t ω - simpleGains τ₂ n₂ a₂ X t ω := by
  obtain ⟨n, τ, b, hτ₀, hτ, hbm, hbb, hhold, hgains⟩ :=
    exists_simpleHolding_simpleGains_add ℱ hτ₁ hτ₂ ha₁
      (a₂ := (-1 : ℝ) • a₂) (fun j hj ↦ (ha₂ j hj).const_smul (-1 : ℝ))
  refine ⟨n, τ, b, hτ₀, hτ, hbm, fun j hj ω ↦ ?_, fun t ω ↦ ?_, fun X t ω ↦ ?_⟩
  · simpa [Pi.smul_apply] using hbb j hj ω
  · rw [hhold, simpleHolding_smul, neg_one_mul, ← sub_eq_add_neg]
  · rw [hgains, simpleGains_smul, neg_one_mul, ← sub_eq_add_neg]

end TauCeti.Finance
