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
`exists_simpleHolding_simpleGains_eq_sub` specializes this to the difference of two simple
strategies on monotone grids, subtracting both their holdings and their gains.

This bridges finite sums of predictable rectangles and finite-grid trading strategies. In
particular, `exists_simpleHolding_simpleGains_sub` clips two finite-grid strategies to `[⊥, t]` and
represents their difference on one common nondecreasing grid starting at `⊥` and bounded by `t`,
preserving height norm bounds before applying an isometry or energy estimate. All equalities are
pointwise, including at trading dates, with no regularity assumption on the price path.

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

/-- Clipping a finite-grid strategy's trading dates to `t` and zeroing out positions starting at or
after `t` leaves its holdings unchanged at every time `s ≤ t`. -/
theorem simpleHolding_min_ite_lt_of_le {g : ℕ → ι} {N : ℕ} {b : ℕ → Ω → ℝ} {s t : ι}
    (hs : s ≤ t) (ω : Ω) :
    simpleHolding (fun j ↦ min (g j) t) N (fun j ↦ if g j < t then b j else 0) s ω =
      simpleHolding g N b s ω := by
  rw [simpleHolding_def, simpleHolding_def]; refine sum_congr rfl fun j _ ↦ ?_
  by_cases h : g j < t
  · simp [h, min_eq_left h.le, Set.indicator_apply, Set.mem_Ioc, hs]
  · simp [h, Set.mem_Ioc, (hs.trans (not_lt.1 h)).not_gt]

/-- For a nondecreasing grid, summing the `min · t`-clipped increments against positions zeroed at
or after `t` recovers `simpleGains` at `t`. -/
theorem sum_ite_lt_mul_sub_min_eq_simpleGains {g : ℕ → ι} {N : ℕ} {b : ℕ → Ω → ℝ}
    (hg : MonotoneOn g (Set.Iic N)) (X : ι → Ω → ℝ) (t : ι) (ω : Ω) :
    (∑ j ∈ range N, (if g j < t then b j else 0) ω *
        (X (min (g (j + 1)) t) ω - X (min (g j) t) ω)) = simpleGains g N b X t ω := by
  rw [simpleGains_def]; refine sum_congr rfl fun j hj ↦ ?_
  by_cases h : g j < t
  · simp [h]
  · simp [h, min_eq_right (not_lt.1 h), min_eq_right ((not_lt.1 h).trans
      (hg (mem_range.1 hj).le (mem_range.1 hj) (Nat.le_succ j)))]

/-- Clip two left-measurable finite-grid strategies to `[⊥, t]` and represent their difference on a
single nondecreasing deterministic grid starting at `⊥` and bounded by `t`, with heights bounded
pointwise by the sum of the input absolute heights. -/
theorem exists_simpleHolding_simpleGains_sub [OrderBot ι] {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) (t : ι) {n₁ n₂ : ℕ} {τ₁ τ₂ : ℕ → ι} {a₁ a₂ : ℕ → Ω → ℝ}
    (hτ₁ : MonotoneOn τ₁ (Set.Iic n₁)) (ha₁ : ∀ j < n₁, StronglyMeasurable[ℱ (τ₁ j)] (a₁ j))
    (hτ₂ : MonotoneOn τ₂ (Set.Iic n₂)) (ha₂ : ∀ j < n₂, StronglyMeasurable[ℱ (τ₂ j)] (a₂ j)) :
    ∃ (N : ℕ) (grid : ℕ → ι) (height : ℕ → Ω → ℝ),
      grid 0 = ⊥ ∧ MonotoneOn grid (Set.Iic N) ∧ (∀ j ≤ N, grid j ≤ t) ∧
      (∀ j < N, StronglyMeasurable[ℱ (grid j)] (height j)) ∧
      (∀ j < N, ∀ ω, ‖height j ω‖ ≤ (∑ i ∈ range n₁, ‖a₁ i ω‖) + ∑ i ∈ range n₂, ‖a₂ i ω‖) ∧
      (∀ s ≤ t, ∀ ω, simpleHolding grid N height s ω =
        simpleHolding τ₁ n₁ a₁ s ω - simpleHolding τ₂ n₂ a₂ s ω) ∧
      ∀ (X : ι → Ω → ℝ) ω,
        (∑ j ∈ range N, height j ω * (X (grid (j + 1)) ω - X (grid j) ω)) =
          simpleGains τ₁ n₁ a₁ X t ω - simpleGains τ₂ n₂ a₂ X t ω := by
  let l : Fin n₁ ⊕ Fin n₂ → ι := Sum.elim (fun i ↦ min (τ₁ i) t) (fun i ↦ min (τ₂ i) t)
  let u : Fin n₁ ⊕ Fin n₂ → ι :=
    Sum.elim (fun i ↦ min (τ₁ (i + 1)) t) (fun i ↦ min (τ₂ (i + 1)) t)
  let c : Fin n₁ ⊕ Fin n₂ → Ω → ℝ := Sum.elim
    (fun i ↦ if τ₁ i < t then a₁ i else 0) (fun i ↦ if τ₂ i < t then (-a₂) i else 0)
  have hc : ∀ k ∈ (Finset.univ : Finset (Fin n₁ ⊕ Fin n₂)), StronglyMeasurable[ℱ (l k)] (c k) := by
    rintro (i | i) _ <;> dsimp only [c, Sum.elim_inl, Sum.elim_inr] <;> split_ifs with h
    · have hl : l (.inl i) = τ₁ i := min_eq_left h.le; exact hl ▸ ha₁ i i.isLt
    · exact stronglyMeasurable_zero
    · have hl : l (.inr i) = τ₂ i := min_eq_left h.le; exact hl ▸ (ha₂ i i.isLt).neg
    · exact stronglyMeasurable_zero
  obtain ⟨N, g, b, hg0, hg, hb, hb_norm, hhold, hgains⟩ :=
    exists_simpleHolding_simpleGains_eq_sum ℱ Finset.univ l u c hc
  let grid (j : ℕ) : ι := min (g j) t
  let height (j : ℕ) : Ω → ℝ := if g j < t then b j else 0
  have hlu : ∀ k : Fin n₁ ⊕ Fin n₂, l k ≤ u k
    | .inl i => min_le_min_right t (hτ₁ i.isLt.le i.isLt (Nat.le_succ i))
    | .inr i => min_le_min_right t (hτ₂ i.isLt.le i.isLt (Nat.le_succ i))
  have hut : ∀ k : Fin n₁ ⊕ Fin n₂, u k ≤ t := by rintro (i | i) <;> exact min_le_right _ _
  refine ⟨N, grid, height, by simp [grid, hg0],
    fun i hi j hj hij ↦ min_le_min_right t (hg.monotoneOn hi hj hij),
    fun _ _ ↦ min_le_right _ _, fun j hj ↦ ?_, fun j hj ω ↦ ?_, fun s hs ω ↦ ?_, fun X ω ↦ ?_⟩
  · dsimp only [height]; split_ifs with h
    · have hg_eq : grid j = g j := min_eq_left h.le; exact hg_eq ▸ hb j hj
    · exact stronglyMeasurable_zero
  · have hsum_c : (∑ k : Fin n₁ ⊕ Fin n₂, ‖c k ω‖) ≤
        (∑ i ∈ range n₁, ‖a₁ i ω‖) + ∑ i ∈ range n₂, ‖a₂ i ω‖ := by
      rw [Fintype.sum_sum_type, ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
      exact add_le_add (sum_le_sum fun _ _ ↦ by dsimp [c]; split_ifs <;> simp)
        (sum_le_sum fun _ _ ↦ by dsimp [c]; split_ifs <;> simp)
    dsimp only [height]; split_ifs
    · exact (hb_norm j hj ω).trans hsum_c
    · simp only [Pi.zero_apply, norm_zero]
      exact add_nonneg (sum_nonneg fun _ _ ↦ norm_nonneg _) (sum_nonneg fun _ _ ↦ norm_nonneg _)
  · rw [simpleHolding_min_ite_lt_of_le hs ω, hhold, Fintype.sum_sum_type]
    dsimp only [l, u, c, Sum.elim_inl, Sum.elim_inr]
    have h₁ := simpleHolding_min_ite_lt_of_le (g := τ₁) (N := n₁) (b := a₁) hs ω
    have h₂ := simpleHolding_min_ite_lt_of_le (g := τ₂) (N := n₂) (b := -a₂) hs ω
    rw [simpleHolding_def, ← Fin.sum_univ_eq_sum_range] at h₁ h₂
    rw [h₁, h₂, simpleHolding_neg, sub_eq_add_neg]
  · rw [sum_ite_lt_mul_sub_min_eq_simpleGains hg.monotoneOn X t ω, hgains, Fintype.sum_sum_type]
    simp only [hlu, ↓reduceIte, min_eq_left (hut _), min_eq_left ((hlu _).trans (hut _))]
    dsimp only [l, u, c, Sum.elim_inl, Sum.elim_inr]
    rw [sub_eq_add_neg, ← simpleGains_neg, ← sum_ite_lt_mul_sub_min_eq_simpleGains hτ₁ X t ω,
      ← sum_ite_lt_mul_sub_min_eq_simpleGains (b := -a₂) hτ₂ X t ω,
      ← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]

/-- The difference of two simple strategies is one simple strategy on a strictly increasing
common grid starting at the bottom time, with heights still chosen at the left endpoints of
their intervals. Holdings and gains against every price path are subtracted. -/
theorem exists_simpleHolding_simpleGains_eq_sub [OrderBot ι] {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) {τ σ : ℕ → ι} {n m : ℕ} {a b : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hσ : MonotoneOn σ (Set.Iic m))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < m, StronglyMeasurable[ℱ (σ j)] (b j)) :
    ∃ (N : ℕ) (ρ : ℕ → ι) (c : ℕ → Ω → ℝ),
      ρ 0 = ⊥ ∧ StrictMonoOn ρ (Set.Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (ρ j)] (c j)) ∧
      (∀ t ω, simpleHolding ρ N c t ω = simpleHolding τ n a t ω - simpleHolding σ m b t ω) ∧
      ∀ (X : ι → Ω → ℝ) t ω, simpleGains ρ N c X t ω =
        simpleGains τ n a X t ω - simpleGains σ m b X t ω := by
  obtain ⟨N, ρ, c, hρ₀, hρ, hc, -, hhold, hgain⟩ := exists_simpleHolding_simpleGains_eq_sum ℱ
    ((range n).disjSum (range m)) (Sum.elim τ σ) (Sum.elim (fun j ↦ τ (j + 1)) fun j ↦ σ (j + 1))
    (Sum.elim a fun j ω ↦ -b j ω) (by
      rintro (j | j) hj <;> simp only [inl_mem_disjSum, inr_mem_disjSum, mem_range] at hj
      · exact ha j hj
      · exact (hb j hj).neg)
  refine ⟨N, ρ, c, hρ₀, hρ, hc, fun t ω ↦ ?_, fun X t ω ↦ ?_⟩
  · rw [hhold, sum_disjSum, simpleHolding_def, simpleHolding_def, sub_eq_add_neg,
      ← sum_neg_distrib]
    simp only [Sum.elim_inl, Sum.elim_inr]
    congr 1
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases ht : t ∈ Set.Ioc (σ j) (σ (j + 1)) <;> simp [ht]
  · rw [hgain, sum_disjSum, simpleGains_def, simpleGains_def, sub_eq_add_neg, ← sum_neg_distrib]
    simp only [Sum.elim_inl, Sum.elim_inr]
    congr 1 <;> refine sum_congr rfl fun j hj ↦ ?_
    · simp [hτ (mem_range.mp hj).le (mem_range.mp hj) (Nat.le_succ j)]
    · simp [hσ (mem_range.mp hj).le (mem_range.mp hj) (Nat.le_succ j)]

end TauCeti.Finance
