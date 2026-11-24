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
bottom time, increases strictly on its finite prefix, and uses only the bottom time and input
endpoints. Empty and reversed input intervals are allowed. The new heights are bounded pointwise
by the sum of the original absolute heights; thus boundedness and Lᵖ control survive refinement
without additional moment assumptions.
`exists_simpleHolding_simpleGains_eq_sub` specializes this to the difference of two simple
strategies on monotone grids, subtracting both their holdings and their gains.

A finite family of elementary predictable holdings can also be refined simultaneously while
preserving each holding and its gains separately, not just their sum. Tagging each strategy with
its own sample-space coordinate reduces this to scalar refinement. Evaluating each refined
holding at the new right endpoints preserves its individual almost-sure uniform bound. This lets
one compare bounded elementary stochastic-integral approximations on a common grid.

This bridges finite sums of predictable rectangles and finite-grid trading strategies. In
particular, differences of elementary stochastic-integral approximants can be evaluated on one
common grid before applying an isometry or energy estimate. All equalities are pointwise,
including at trading dates, with no regularity assumption on the price path.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, 2nd ed., Springer, 2005,
  §II.2.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §§3.2 and 3.5.
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
The grid starts at the bottom time and is nondecreasing globally, using only the bottom time
and input endpoints. Heights are measurable at their left endpoints and zero beyond the active
cells. Empty or reversed intervals contribute no holdings or gains; for a reversed interval the
displayed increment must therefore be suppressed. -/
theorem exists_simpleHolding_simpleGains_eq_sum [OrderBot ι] {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) (s : Finset κ) (l u : κ → ι) (a : κ → Ω → ℝ)
    (ha : ∀ i ∈ s, StronglyMeasurable[ℱ (l i)] (a i)) :
    ∃ (n : ℕ) (τ : ℕ → ι) (b : ℕ → Ω → ℝ),
      τ 0 = ⊥ ∧ StrictMonoOn τ (Set.Iic n) ∧ Monotone τ ∧
      (∀ j, τ j ∈ insert ⊥ (s.image l ∪ s.image u)) ∧
      (∀ j, StronglyMeasurable[ℱ (τ j)] (b j)) ∧
      (∀ j, n ≤ j → b j = 0) ∧
      (∀ j < n, ∀ ω, ‖b j ω‖ ≤ ∑ i ∈ s, ‖a i ω‖) ∧
      (∀ t ω, simpleHolding τ n b t ω =
        ∑ i ∈ s, (Set.Ioc (l i) (u i)).indicator (fun _ ↦ a i ω) t) ∧
      ∀ (X : ι → Ω → ℝ) t ω, simpleGains τ n b X t ω =
        ∑ i ∈ s, if l i ≤ u i then
          a i ω * (X (min (u i) t) ω - X (min (l i) t) ω) else 0 := by
  classical
  -- Sort the distinct endpoints, including the initial time.
  let d := insert ⊥ (s.image l ∪ s.image u)
  obtain ⟨τ, hmono, hτ, hmem, himage, -⟩ :=
    d.exists_strictMonoOn_Iic_surj ⟨⊥, mem_insert_self _ _⟩
  let n := d.card - 1
  have hsurj (x : ι) (hx : x ∈ d) : ∃ j ≤ n, τ j = x :=
    (Set.mem_image τ (Set.Iic n) x).mp (himage.symm ▸ hx)
  have hzero : τ 0 = ⊥ := by
    obtain ⟨j, -, heq⟩ := hsurj ⊥ (mem_insert_self _ _)
    exact le_bot_iff.mp (heq ▸ hmono (Nat.zero_le j))
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
  refine ⟨n, τ, b, hzero, hτ, hmono, hmem, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    refine Finset.stronglyMeasurable_fun_sum _ fun i hi ↦ ?_
    by_cases hij : L i ≤ j ∧ j < U i
    · have hle : l i ≤ τ j := (hL i hi).2 ▸ hmono hij.1
      simpa [hij] using (ha i hi).mono (ℱ.mono hle)
    · simpa only [ite_eq_right hij] using stronglyMeasurable_const (b := (0 : ℝ))
  · intro j hj
    funext ω
    exact sum_eq_zero fun i hi ↦ ite_eq_right (not_lt_of_ge ((hU i hi).1.trans hj) ∘ And.right)
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
  obtain ⟨N, ρ, c, hρ₀, hρ, -, -, hc, -, -, hhold, hgain⟩ :=
    exists_simpleHolding_simpleGains_eq_sum ℱ ((range n).disjSum (range m)) (Sum.elim τ σ)
      (Sum.elim (fun j ↦ τ (j + 1)) fun j ↦ σ (j + 1)) (Sum.elim a fun j ω ↦ -b j ω) (by
        rintro (j | j) hj <;> simp only [inl_mem_disjSum, inr_mem_disjSum, mem_range] at hj
        · exact ha j hj
        · exact (hb j hj).neg)
  refine ⟨N, ρ, c, hρ₀, hρ, fun j _ ↦ hc j, fun t ω ↦ ?_, fun X t ω ↦ ?_⟩
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

/-- The sum of two simple strategies is one simple strategy on a strictly increasing common grid
starting at the bottom time, with heights still chosen at the left endpoints of their intervals.
Holdings and gains against every price path are added. -/
theorem exists_simpleHolding_simpleGains_eq_add [OrderBot ι] {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) {τ σ : ℕ → ι} {n m : ℕ} {a b : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (hσ : MonotoneOn σ (Set.Iic m))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < m, StronglyMeasurable[ℱ (σ j)] (b j)) :
    ∃ (N : ℕ) (ρ : ℕ → ι) (c : ℕ → Ω → ℝ),
      ρ 0 = ⊥ ∧ StrictMonoOn ρ (Set.Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (ρ j)] (c j)) ∧
      (∀ t ω, simpleHolding ρ N c t ω = simpleHolding τ n a t ω + simpleHolding σ m b t ω) ∧
      ∀ (X : ι → Ω → ℝ) t ω, simpleGains ρ N c X t ω =
        simpleGains τ n a X t ω + simpleGains σ m b X t ω := by
  obtain ⟨N, ρ, c, hρ₀, hρ, hc, hhold, hgain⟩ := exists_simpleHolding_simpleGains_eq_sub ℱ hτ hσ
    ha (b := -b) fun j hj ↦ (hb j hj).neg
  refine ⟨N, ρ, c, hρ₀, hρ, hc, fun t ω ↦ ?_, fun X t ω ↦ ?_⟩
  · have hbneg : simpleHolding σ m (-b) t ω = -simpleHolding σ m b t ω := by
      simpa only [neg_smul, one_smul, neg_one_mul] using simpleHolding_smul σ m (-1) b t ω
    rw [hhold, hbneg, sub_neg_eq_add]
  · have hbneg : simpleGains σ m (-b) X t ω = -simpleGains σ m b X t ω := by
      simpa only [neg_smul, one_smul, neg_one_mul] using simpleGains_smul σ m (-1) b X t ω
    rw [hgain, hbneg, sub_neg_eq_add]

end TauCeti.Finance

namespace MeasureTheory.Filtration

open TauCeti.Finance

variable {Ω ι κ : Type*} [LinearOrder ι] [OrderBot ι] [Finite κ]

/-- Several elementary predictable holdings can be put on one strictly increasing grid,
with their individual gains unchanged against every price path.
The grid is nondecreasing globally, uses only the bottom time and active input dates, and has
left-endpoint measurable heights that vanish beyond the active cells. Empty grids, repeated
original dates and nonzero original initial dates are allowed. -/
theorem exists_strictMonoOn_forall_simpleHolding_simpleGains_eq {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) (n : κ → ℕ) (τ : κ → ℕ → ι) (a : κ → ℕ → Ω → ℝ)
    (hτ : ∀ k, MonotoneOn (τ k) (Set.Iic (n k)))
    (ha : ∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) :
    ∃ (N : ℕ) (σ : ℕ → ι) (b : κ → ℕ → Ω → ℝ),
      σ 0 = ⊥ ∧ StrictMonoOn σ (Set.Iic N) ∧ Monotone σ ∧
      (∀ j, σ j = ⊥ ∨ ∃ k, 0 < n k ∧ ∃ i ≤ n k, σ j = τ k i) ∧
      (∀ k j, StronglyMeasurable[ℱ (σ j)] (b k j)) ∧
      (∀ k j, N ≤ j → b k j = 0) ∧
      (∀ k t ω, simpleHolding σ N (b k) t ω = simpleHolding (τ k) (n k) (a k) t ω) ∧
      ∀ k (X : ι → Ω → ℝ) t ω,
        simpleGains σ N (b k) X t ω = simpleGains (τ k) (n k) (a k) X t ω := by
  classical
  let := Fintype.ofFinite κ
  let : MeasurableSpace κ := ⊤
  let 𝒢 : Filtration ι (inferInstance : MeasurableSpace (κ × Ω)) :=
    ⟨fun t ↦ (⊤ : MeasurableSpace κ).prod (ℱ t),
      fun _ _ h ↦ MeasurableSpace.prod_mono le_rfl (ℱ.mono h),
      fun t ↦ MeasurableSpace.prod_mono le_rfl (ℱ.le t)⟩
  let s : Finset (Σ _ : κ, ℕ) := univ.sigma fun k ↦ range (n k)
  let c (i : Σ _ : κ, ℕ) (p : κ × Ω) := if p.1 = i.1 then a i.1 i.2 p.2 else 0
  obtain ⟨N, σ, b, hzero, hσ, hmono, hdate, hb, htail, -, hhold, hgain⟩ :=
    exists_simpleHolding_simpleGains_eq_sum 𝒢 s
      (fun i ↦ τ i.1 i.2) (fun i ↦ τ i.1 (i.2 + 1)) c (by
        intro i hi
        exact ((ha i.1 i.2 (by simpa [s] using hi)).comp_measurable measurable_snd).ite
          ((MeasurableSet.of_discrete : MeasurableSet {k : κ | k = i.1}).preimage measurable_fst)
          stronglyMeasurable_const)
  refine ⟨N, σ, fun k j ω ↦ b j (k, ω), hzero, hσ, hmono, ?_,
    fun k j ↦ (hb j).comp_measurable (measurable_const.prodMk measurable_id),
    fun k j hj ↦ funext fun ω ↦ congrFun (htail j hj) (k, ω), ?_, ?_⟩
  · simp only [mem_insert, mem_union, mem_image, s, mem_sigma, mem_univ, true_and,
      mem_range] at hdate
    intro j
    rcases hdate j with h | ⟨i, hi, h⟩ | ⟨i, hi, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨i.1, (Nat.zero_le _).trans_lt hi, i.2, hi.le, h.symm⟩
    · exact Or.inr ⟨i.1, (Nat.zero_le _).trans_lt hi, i.2 + 1, hi, h.symm⟩
  · intro k t ω
    calc
      _ = ∑ i ∈ s, (Set.Ioc (τ i.1 i.2) (τ i.1 (i.2 + 1))).indicator
          (fun _ ↦ c i (k, ω)) t := by
        simpa only [simpleHolding_def] using hhold t (k, ω)
      _ = _ := by
        simp only [s, sum_sigma]
        rw [sum_eq_single_of_mem k (mem_univ _)]
        · simp [c, simpleHolding_def]
        · exact fun l _ hl ↦ sum_eq_zero fun j _ ↦ by simp [c, Ne.symm hl]
  · intro k X t ω
    calc
      _ = ∑ i ∈ s, if τ i.1 i.2 ≤ τ i.1 (i.2 + 1) then
          c i (k, ω) * (X (min (τ i.1 (i.2 + 1)) t) ω - X (min (τ i.1 i.2) t) ω)
          else 0 := by
        simpa only [simpleGains_def] using hgain (fun t p ↦ X t p.2) t (k, ω)
      _ = _ := by
        simp only [s, sum_sigma]
        rw [sum_eq_single_of_mem k (mem_univ _), simpleGains_def]
        · refine sum_congr rfl fun j hj ↦ ?_
          simp [c, hτ k (mem_range.mp hj).le (mem_range.mp hj) (Nat.le_succ j)]
        · exact fun l _ hl ↦ sum_eq_zero fun j _ ↦ by simp [c, Ne.symm hl]

/-- Simultaneous refinement preserves separate almost-sure uniform bounds, including bounds
that depend on the strategy and the sample. The bound holds for every new height, including
zero heights beyond the active cells; no hypothesis is made on unused original heights. -/
theorem exists_strictMonoOn_forall_ae_abs_le_simpleHolding_simpleGains_eq_of_bound
    {mΩ : MeasurableSpace Ω} (ℱ : Filtration ι mΩ) (P : Measure Ω) (n : κ → ℕ)
    (τ : κ → ℕ → ι) (a : κ → ℕ → Ω → ℝ) (K : κ → Ω → ℝ)
    (hτ : ∀ k, MonotoneOn (τ k) (Set.Iic (n k)))
    (ha : ∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j))
    (hK : ∀ k, ∀ᵐ ω ∂P, ∀ t, |simpleHolding (τ k) (n k) (a k) t ω| ≤ K k ω) :
    ∃ (N : ℕ) (σ : ℕ → ι) (b : κ → ℕ → Ω → ℝ),
      σ 0 = ⊥ ∧ StrictMonoOn σ (Set.Iic N) ∧ Monotone σ ∧
      (∀ j, σ j = ⊥ ∨ ∃ k, 0 < n k ∧ ∃ i ≤ n k, σ j = τ k i) ∧
      (∀ k j, StronglyMeasurable[ℱ (σ j)] (b k j)) ∧
      (∀ k j, N ≤ j → b k j = 0) ∧
      (∀ k, ∀ᵐ ω ∂P, ∀ j, |b k j ω| ≤ K k ω) ∧
      (∀ k t ω, simpleHolding σ N (b k) t ω = simpleHolding (τ k) (n k) (a k) t ω) ∧
      ∀ k (X : ι → Ω → ℝ) t ω,
        simpleGains σ N (b k) X t ω = simpleGains (τ k) (n k) (a k) X t ω := by
  obtain ⟨N, σ, b, hzero, hσ, hmono, hdate, hb, htail, hhold, hgain⟩ :=
    ℱ.exists_strictMonoOn_forall_simpleHolding_simpleGains_eq n τ a hτ ha
  refine ⟨N, σ, b, hzero, hσ, hmono, hdate, hb, htail, ?_, hhold, hgain⟩
  intro k
  filter_upwards [hK k] with ω hω j
  by_cases hj : j < N
  · have heq := hhold k (σ (j + 1)) ω
    rw [simpleHolding_of_mem_Ioc hσ.monotoneOn hj
      ⟨hσ hj.le hj (Nat.lt_succ_self j), le_rfl⟩] at heq
    exact heq.symm ▸ hω (σ (j + 1))
  · rw [htail k j (Nat.le_of_not_lt hj), Pi.zero_apply, abs_zero]
    exact (abs_nonneg _).trans (hω ⊥)

end MeasureTheory.Filtration
