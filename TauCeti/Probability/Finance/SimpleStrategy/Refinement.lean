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
`simpleHolding_clip_Ioc_mul` clips a simple strategy to `(s, t]` via `Set.projIcc s t hst ∘ τ`
and multiplies by an `ℱ s`-measurable height `ξ`, factoring `ξ` out of the `(s, t]` gain
difference.

This bridges finite sums of predictable rectangles and finite-grid trading strategies. In
particular, differences of elementary stochastic-integral approximants can be evaluated on one
common grid before applying an isometry or energy estimate. All equalities are pointwise,
including at trading dates, with no regularity assumption on the price path.

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

private theorem Ioc_projIcc_eq_Ioc_inter {s t l r : ι} (hst : s ≤ t) (hlt : l ≤ t) :
    Set.Ioc (Set.projIcc s t hst l : ι) (Set.projIcc s t hst r : ι) =
      Set.Ioc s t ∩ Set.Ioc l r := by
  ext u
  simp only [Set.mem_Ioc, Set.mem_inter_iff, Set.coe_projIcc, min_eq_right hlt, max_lt_iff,
    le_max_iff, le_min_iff]
  constructor
  · rintro ⟨⟨hsu, hlu⟩, h1 | ⟨hut, hur⟩⟩
    · exact absurd h1 hsu.not_ge
    · exact ⟨⟨hsu, hut⟩, ⟨hlu, hur⟩⟩
  · rintro ⟨⟨hsu, hut⟩, ⟨hlu, hur⟩⟩
    exact ⟨⟨hsu, hlu⟩, Or.inr ⟨hut, hur⟩⟩

private theorem indicator_Ioc_projIcc_mul {s t l r : ι} (hst : s ≤ t) (hlr : l ≤ r)
    (ξ c : ℝ) (u : ι) :
    (Set.Ioc (Set.projIcc s t hst l : ι) (Set.projIcc s t hst r : ι)).indicator
        (fun _ ↦ if l ≤ t then ξ * c else 0) u =
      (Set.Ioc s t).indicator (fun _ ↦ ξ * (Set.Ioc l r).indicator (fun _ ↦ c) u) u := by
  by_cases hlt : l ≤ t
  · rw [Ioc_projIcc_eq_Ioc_inter hst hlt]
    by_cases hus : u ∈ Set.Ioc s t <;> by_cases hul : u ∈ Set.Ioc l r <;>
      simp [hlt, hus, hul]
  · have htl : t < l := lt_of_not_ge hlt
    have htr : t < r := htl.trans_le hlr
    have hpl : Set.projIcc s t hst l = ⟨t, Set.right_mem_Icc.2 hst⟩ :=
      Set.projIcc_of_right_le hst htl.le
    have hpr : Set.projIcc s t hst r = ⟨t, Set.right_mem_Icc.2 hst⟩ :=
      Set.projIcc_of_right_le hst htr.le
    simp only [hlt, ite_false, hpl, hpr, Set.Ioc_self, Set.indicator_apply, Set.mem_Ioc]
    by_cases hus : s < u ∧ u ≤ t
    · have hul : ¬ l < u := not_lt_of_ge (hus.2.trans htl.le)
      simp [hus, hul]
    · simp [hus]

private theorem min_coe_projIcc_eq {s t T : ι} (hst : s ≤ t) (hsT : s ≤ T) (r : ι) :
    min (Set.projIcc s t hst r : ι) T = max s (min r (min T t)) := by
  rw [Set.coe_projIcc, min_max_distrib_right, min_eq_left hsT]
  ac_rfl

private theorem single_clip_Ioc_gain {s t l r T : ι} (hst : s ≤ t) (hlr : l ≤ r)
    (ξ c : ℝ) (f : ι → ℝ) :
    (if l ≤ t then ξ * c else 0) *
        (f (min (Set.projIcc s t hst r : ι) T) - f (min (Set.projIcc s t hst l : ι) T)) =
      ξ * (c * (f (min r (min T t)) - f (min l (min T t))) -
        c * (f (min r (min T s)) - f (min l (min T s)))) := by
  rcases le_total T s with hTs | hsT
  · have hpl : T ≤ (Set.projIcc s t hst l : ι) := hTs.trans (Set.projIcc s t hst l).property.1
    have hpr : T ≤ (Set.projIcc s t hst r : ι) := hTs.trans (Set.projIcc s t hst r).property.1
    rw [min_eq_right hpl, min_eq_right hpr, min_eq_left (hTs.trans hst), min_eq_left hTs,
      sub_self, mul_zero, sub_self, mul_zero]
  · by_cases hlt : l ≤ t
    · simp only [hlt, ite_true, min_coe_projIcc_eq hst hsT, min_eq_right hsT]
      rw [show ξ * (c * (f (min r (min T t)) - f (min l (min T t))) -
            c * (f (min r s) - f (min l s))) =
          (ξ * c) * ((f (min r (min T t)) - f (min l (min T t))) -
            (f (min r s) - f (min l s))) by ring]
      congr 1
      have hsu : s ≤ min T t := le_min hsT hst
      rcases le_total l s with hls | hsl <;> rcases le_total r s with hrs | hsr
      · simp [hls, hrs, hls.trans hsu, hrs.trans hsu]
      · rw [max_eq_right (le_min hsr hsu), max_eq_left (min_le_of_left_le hls),
          min_eq_left (hls.trans hsu), min_eq_right hsr, min_eq_left hls]
        ring
      · have hls_eq : l = s := (hlr.trans hrs).antisymm hsl
        have hrs_eq : r = s := hrs.antisymm (hsl.trans hlr)
        simp [hls_eq, hrs_eq, hsu]
      · rw [max_eq_right (le_min hsl hsu), max_eq_right (le_min hsr hsu),
          min_eq_right hsl, min_eq_right hsr]
        ring
    · have htl : t < l := lt_of_not_ge hlt
      have htr : t < r := htl.trans_le hlr
      simp only [hlt, ite_false, zero_mul]
      have h1 : min T t ≤ l := (min_le_right T t).trans htl.le
      have h2 : min T t ≤ r := (min_le_right T t).trans htr.le
      have h3 : min T s ≤ l := (min_le_right T s).trans (hst.trans htl.le)
      have h4 : min T s ≤ r := (min_le_right T s).trans (hst.trans htr.le)
      rw [min_eq_right h1, min_eq_right h2, min_eq_right h3, min_eq_right h4,
        sub_self, mul_zero, sub_self, mul_zero, sub_self, mul_zero]

/-- Clipping a simple holding `(τ, n, a)` to `(s, t]` via `Set.projIcc s t hst ∘ τ` and
multiplying by an `ℱ s`-measurable function `ξ` yields another simple holding whose holdings
equal `1_{(s, t]} · ξ · simpleHolding τ n a` and whose gains factor `ξ` out of the `(s, t]`
difference of gains. -/
theorem simpleHolding_clip_Ioc_mul {mΩ : MeasurableSpace Ω} (ℱ : Filtration ι mΩ)
    {τ : ℕ → ι} {n : ℕ} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    {s t : ι} (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ) :
    let σ : ℕ → ι := fun j ↦ Set.projIcc s t hst (τ j)
    let b (j : ℕ) (ω : Ω) : ℝ := if τ j ≤ t then ξ ω * a j ω else 0
    MonotoneOn σ (Set.Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (σ j)] (b j)) ∧
      (∀ u ω, simpleHolding σ n b u ω =
        (Set.Ioc s t).indicator (fun _ ↦ ξ ω * simpleHolding τ n a u ω) u) ∧
      ∀ (X : ι → Ω → ℝ) (T : ι) (ω : Ω), simpleGains σ n b X T ω =
        ξ ω * (simpleGains τ n a X (min T t) ω - simpleGains τ n a X (min T s) ω) := by
  intro σ b
  have hσ : MonotoneOn σ (Set.Iic n) := fun i hi j hj hij ↦
    Set.monotone_projIcc hst (hτ hi hj hij)
  refine ⟨hσ, fun j hj ↦ ?_, fun u ω ↦ ?_, fun X T ω ↦ ?_⟩
  · dsimp only [b]
    by_cases hjt : τ j ≤ t
    · simp only [hjt, ite_true]
      have hsσ : s ≤ σ j := (Set.projIcc s t hst (τ j)).property.1
      have hτσ : τ j ≤ σ j := by
        rw [show σ j = max s (min t (τ j)) from Set.coe_projIcc s t hst (τ j)]
        exact le_max_of_le_right (le_min hjt le_rfl)
      exact (hξ.mono (ℱ.mono hsσ)).mul ((ha j hj).mono (ℱ.mono hτσ))
    · simp only [hjt, ite_false]
      exact stronglyMeasurable_zero
  · rw [simpleHolding_def, simpleHolding_def, sum_congr rfl fun j hj ↦
      indicator_Ioc_projIcc_mul hst (hτ (mem_range.mp hj).le (mem_range.mp hj) (Nat.le_succ j))
        (ξ ω) (a j ω) u]
    by_cases hu : u ∈ Set.Ioc s t
    · simp only [Set.indicator_of_mem hu, mul_sum]
    · simp [Set.indicator_of_notMem hu]
  · rw [simpleGains_def, simpleGains_def, simpleGains_def, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' : j < n := mem_range.mp hj
    exact single_clip_Ioc_gain hst (hτ hj'.le hj' (Nat.le_succ j)) (ξ ω) (a j ω) (X · ω)

end TauCeti.Finance
