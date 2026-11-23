/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.DeGiorgi
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.BoundedVariation.Submodularity

/-!
# Finite perimeter from a frontier of finite Hausdorff measure

Let `μ` be an additive Haar measure on a finite-dimensional real inner product space `E` of
dimension `n`. This file proves that a set whose topological frontier has locally finite
`(n - 1)`-dimensional Hausdorff measure has locally finite perimeter, with no measurability or
regularity assumption on the set:

* `TauCeti.perimeter_le_mul_hausdorffMeasure_frontier_inter`: for every set `s` and open set `Ω`,
  `P(s; Ω) ≤ n μ(B(0, 1)) μH[n - 1](∂s ∩ Ω)`;
* `TauCeti.exists_perimeter_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top`: if
  `Hⁿ⁻¹(∂s ∩ K) < ∞` for every compact `K ⊆ Ω`, then every compact subset of `Ω` has an open
  neighborhood in which `s` has finite perimeter;
* `TauCeti.perimeter_le_euclideanHausdorffMeasure_frontier_inter`: in dimension `n ≥ 2`, the sharp
  bound `P(s; Ω) ≤ Hⁿ⁻¹(∂s ∩ Ω)` for every set `s`, combining the criterion with De Giorgi's
  representation `P(s; Ω) = Hⁿ⁻¹(∂*s)` of the perimeter of a set of locally finite perimeter.

The proof uses two further results. `TauCeti.perimeter_diff_le_of_frontier_inter_subset`: if an
open set `G` contains `∂s ∩ V`, then `P(s \ G; V) ≤ P(G; V)`. And
`TauCeti.exists_finset_ball_cover_sum_rpow_lt_of_isCompact`, in any metric space: a compact set
`A` is covered by finitely many arbitrarily small open balls `B(xᵢ, ρᵢ)` with `∑ ρᵢ ^ d` arbitrarily
close to `μH[d] A`.

## Strategy

When `Hⁿ⁻¹(∂s ∩ Ω)` is finite, the frontier is Lebesgue null in `Ω`, so `s` may be replaced by its
interior. Fix an open set `V` with compact closure in `Ω`. Cover the compact set `∂s ∩ closure V`
by finitely many open balls `B(xᵢ, ρᵢ)` of radii at most `δ` with `∑ ρᵢ ^ (n - 1)` close to
`μH[n - 1](∂s ∩ closure V)`, and let `G` be their union. The set `s \ G` is empty on `G` and on the
exterior of `s`, and agrees with `Gᶜ` on the interior of `s`; these three open sets cover `V`.
Hence `P(s \ G; V) ≤ P(G) ≤ ∑ n μ(B(0, 1)) ρᵢ ^ (n - 1)`. As `δ → 0` the volume of `G` tends to
zero, so `s \ G → s` in measure, and lower semicontinuity of the perimeter bounds `P(s; V)`.

## Main gap

The criterion stated with the essential boundary in place of the topological frontier, which
Federer proves by slicing, is not proved here.

## References

* H. Federer, *Geometric Measure Theory*, 4.5.11.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.11 (criterion for finite perimeter).
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Proposition 3.62.
-/

public section

namespace TauCeti

open MeasureTheory Measure TopologicalSpace Set Filter Metric Module
open scoped ENNReal NNReal Topology symmDiff

section Cover

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A radius `ρ ∈ (D, δ]` whose `d`-th power exceeds `D ^ d` by less than a given `η > 0`, for
`D ≤ δ / 2`. -/
private lemma exists_ofReal_rpow_le_add {D : ℝ≥0∞} {δ : ℝ} (hδ : 0 < δ)
    (hD : D ≤ ENNReal.ofReal (δ / 2)) (d : ℝ) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ ρ : ℝ, D < ENNReal.ofReal ρ ∧ ρ ≤ δ ∧ ENNReal.ofReal ρ ^ d ≤ D ^ d + η := by
  have hDtop : D ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD
  have hDδ : D.toReal ≤ δ / 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hD
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  by_cases hDd : D ^ d = ∞
  · refine ⟨3 * δ / 4, ?_, by linarith, by simp [hDd]⟩
    rw [← ENNReal.ofReal_toReal hDtop]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  -- Near `D` from the right, `ofReal ρ ^ d` is close to `D ^ d`.
  have hcont : Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ ^ d) (𝓝[>] D.toReal) (𝓝 (D ^ d)) := by
    have := ((ENNReal.continuous_rpow_const (y := d)).comp ENNReal.continuous_ofReal).tendsto
      D.toReal
    simpa [Function.comp_def, ENNReal.ofReal_toReal hDtop] using this.mono_left nhdsWithin_le_nhds
  have hIoo : ∀ᶠ ρ in 𝓝[>] D.toReal, ρ ∈ Ioo D.toReal δ :=
    Ioo_mem_nhdsGT (show D.toReal < δ by linarith)
  obtain ⟨ρ, h1, h2⟩ :=
    ((hcont.eventually (gt_mem_nhds (ENNReal.lt_add_right hDd hη))).and hIoo).exists
  refine ⟨ρ, ?_, h2.2.le, h1.le⟩
  rw [← ENNReal.ofReal_toReal hDtop]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [h2.1, ENNReal.toReal_nonneg (a := D)])).2 h2.1

/-- **Finite covers by small balls with almost minimal `d`-dimensional sum.** A compact set `A`
with `μH[d] A < c` is covered, for every `δ > 0`, by finitely many open balls `ball x ρ`, indexed
by a finite set `T` of pairs `(x, ρ)`, with `0 < ρ ≤ δ` and `∑ ρ ^ d < c`. A set of diameter `D`
containing `y` lies in every ball about `y` of radius larger than `D`, so no covering constant is
lost. -/
theorem exists_finset_ball_cover_sum_rpow_lt_of_isCompact {A : Set X} (hA : IsCompact A)
    {d : ℝ} {c : ℝ≥0∞} (hAc : μH[d] A < c) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : Finset (X × ℝ), (∀ p ∈ T, 0 < p.2 ∧ p.2 ≤ δ) ∧
      A ⊆ ⋃ p ∈ T, ball p.1 p.2 ∧ ∑ p ∈ T, ENNReal.ofReal p.2 ^ d < c := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨∅, by simp, by simp [eq_empty_of_isEmpty A], by simpa using zero_le.trans_lt hAc⟩
  -- A countable cover by sets `t n` of diameter at most `δ / 2` with `∑ diam (t n) ^ d < c`.
  have hr : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.2 (half_pos hδ)
  rw [hausdorffMeasure_apply] at hAc
  have h1 := (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) => ⨅ (t : ℕ → Set X)
    (_ : A ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ r), ∑' n, ⨆ _ : (t n).Nonempty,
      ediam (t n) ^ d) _ hr).trans_lt hAc
  simp only [iInf_lt_iff] at h1
  obtain ⟨t, htA, htδ, htc⟩ := h1
  set S := ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d
  obtain ⟨ε, hε0, hεc⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 htc
  obtain ⟨ε', hε'0, hε'⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.coe_ne_zero.2 hε0.ne') ℕ
  -- Enlarge each nonempty `t n` to a ball about one of its points.
  have hball (n : ℕ) (hn : (t n).Nonempty) : ∃ y : X, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δ ∧
      t n ⊆ ball y ρ ∧ ENNReal.ofReal ρ ^ d ≤ ediam (t n) ^ d + ε' n := by
    obtain ⟨y, hy⟩ := hn
    obtain ⟨ρ, hρD, hρδ, hρd⟩ := exists_ofReal_rpow_le_add hδ (htδ n) d
      (ENNReal.coe_ne_zero.2 (hε'0 n).ne')
    refine ⟨y, ρ, ENNReal.ofReal_pos.1 (zero_le.trans_lt hρD), hρδ, fun z hz => ?_, hρd⟩
    rw [mem_ball, ← edist_lt_ofReal]
    exact (edist_le_ediam_of_mem hz hy).trans_lt hρD
  choose! y ρ hρ0 hρδ hty hρd using hball
  let B : ℕ → Set X := fun n => ⋃ _ : (t n).Nonempty, ball (y n) (ρ n)
  have hAB : A ⊆ ⋃ n, B n := fun z hz => by
    obtain ⟨n, hn⟩ := mem_iUnion.1 (htA hz)
    exact mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨⟨z, hn⟩, hty n ⟨z, hn⟩ hn⟩⟩
  obtain ⟨T, hT⟩ := hA.elim_finite_subcover B (fun n => isOpen_iUnion fun _ => isOpen_ball) hAB
  refine ⟨(T.filter fun n => (t n).Nonempty).image fun n => (y n, ρ n), ?_, fun z hz => ?_, ?_⟩
  · simp only [Finset.mem_image, Finset.mem_filter]
    rintro _ ⟨i, ⟨-, hi⟩, rfl⟩
    exact ⟨hρ0 i hi, hρδ i hi⟩
  · obtain ⟨n, hnT, hzn⟩ := mem_iUnion₂.1 (hT hz)
    obtain ⟨hn, hzn⟩ := mem_iUnion.1 hzn
    exact mem_iUnion₂.2 ⟨(y n, ρ n), Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hnT, hn⟩),
      hzn⟩
  calc ∑ p ∈ (T.filter fun n => (t n).Nonempty).image (fun n => (y n, ρ n)),
        ENNReal.ofReal p.2 ^ d
      ≤ ∑ i ∈ T.filter fun n => (t n).Nonempty, ENNReal.ofReal (ρ i) ^ d :=
        Finset.sum_image_le_of_nonneg fun _ _ => zero_le
    _ ≤ ∑ i ∈ T.filter fun n => (t n).Nonempty,
          ((⨆ _ : (t i).Nonempty, ediam (t i) ^ d) + ε' i) :=
        Finset.sum_le_sum fun i hi => by
          rw [iSup_pos (Finset.mem_filter.1 hi).2]
          exact hρd i (Finset.mem_filter.1 hi).2
    _ ≤ ∑' i, ((⨆ _ : (t i).Nonempty, ediam (t i) ^ d) + ε' i) := sum_le_tsum _
    _ = S + ∑' i, (ε' i : ℝ≥0∞) := tsum_add
    _ < S + ε := ENNReal.add_lt_add_left htc.ne_top hε'
    _ < c := hεc

end Cover

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E}

/-- **Cutting out a neighborhood of the frontier.** If an open set `G` contains the frontier of
`s` inside an open set `V`, then `P(s \ G; V) ≤ P(G; V)`: inside `V` the set `s \ G` is empty on
`G` and on the exterior of `s`, and agrees with `Gᶜ` on the interior of `s`. No measurability of
`s` is needed. -/
theorem perimeter_diff_le_of_frontier_inter_subset {V : Opens E} {G : Set E} (hG : IsOpen G)
    (h : frontier s ∩ V ⊆ G) :
    perimeter μ V (s \ G) ≤ perimeter μ V G := by
  -- Inside `V`, `s \ G` agrees with the open set `interior s \ G`.
  have hint : (s \ G) ∩ V = (interior s \ G) ∩ V := by
    ext y
    refine ⟨fun ⟨⟨hys, hyG⟩, hyV⟩ => ⟨⟨by_contra fun hy => hyG (h ⟨⟨subset_closure hys, hy⟩, hyV⟩),
      hyG⟩, hyV⟩, fun ⟨⟨hys, hyG⟩, hyV⟩ => ⟨⟨interior_subset hys, hyG⟩, hyV⟩⟩
  rw [perimeter_congr_of_inter_eq hint]
  have hli (U : Set E) : LocallyIntegrableOn ((interior s \ G).indicator (1 : E → ℝ)) U μ :=
    ((locallyIntegrable_const 1).indicator
      (isOpen_interior.measurableSet.diff hG.measurableSet)).locallyIntegrableOn U
  let W₁ : Opens E := V ⊓ ⟨G, hG⟩
  let W₂ : Opens E := V ⊓ ⟨interior s, isOpen_interior⟩
  let W₃ : Opens E := V ⊓ ⟨(closure s)ᶜ, isClosed_closure.isOpen_compl⟩
  have hV : V ≤ W₁ ⊔ W₂ ⊔ W₃ := fun y hy => by
    by_cases h₂ : y ∈ interior s
    · exact Or.inl (Or.inr ⟨hy, h₂⟩)
    by_cases h₃ : y ∈ closure s
    · exact Or.inl (Or.inl ⟨hy, h ⟨⟨h₃, h₂⟩, hy⟩⟩)
    · exact Or.inr ⟨hy, h₃⟩
  have h₁ : perimeter μ W₁ (interior s \ G) = 0 := by
    rw [perimeter_congr_of_inter_eq (t := ∅) (by ext y; simp [W₁]; tauto), perimeter_empty]
  have h₃ : perimeter μ W₃ (interior s \ G) = 0 := by
    rw [perimeter_congr_of_inter_eq (t := ∅) ?_, perimeter_empty]
    ext y
    simp only [mem_inter_iff, Set.mem_sdiff, SetLike.mem_coe, mem_empty_iff_false, false_and,
      iff_false]
    exact fun ⟨⟨hys, _⟩, hy⟩ => hy.2 (subset_closure (interior_subset hys))
  have h₂ : perimeter μ W₂ (interior s \ G) ≤ perimeter μ V G := by
    rw [perimeter_congr_of_inter_eq (t := Gᶜ) ?_, perimeter_compl]
    · exact perimeter_mono inf_le_left
    ext y
    simp only [mem_inter_iff, Set.mem_sdiff, mem_compl_iff, SetLike.mem_coe]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.2, h.1⟩, h.2⟩⟩
  calc perimeter μ V (interior s \ G) ≤ perimeter μ (W₁ ⊔ W₂ ⊔ W₃) (interior s \ G) :=
        perimeter_mono hV
    _ ≤ perimeter μ W₁ (interior s \ G) + perimeter μ W₂ (interior s \ G) +
        perimeter μ W₃ (interior s \ G) := by
      simp only [perimeter_def]
      exact (totalVariationOn_sup_le (hli _)).trans
        (add_le_add (totalVariationOn_sup_le (hli _)) le_rfl)
    _ ≤ perimeter μ V G := by rw [h₁, h₃, zero_add, add_zero]; exact h₂

/-- A finite union of open balls `ball p.1 p.2`, `p ∈ T`, has perimeter at most
`n μ(B(0, 1)) ∑ p.2 ^ (n - 1)`. -/
private lemma perimeter_biUnion_ball_le (T : Finset (E × ℝ)) (hT : ∀ p ∈ T, 0 < p.2) :
    perimeter μ ⊤ (⋃ p ∈ T, ball p.1 p.2) ≤ finrank ℝ E * μ (ball 0 1) *
      ∑ p ∈ T, ENNReal.ofReal p.2 ^ ((finrank ℝ E - 1 : ℕ) : ℝ) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha, mul_add]
    have ha0 := hT a (Finset.mem_insert_self a T)
    refine (perimeter_union_le measurableSet_ball.nullMeasurableSet
      (isOpen_biUnion fun _ _ => isOpen_ball).measurableSet.nullMeasurableSet).trans
      (add_le_add ?_ (ih fun p hp => hT p (Finset.mem_insert_of_mem hp)))
    rw [perimeter_ball ha0, ENNReal.rpow_natCast, ← ENNReal.ofReal_pow ha0.le, mul_right_comm]

/-- The volume of a finite union of open balls `ball p.1 p.2`, `p ∈ T`, of radii in `(0, δ]` is at
most `δ μ(B(0, 1)) ∑ p.2 ^ (n - 1)`, in positive dimension. -/
private lemma measure_biUnion_ball_le (hn : finrank ℝ E ≠ 0) (T : Finset (E × ℝ)) {δ : ℝ}
    (hT : ∀ p ∈ T, 0 < p.2 ∧ p.2 ≤ δ) :
    μ (⋃ p ∈ T, ball p.1 p.2) ≤ ENNReal.ofReal δ * μ (ball 0 1) *
      ∑ p ∈ T, ENNReal.ofReal p.2 ^ ((finrank ℝ E - 1 : ℕ) : ℝ) := by
  refine (measure_biUnion_finset_le T _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hρ0, hρδ⟩ := hT p hp
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  calc μ (ball p.1 p.2) = ENNReal.ofReal p.2 ^ k * ENNReal.ofReal p.2 * μ (ball 0 1) := by
        rw [μ.addHaar_ball_of_pos _ hρ0, hk, pow_succ, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow hρ0.le]
    _ ≤ ENNReal.ofReal p.2 ^ k * ENNReal.ofReal δ * μ (ball 0 1) := by gcongr
    _ = _ := by rw [hk, Nat.succ_sub_one, ENNReal.rpow_natCast]; ring

/-- The perimeter in `V`, an open set with compact closure, is at most `n μ(B(0, 1)) c` whenever
`c` exceeds the `(n - 1)`-dimensional Hausdorff measure of the frontier in `closure V`. -/
private lemma perimeter_le_mul_of_hausdorffMeasure_lt (hn : finrank ℝ E ≠ 0)
    (hs : MeasurableSet s) {V : Opens E} (hV : IsCompact (closure (V : Set E))) {c : ℝ≥0∞}
    (hc : c ≠ ∞) (hfc : μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s ∩ closure V) < c) :
    perimeter μ V s ≤ finrank ℝ E * μ (ball 0 1) * c := by
  set C : ℝ≥0∞ := finrank ℝ E * μ (ball 0 1)
  have hA : IsCompact (frontier s ∩ closure V) := hV.inter_left isClosed_frontier
  choose T hρ hcov hsum using fun k : ℕ =>
    exists_finset_ball_cover_sum_rpow_lt_of_isCompact hA hfc (Nat.one_div_pos_of_nat (n := k))
  set G : ℕ → Set E := fun k => ⋃ p ∈ T k, ball p.1 p.2
  have hGo (k : ℕ) : IsOpen (G k) := isOpen_biUnion fun _ _ => isOpen_ball
  have hper (k : ℕ) : perimeter μ V (s \ G k) ≤ C * c :=
    (perimeter_diff_le_of_frontier_inter_subset (hGo k) fun y hy =>
      hcov k ⟨hy.1, subset_closure hy.2⟩).trans <| (perimeter_mono le_top).trans <|
        (perimeter_biUnion_ball_le _ fun p hp => (hρ k p hp).1).trans (by gcongr; exact (hsum k).le)
  -- `s \ G k → s` in measure, since the volume of `G k` tends to zero.
  have hconv (K : Set E) : Tendsto (fun k => μ (((s \ G k) ∆ s) ∩ K)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1)) * μ (ball 0 1) * c)
        atTop (𝓝 0) := by
      have h0 := ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
        (Or.inr (measure_ball_lt_top (μ := μ) (x := 0) (r := 1)).ne)
      simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hc)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) fun k => ?_
    refine (measure_mono fun y hy => ?_).trans ((measure_biUnion_ball_le hn (T k)
      (hρ k)).trans (by gcongr; exact (hsum k).le))
    rcases hy.1 with h | h
    · exact absurd h.1.1 h.2
    · exact not_not.1 fun hG => h.2 ⟨h.1, hG⟩
  calc perimeter μ V s ≤ liminf (fun k => perimeter μ V (s \ G k)) atTop :=
        perimeter_le_liminf (.of_forall fun k => (hs.diff (hGo k).measurableSet).nullMeasurableSet)
          hs.nullMeasurableSet fun K _ _ => hconv K
    _ ≤ C * c := liminf_le_of_le (by isBoundedDefault) fun b hb => by
        obtain ⟨k, hk⟩ := hb.exists
        exact hk.trans (hper k)

/-- The perimeter in an open set `V` with compact closure is at most
`n μ(B(0, 1)) μH[n - 1](∂s ∩ closure V)`. -/
private lemma perimeter_le_mul_hausdorffMeasure_frontier_inter_closure (hn : finrank ℝ E ≠ 0)
    (hs : MeasurableSet s) {V : Opens E} (hV : IsCompact (closure (V : Set E))) :
    perimeter μ V s ≤
      finrank ℝ E * μ (ball 0 1) * μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s ∩ closure V) := by
  set M := μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s ∩ closure V)
  have hC : (finrank ℝ E : ℝ≥0∞) * μ (ball 0 1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hn) (measure_ball_pos μ 0 one_pos).ne'
  by_cases hM : M = ∞
  · rw [hM, ENNReal.mul_top hC]
    exact le_top
  have hlim : Tendsto (fun k : ℕ => (finrank ℝ E : ℝ≥0∞) * μ (ball 0 1) * (M + (k + 1 : ℝ≥0∞)⁻¹))
      atTop (𝓝 ((finrank ℝ E : ℝ≥0∞) * μ (ball 0 1) * M)) := by
    refine ENNReal.Tendsto.const_mul ?_ (.inr (ENNReal.mul_ne_top (by simp)
      measure_ball_lt_top.ne))
    simpa using tendsto_const_nhds.add (ENNReal.tendsto_inv_nat_nhds_zero.comp
      (tendsto_add_atTop_nat 1))
  refine ge_of_tendsto' hlim fun k => perimeter_le_mul_of_hausdorffMeasure_lt hn hs hV
    (ENNReal.add_ne_top.2 ⟨hM, by simp⟩) (ENNReal.lt_add_right hM (by simp))

/-- A set whose frontier has finite `μH[n - 1]` measure in `Ω` agrees almost everywhere in `Ω`
with its interior, in positive dimension: the frontier is null in `Ω`. -/
private lemma ae_eq_interior_of_hausdorffMeasure_frontier_inter_ne_top (hn : finrank ℝ E ≠ 0)
    (h : μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s ∩ Ω) ≠ ∞) :
    s =ᵐ[μ.restrict Ω] interior s := by
  have hH : μH[((finrank ℝ E : ℕ) : ℝ)] (frontier s ∩ Ω) = 0 :=
    (hausdorffMeasure_zero_or_top (Nat.cast_lt.2 (Nat.sub_lt (Nat.pos_of_ne_zero hn) one_pos))
      _).resolve_right h
  have hHE : μHE[finrank ℝ E] (frontier s ∩ Ω) = 0 := by
    rw [euclideanHausdorffMeasure_def, smul_apply, hH, smul_zero]
  have hnull : μ (frontier s ∩ Ω) = 0 := absolutelyContinuous_isAddHaarMeasure μ _ hHE
  refine ae_eq_set.2 ⟨?_, by simp [sdiff_eq_empty.2 interior_subset]⟩
  rw [Measure.restrict_apply' Ω.isOpen.measurableSet]
  exact measure_mono_null (inter_subset_inter_left _
    (sdiff_subset_sdiff_left subset_closure)) hnull

/-- **Perimeter bound by the Hausdorff measure of the frontier.** For an additive Haar measure `μ`
on a space of dimension `n`, every set `s` (measurable or not) and every open set `Ω`,
`P(s; Ω) ≤ n μ(B(0, 1)) μH[n - 1](∂s ∩ Ω)`. In particular a set whose frontier has finite
`(n - 1)`-dimensional Hausdorff measure in `Ω` has finite perimeter in `Ω`. -/
theorem perimeter_le_mul_hausdorffMeasure_frontier_inter (μ : Measure E) [μ.IsAddHaarMeasure]
    (Ω : Opens E) (s : Set E) :
    perimeter μ Ω s ≤
      finrank ℝ E * μ (ball 0 1) * μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s ∩ Ω) := by
  rcases eq_or_ne (finrank ℝ E) 0 with hn | hn
  · have : Subsingleton E := finrank_zero_iff.1 hn
    rw [perimeter_of_subsingleton]
    exact zero_le
  set M := μH[((finrank ℝ E - 1 : ℕ) : ℝ)] (frontier s ∩ Ω)
  by_cases hM : M = ∞
  · rw [hM, ENNReal.mul_top (mul_ne_zero (by exact_mod_cast hn)
      (measure_ball_pos μ 0 one_pos).ne')]
    exact le_top
  -- Replace `s` by its interior, then bound the perimeter in relatively compact open sets.
  rw [perimeter_congr_ae (ae_eq_interior_of_hausdorffMeasure_frontier_inter_ne_top hn hM),
    perimeter_def, totalVariationOn_le_iff]
  intro φ hφ
  obtain ⟨V, hVo, hKV, hVΩ, hV⟩ := exists_open_between_and_isCompact_closure
    φ.hasCompactSupport.isCompact Ω.isOpen φ.tsupport_subset
  refine (ofReal_integral_le_totalVariationOn_of_tsupport_subset (Ω' := ⟨V, hVo⟩) φ hφ
    hKV).trans ?_
  rw [← perimeter_def]
  refine (perimeter_le_mul_hausdorffMeasure_frontier_inter_closure (μ := μ) hn
    isOpen_interior.measurableSet (V := ⟨V, hVo⟩) hV).trans ?_
  gcongr
  exact measure_mono (inter_subset_inter frontier_interior_subset hVΩ)

/-- `μHE[d]` is a positive finite multiple of `μH[d]`, so they have the same null and finite
sets. -/
private lemma euclideanHausdorffMeasure_ne_top_iff {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {d : ℕ} {t : Set X} :
    μHE[d] t ≠ ∞ ↔ μH[(d : ℝ)] t ≠ ∞ := by
  rw [euclideanHausdorffMeasure_def, smul_apply, ENNReal.smul_def, smul_eq_mul, ne_eq,
    ENNReal.mul_eq_top]
  simp [addHaarScalarFactor_volume_hausdorffMeasure_ne_zero]

/-- **Federer's finite-perimeter criterion for the topological frontier.** If the frontier of `s`
has locally finite `(n - 1)`-dimensional Hausdorff measure in `Ω`, that is `Hⁿ⁻¹(∂s ∩ K) < ∞`
for every compact `K ⊆ Ω`, then `s` has locally finite perimeter in `Ω`: every compact subset of
`Ω` has an open neighborhood `U` with `P(s; U) < ∞`. No measurability of `s` is assumed. -/
theorem exists_perimeter_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top
    (h : ∀ K, IsCompact K → K ⊆ Ω → μHE[finrank ℝ E - 1] (frontier s ∩ K) ≠ ∞) {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ U : Opens E, K ⊆ (U : Set E) ∧ perimeter μ U s ≠ ∞ := by
  obtain ⟨V, hVo, hKV, hVΩ, hV⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  refine ⟨⟨V, hVo⟩, hKV, ne_top_of_le_ne_top ?_
    (perimeter_le_mul_hausdorffMeasure_frontier_inter μ ⟨V, hVo⟩ s)⟩
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne)
    (ne_top_of_le_ne_top (euclideanHausdorffMeasure_ne_top_iff.1 (h _ hV hVΩ)) ?_)
  exact measure_mono (inter_subset_inter_right _ subset_closure)

/-- **The perimeter is at most the Hausdorff measure of the frontier.** In dimension `n ≥ 2`,
every set `s`, measurable or not, has `P(s; Ω) ≤ Hⁿ⁻¹(∂s ∩ Ω)` in every open set `Ω`. When the
right side is finite, `s` has locally finite perimeter in `Ω` by
`TauCeti.exists_perimeter_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top`, and the
bound follows from De Giorgi's `P(s; Ω) = Hⁿ⁻¹(∂*s)` since `∂*s ⊆ ∂s`. -/
theorem perimeter_le_euclideanHausdorffMeasure_frontier_inter (hn : 2 ≤ finrank ℝ E)
    (Ω : Opens E) (s : Set E) :
    perimeter volume Ω s ≤ μHE[finrank ℝ E - 1] (frontier s ∩ Ω) := by
  by_cases hM : μHE[finrank ℝ E - 1] (frontier s ∩ Ω) = ∞
  · rw [hM]
    exact le_top
  rw [perimeter_congr_ae (ae_eq_interior_of_hausdorffMeasure_frontier_inter_ne_top (by omega)
    (euclideanHausdorffMeasure_ne_top_iff.1 hM))]
  have hfin (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      ∃ U : Opens E, K ⊆ (U : Set E) ∧
        totalVariationOn volume U ((interior s).indicator 1) ≠ ∞ := by
    simpa only [perimeter_def] using
      exists_perimeter_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top (fun K _ _ =>
        ne_top_of_le_ne_top hM (measure_mono (inter_subset_inter frontier_interior_subset
          ‹K ⊆ Ω›))) hK hKΩ
  rw [perimeter_eq_euclideanHausdorffMeasure_reducedBoundary hn
    (((locallyIntegrable_const 1).indicator isOpen_interior.measurableSet).locallyIntegrableOn _)
    hfin]
  exact measure_mono (subset_inter (reducedBoundary_subset_frontier.trans frontier_interior_subset)
    reducedBoundary_subset)

end TauCeti
