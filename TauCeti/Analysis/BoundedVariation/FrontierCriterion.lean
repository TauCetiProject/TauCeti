/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.DeGiorgi
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.BoundedVariation.Submodularity
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Haar.Hausdorff.Frontier
import TauCeti.MeasureTheory.Measure.Hausdorff.BallCover

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
  neighborhood in which `s` has finite perimeter, and so does the interior of `s`
  (`TauCeti.exists_perimeter_interior_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top`);
* `TauCeti.perimeter_le_euclideanHausdorffMeasure_frontier_inter`: in dimension `n ≥ 2`, the sharp
  bound `P(s; Ω) ≤ Hⁿ⁻¹(∂s ∩ Ω)` for every set `s`, combining the criterion with De Giorgi's
  representation `P(s; Ω) = Hⁿ⁻¹(∂*s)` of the perimeter of a set of locally finite perimeter.

The proof uses three further results, in more basic modules.
`TauCeti.perimeter_diff_le_of_frontier_inter_subset`: if an open set `G` contains `∂s ∩ V`, then
`P(s \ G; V) ≤ P(G; V)`. `TauCeti.exists_finset_ball_cover_sum_rpow_lt_of_isCompact`, in any
metric space: a compact set `A` is covered by finitely many arbitrarily small open balls
`B(xᵢ, ρᵢ)` with `∑ ρᵢ ^ d < c` for any `c > μH[d] A`. And
`TauCeti.ae_eq_interior_of_hausdorffMeasure_frontier_inter_ne_top`: a set whose frontier has
finite `μH[n - 1]` measure in `Ω` agrees almost everywhere in `Ω` with its interior.

## Strategy

When `Hⁿ⁻¹(∂s ∩ Ω)` is finite, the frontier is Lebesgue null in `Ω`, so `s` may be replaced by its
interior. Fix an open set `V` with compact closure in `Ω`. Cover the compact set `∂s ∩ closure V`
by finitely many open balls `B(xᵢ, ρᵢ)` of radii at most `δ` with `∑ ρᵢ ^ (n - 1) < c` for a
chosen `c > μH[n - 1](∂s ∩ closure V)`, and let `G` be their union. The set `s \ G` is empty on
`G` and on the exterior of `s`, and agrees with `Gᶜ` on the interior of `s`; these three open sets
cover `V`.
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E}

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
  rw [perimeter_congr_ae (ae_eq_interior_of_hausdorffMeasure_frontier_inter_ne_top μ hn hM),
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
    (ne_top_of_le_ne_top (euclideanHausdorffMeasure_lt_top_iff.1
      (lt_top_iff_ne_top.2 (h _ hV hVΩ))).ne ?_)
  exact measure_mono (inter_subset_inter_right _ subset_closure)

/-- Under the hypothesis of Federer's criterion, the interior of `s` also has locally finite
perimeter in `Ω`, since its frontier lies in that of `s`. -/
theorem exists_perimeter_interior_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top
    (h : ∀ K, IsCompact K → K ⊆ Ω → μHE[finrank ℝ E - 1] (frontier s ∩ K) ≠ ∞) {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ U : Opens E, K ⊆ (U : Set E) ∧ perimeter μ U (interior s) ≠ ∞ :=
  exists_perimeter_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top
    (fun L hL hLΩ => ne_top_of_le_ne_top (h L hL hLΩ)
      (measure_mono (inter_subset_inter_left _ frontier_interior_subset))) hK hKΩ

/-- **The perimeter is at most the Hausdorff measure of the frontier.** In dimension `n ≥ 2`,
every set `s`, measurable or not, has `P(s; Ω) ≤ Hⁿ⁻¹(∂s ∩ Ω)` in every open set `Ω`. -/
theorem perimeter_le_euclideanHausdorffMeasure_frontier_inter (hn : 2 ≤ finrank ℝ E)
    (Ω : Opens E) (s : Set E) :
    perimeter volume Ω s ≤ μHE[finrank ℝ E - 1] (frontier s ∩ Ω) := by
  by_cases hM : μHE[finrank ℝ E - 1] (frontier s ∩ Ω) = ∞
  · rw [hM]
    exact le_top
  rw [perimeter_congr_ae (ae_eq_interior_of_hausdorffMeasure_frontier_inter_ne_top volume (by omega)
    (euclideanHausdorffMeasure_lt_top_iff.1 (lt_top_iff_ne_top.2 hM)).ne)]
  have hfin (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
      ∃ U : Opens E, K ⊆ (U : Set E) ∧
        totalVariationOn volume U ((interior s).indicator 1) ≠ ∞ := by
    simpa only [perimeter_def] using
      exists_perimeter_interior_ne_top_of_euclideanHausdorffMeasure_frontier_inter_ne_top
        (fun K _ hKΩ => ne_top_of_le_ne_top hM (measure_mono (inter_subset_inter_right _ hKΩ)))
        hK hKΩ
  rw [perimeter_eq_euclideanHausdorffMeasure_reducedBoundary hn
    (((locallyIntegrable_const 1).indicator isOpen_interior.measurableSet).locallyIntegrableOn _)
    hfin]
  exact measure_mono (subset_inter (reducedBoundary_subset_frontier.trans frontier_interior_subset)
    reducedBoundary_subset)

end TauCeti
