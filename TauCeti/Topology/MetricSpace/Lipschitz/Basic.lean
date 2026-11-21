/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Continuity
import TauCeti.Algebra.Order.Field.Basic

/-!
# Basic Lipschitz estimates

This file collects elementary `LipschitzWith` facts and bounded-gauge estimates:

* The shifted positive part `t ↦ max (t - k) 0` is `1`-Lipschitz on the real line.
* Pointwise infima `x ↦ sInf ((F x) '' S)` of uniformly `K`-Lipschitz families bounded below at
  each point are `K`-Lipschitz.
* A `K`-Lipschitz map with `1 ≤ K` scales the bounded-metric gauge `d / (1 + d)` by at most `K`,
  and a `K`-Lipschitz binary map on a product pseudometric space bounds the output gauge by `K`
  times the sum of the component gauges.
* For uniformly `K`-Lipschitz maps `u i` on a seminormed group, pointwise limits of the translates
  `z ↦ u i (z + σ i)` and `z ↦ u i (z + σ' i)` are translates of each other when `σ' i - σ i`
  converges.

## Main results

* `TauCeti.lipschitzWith_max_sub_const_zero`: the shifted positive part is `1`-Lipschitz.
* `TauCeti.lipschitzWith_sInf_image`: pointwise infimum over an index set `S` preserves a uniform
  Lipschitz constant `K` when each slice `(F x) '' S` is bounded below.
* `LipschitzWith.dist_div_one_add_dist_le_mul`: bounded-gauge estimate for a `K`-Lipschitz map
  with `1 ≤ K`.
* `LipschitzWith.dist_div_one_add_dist_prod_le`: bounded-gauge estimate for a `K`-Lipschitz binary
  map `α × β → γ` with `1 ≤ K`.
* `TauCeti.apply_eq_apply_add_of_tendsto_sub`: limits of translates of uniformly Lipschitz maps
  along shifts with convergent difference are translates of each other.
* `TauCeti.apply_eq_apply_add_prodMk_zero_of_tendsto_sub`: the same for maps on a product
  translated in the first coordinate.

## References

* H. Federer, *Geometric Measure Theory*, Springer (1969), Section 2.2.7.
-/

public section

open scoped NNReal

namespace TauCeti

open Filter Topology in
/-- **Limits of translates of uniformly Lipschitz maps.** Let `u i` be `K`-Lipschitz maps on a
seminormed additive group, and let `σ i`, `σ' i` be shifts whose difference `σ' i - σ i` tends to
`δ`. If the translates `z ↦ u i (z + σ i)` converge pointwise to `g` and the translates
`z ↦ u i (z + σ' i)` converge pointwise to `g'`, then `g'` is the translate `z ↦ g (z + δ)`. -/
theorem apply_eq_apply_add_of_tendsto_sub {ι E F : Type*} [SeminormedAddCommGroup E]
    [MetricSpace F] {l : Filter ι} [l.NeBot] {u : ι → E → F} {K : ℝ≥0}
    (hu : ∀ i, LipschitzWith K (u i)) {σ σ' : ι → E} {δ : E}
    (hδ : Tendsto (fun i ↦ σ' i - σ i) l (𝓝 δ)) {g g' : E → F}
    (hg : ∀ z, Tendsto (fun i ↦ u i (z + σ i)) l (𝓝 (g z)))
    (hg' : ∀ z, Tendsto (fun i ↦ u i (z + σ' i)) l (𝓝 (g' z))) (z : E) :
    g' z = g (z + δ) := by
  refine tendsto_nhds_unique (hg' z) ((hg (z + δ)).congr_dist ?_)
  -- The points `z + δ + σ i` and `z + σ' i` are `‖σ' i - σ i - δ‖` apart.
  have h : Tendsto (fun i ↦ (K : ℝ) * ‖σ' i - σ i - δ‖) l (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hδ).const_mul (K : ℝ)
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun i ↦ ?_) h
  calc dist (u i (z + δ + σ i)) (u i (z + σ' i))
      ≤ K * dist (z + δ + σ i) (z + σ' i) := (hu i).dist_le_mul _ _
    _ = K * ‖σ' i - σ i - δ‖ := by
      rw [dist_eq_norm, ← norm_neg]
      congr 2
      abel

open Filter Topology in
/-- **Limits of translates in the first coordinate.** The special case of
`apply_eq_apply_add_of_tendsto_sub` for maps on a product `E × E'` translated by `(σ i, 0)` and
`(σ' i, 0)`: if `σ' i - σ i → δ`, the two pointwise limits differ by the translation `(δ, 0)`. -/
theorem apply_eq_apply_add_prodMk_zero_of_tendsto_sub {ι E E' F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E'] [MetricSpace F] {l : Filter ι}
    [l.NeBot] {u : ι → E × E' → F} {K : ℝ≥0} (hu : ∀ i, LipschitzWith K (u i)) {σ σ' : ι → E}
    {δ : E} (hδ : Tendsto (fun i ↦ σ' i - σ i) l (𝓝 δ)) {g g' : E × E' → F}
    (hg : ∀ z, Tendsto (fun i ↦ u i (z + (σ i, 0))) l (𝓝 (g z)))
    (hg' : ∀ z, Tendsto (fun i ↦ u i (z + (σ' i, 0))) l (𝓝 (g' z))) (z : E × E') :
    g' z = g (z + (δ, 0)) :=
  apply_eq_apply_add_of_tendsto_sub hu (by simpa using hδ.prodMk_nhds tendsto_const_nhds) hg hg' z

/-- The shifted positive part `t ↦ max (t - k) 0` is `1`-Lipschitz on the real line. -/
theorem lipschitzWith_max_sub_const_zero (k : ℝ) :
    LipschitzWith 1 (fun t : ℝ => max (t - k) 0) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right] using
      abs_max_sub_max_le_abs (x - k) (y - k) 0

/-- Pointwise infimum over `S` preserves a uniform Lipschitz constant `K` when each slice is
bounded below. -/
theorem lipschitzWith_sInf_image {α ι : Type*} [PseudoMetricSpace α] {S : Set ι}
    {F : α → ι → ℝ} {K : NNReal} (hbdd : ∀ x, BddBelow ((F x) '' S))
    (hlip : ∀ i ∈ S, LipschitzWith K (fun x ↦ F x i)) :
    LipschitzWith K (fun x ↦ sInf ((F x) '' S)) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq]
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp only [Set.image_empty, Real.sInf_empty, sub_self, abs_zero]; positivity
  · have hle (u v : α) : sInf ((F u) '' S) - (K : ℝ) * dist u v ≤ sInf ((F v) '' S) := by
      refine le_csInf (hS.image _) ?_
      rintro _ ⟨i, hi, rfl⟩
      have hd : F u i - F v i ≤ (K : ℝ) * dist u v := (le_abs_self _).trans <| by
        simpa only [Real.dist_eq] using (hlip i hi).dist_le_mul u v
      linarith [csInf_le (hbdd u) ⟨i, hi, rfl⟩]
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hle x y], by linarith [dist_comm x y ▸ hle y x]⟩

end TauCeti

namespace LipschitzWith

/-- For a `K`-Lipschitz map `f : α → β` with `1 ≤ K`, the bounded-metric gauge `d / (1 + d)`
satisfies `dist (f x) (f y) / (1 + dist (f x) (f y)) ≤ K * (dist x y / (1 + dist x y))`. -/
theorem dist_div_one_add_dist_le_mul {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {K : ℝ≥0} {f : α → β} (hf : LipschitzWith K f) (hK : 1 ≤ K) (x y : α) :
    dist (f x) (f y) / (1 + dist (f x) (f y)) ≤
      (K : ℝ) * (dist x y / (1 + dist x y)) :=
  (TauCeti.div_one_add_mono dist_nonneg (hf.dist_le_mul x y)).trans
    (TauCeti.mul_div_one_add_mul_le (NNReal.one_le_coe.mpr hK) dist_nonneg)

/-- For a `K`-Lipschitz binary map `f : α × β → γ` with `1 ≤ K`, the bounded-metric gauge of `f`
is bounded by `K` times the sum of the component gauges. -/
theorem dist_div_one_add_dist_prod_le {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ] {K : ℝ≥0} {f : α × β → γ} (hf : LipschitzWith K f) (hK : 1 ≤ K)
    (p q : α × β) :
    dist (f p) (f q) / (1 + dist (f p) (f q)) ≤
      (K : ℝ) * (dist p.1 q.1 / (1 + dist p.1 q.1)) +
        (K : ℝ) * (dist p.2 q.2 / (1 + dist p.2 q.2)) := by
  calc dist (f p) (f q) / (1 + dist (f p) (f q))
      ≤ (K : ℝ) * (dist p q / (1 + dist p q)) :=
        hf.dist_div_one_add_dist_le_mul hK p q
    _ ≤ (K : ℝ) * (dist p.1 q.1 / (1 + dist p.1 q.1) +
          dist p.2 q.2 / (1 + dist p.2 q.2)) := by
        refine mul_le_mul_of_nonneg_left ?_ K.coe_nonneg
        rw [Prod.dist_eq]
        rcases le_total (dist p.1 q.1) (dist p.2 q.2) with h | h
        · rw [max_eq_right h]
          exact le_add_of_nonneg_left (TauCeti.div_one_add_nonneg dist_nonneg)
        · rw [max_eq_left h]
          exact le_add_of_nonneg_right (TauCeti.div_one_add_nonneg dist_nonneg)
    _ = (K : ℝ) * (dist p.1 q.1 / (1 + dist p.1 q.1)) +
          (K : ℝ) * (dist p.2 q.2 / (1 + dist p.2 q.2)) := mul_add _ _ _

end LipschitzWith
