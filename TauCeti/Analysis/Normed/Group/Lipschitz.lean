/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Limits of translates of uniformly Lipschitz maps

For uniformly `K`-Lipschitz maps `u i` on a seminormed group, pointwise limits of the translates
`z ↦ u i (z + σ i)` and `z ↦ u i (z + σ' i)` are translates of each other when `σ' i - σ i`
converges.

## Main results

* `TauCeti.apply_eq_apply_add_of_tendsto_sub`: limits of translates of uniformly Lipschitz maps
  along shifts with convergent difference are translates of each other.
* `TauCeti.apply_eq_apply_add_prodMk_zero_of_tendsto_sub`: the same for maps on a product
  translated in the first coordinate.
-/

public section

open Filter Topology
open scoped NNReal

namespace TauCeti

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

end TauCeti
