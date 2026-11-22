/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RieszLemma

/-!
# Riesz's lemma relative to a larger subspace

Mathlib's `riesz_lemma_of_norm_lt` finds, outside a proper closed subspace `F` of a normed space,
a vector of controlled norm at distance at least `1` from `F`. This file records the relative
form, for seminormed spaces: when `F` is a proper subspace of a subspace `G` and is closed in `G`,
the vector can be chosen in `G`. This is the form used to build separated sequences along strictly
decreasing chains of closed subspaces, as in the Riesz theory of compact operators.

It also records the translated form `TauCeti.riesz_lemma_translate`: in a seminormed group, a
prescribed vector `x` can be moved by an element of a closed submodule `F` to a vector `x - y` with
`r * ‖x - y‖ ≤ ‖x - y - z‖` for every `z ∈ F`. Unlike `riesz_lemma`, this keeps track of the coset
`x + F`, which is what an approximate Gram–Schmidt process needs.
-/

public section

namespace TauCeti

open SeparationQuotient in
/-- **Riesz's lemma** relative to a larger subspace: if a subspace `F` of a seminormed space is
properly contained in a subspace `G` and is closed in `G`, then `G` contains a vector of norm at
most `R` at distance at least `1` from `F`. If `hF : IsClosed (F : Set E)`, then
`hF.preimage continuous_subtypeVal` supplies `hFc`. -/
theorem riesz_lemma_of_norm_lt_of_lt {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) {F G : Submodule 𝕜 E}
    (hFc : IsClosed (((↑) : G → E) ⁻¹' F)) (hFG : F < G) :
    ∃ x₀ ∈ G, ‖x₀‖ ≤ R ∧ ∀ y ∈ F, 1 ≤ ‖x₀ - y‖ := by
  obtain ⟨x, hxG, hxF⟩ := IsConcreteLE.exists_of_lt hFG
  -- Apply Mathlib's lemma in the normed space `SeparationQuotient G`, to the image `F'` of `F`.
  -- The quotient map `mk` preserves norms and is closed.
  let F' := (F.comap G.subtype).map (mkCLM 𝕜 G).toLinearMap
  have hF' : (F' : Set (SeparationQuotient G)) = mk '' (((↑) : G → E) ⁻¹' F) :=
    Submodule.map_coe _ _
  -- As `F` is closed in `G`, it is saturated for inseparability, so `mk a ∈ F'` iff `a ∈ F`
  -- (membership in a preimage is membership of the image point, by `Set.mem_preimage`).
  have hmem (a : G) : mk a ∈ F' ↔ (a : E) ∈ F := by
    rw [← SetLike.mem_coe, hF']
    exact Set.ext_iff.mp (preimage_image_mk_closed hFc) a
  obtain ⟨q₀, hq₀R, hq₀⟩ := riesz_lemma_of_norm_lt hc hR (F := F')
    (hF' ▸ isClosedMap_mk _ hFc) ⟨mk ⟨x, hxG⟩, (hmem _).not.2 hxF⟩
  obtain ⟨x₀, rfl⟩ := surjective_mk q₀
  refine ⟨x₀, x₀.property, ?_, fun y hy => ?_⟩
  · rwa [norm_mk, ← Submodule.norm_coe] at hq₀R
  · have h := hq₀ _ ((hmem ⟨y, hFG.le hy⟩).2 hy)
    rwa [← mk_sub, norm_mk, ← Submodule.norm_coe, Submodule.coe_sub] at h

/-- **Riesz's lemma**, translated form: for a closed submodule `F` of a seminormed group, a vector
`x` and `r < 1`, some `y ∈ F` satisfies `r * ‖x - y‖ ≤ ‖x - y - z‖` for every `z ∈ F`, so `x - y`
is almost as far from `F` as its norm. For `x ∈ F` one may take `y = x`. -/
theorem riesz_lemma_translate {R E : Type*} [Semiring R] [SeminormedAddCommGroup E] [Module R E]
    {F : Submodule R E} (hFc : IsClosed (F : Set E)) (x : E) {r : ℝ} (hr : r < 1) :
    ∃ y ∈ F, ∀ z ∈ F, r * ‖x - y‖ ≤ ‖x - y - z‖ := by
  by_cases hx : x ∈ F
  · exact ⟨x, hx, fun z _ ↦ by simp⟩
  have hd : 0 < Metric.infDist x F := (hFc.notMem_iff_infDist_pos ⟨0, F.zero_mem⟩).1 hx
  rcases le_or_gt r 0 with hr0 | hr0
  · exact ⟨0, F.zero_mem, fun z _ ↦ (mul_nonpos_of_nonpos_of_nonneg hr0 (norm_nonneg _)).trans
      (norm_nonneg _)⟩
  obtain ⟨y, hyF, hxy⟩ : ∃ y ∈ (F : Set E), dist x y < Metric.infDist x F / r :=
    (Metric.infDist_lt_iff ⟨0, F.zero_mem⟩).1 <| (lt_div_iff₀ hr0).2 <|
      mul_lt_of_lt_one_right hd hr
  refine ⟨y, hyF, fun z hz ↦ ?_⟩
  rw [dist_eq_norm, lt_div_iff₀ hr0, mul_comm] at hxy
  refine hxy.le.trans ?_
  rw [sub_sub, ← dist_eq_norm]
  exact Metric.infDist_le_dist_of_mem (F.add_mem hyF hz)

end TauCeti

end
