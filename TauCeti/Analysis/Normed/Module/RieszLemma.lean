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
and `c` is a scalar with `1 < ‖c‖ < R`, the vector can be chosen in `G` with norm at most `R`.
This is the form used to build separated sequences along strictly decreasing chains of closed
subspaces, as in the Riesz theory of compact operators.

The translated form `TauCeti.riesz_lemma_translate`, which needs no scalars, is in
`TauCeti.Analysis.Normed.Group.RieszLemma`.
-/

public section

namespace TauCeti

open SeparationQuotient in
/-- **Riesz's lemma** relative to a larger subspace: if a subspace `F` of a seminormed space is
properly contained in a subspace `G` and is closed in `G`, and `c` is a scalar with
`1 < ‖c‖ < R`, then `G` contains a vector of norm at most `R` at distance at least `1` from `F`.
If `hF : IsClosed (F : Set E)`, then `hF.preimage continuous_subtypeVal` supplies `hFc`. -/
theorem riesz_lemma_of_norm_lt_of_lt {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) {F G : Submodule 𝕜 E}
    (hFc : IsClosed (((↑) : G → E) ⁻¹' F)) (hFG : F < G) :
    ∃ x₀ ∈ G, ‖x₀‖ ≤ R ∧ ∀ y ∈ F, 1 ≤ ‖x₀ - y‖ := by
  obtain ⟨x, hxG, hxF⟩ := IsConcreteLE.exists_of_lt hFG
  -- Apply Mathlib's lemma in the normed space `SeparationQuotient G`, to the image `F'` of `F`.
  -- The quotient map `mk` preserves norms and is closed.
  let F' := (F.comap G.subtype).map (mkCLM 𝕜 G).toLinearMap
  have hF' : (F' : Set (SeparationQuotient G)) = mk '' (((↑) : G → E) ⁻¹' F) := by
    simp [F']
  -- As `F` is closed in `G`, it is saturated for inseparability, so `mk a ∈ F'` iff `a ∈ F`
  -- (membership in a preimage is membership of the image point, by `Set.mem_preimage`).
  have hmem (a : G) : mk a ∈ F' ↔ (a : E) ∈ F := by
    rw [← SetLike.mem_coe, hF']
    exact Set.ext_iff.mp (preimage_image_mk_closed hFc) a
  obtain ⟨q₀, hq₀R, hq₀⟩ := riesz_lemma_of_norm_lt hc hR (F := F')
    (hF' ▸ isClosedMap_mk _ hFc) ⟨mk ⟨x, hxG⟩, (hmem _).not.2 hxF⟩
  obtain ⟨x₀, rfl⟩ := surjective_mk q₀
  refine ⟨x₀, x₀.property, ?_, fun y hy => ?_⟩
  · simpa using hq₀R
  · simpa [← mk_sub, Submodule.coe_sub] using hq₀ _ ((hmem ⟨y, hFG.le hy⟩).2 hy)

end TauCeti

end
