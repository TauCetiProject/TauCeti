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
form: when `F` is a proper closed subspace of a subspace `G`, the vector can be chosen in `G`.
This is the form used to build separated sequences along strictly decreasing chains of closed
subspaces, as in the Riesz theory of compact operators.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Riesz's lemma** relative to a larger subspace: if `F` is a closed subspace properly contained
in a subspace `G`, then `G` contains a vector of norm at most `R` at distance at least `1`
from `F`. -/
theorem riesz_lemma_of_norm_lt_of_lt {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R)
    {F G : Submodule 𝕜 E} (hFc : IsClosed (F : Set E)) (hFG : F < G) :
    ∃ x₀ ∈ G, ‖x₀‖ ≤ R ∧ ∀ y ∈ F, 1 ≤ ‖x₀ - y‖ := by
  obtain ⟨x, hxG, hxF⟩ := IsConcreteLE.exists_of_lt hFG
  obtain ⟨x₀, hx₀R, hx₀⟩ := riesz_lemma_of_norm_lt hc hR (F := F.comap G.subtype)
    (hFc.preimage continuous_subtype_val) ⟨⟨x, hxG⟩, hxF⟩
  exact ⟨x₀, x₀.2, hx₀R, fun y hy => hx₀ ⟨y, hFG.le hy⟩ hy⟩

end TauCeti

end
