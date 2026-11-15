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

It also records the translated form `TauCeti.riesz_lemma_translate`: a prescribed vector `x` can be
moved by an element of a closed subspace `F` to a vector `x - y` with `r * ‖x - y‖ ≤ ‖x - y - z‖`
for every `z ∈ F`. Unlike `riesz_lemma`, this keeps track of the coset `x + F`, which is what an
approximate Gram–Schmidt process needs.
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

/-- **Riesz's lemma**, translated form: for a closed submodule `F`, a vector `x` and `r < 1`, some
`y ∈ F` satisfies `r * ‖x - y‖ ≤ ‖x - y - z‖` for every `z ∈ F`, so `x - y` is almost as far from
`F` as its norm. For `x ∈ F` one may take `y = x`. -/
theorem riesz_lemma_translate {R : Type*} [Semiring R] [Module R E] {F : Submodule R E}
    (hFc : IsClosed (F : Set E)) (x : E) {r : ℝ} (hr : r < 1) :
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
