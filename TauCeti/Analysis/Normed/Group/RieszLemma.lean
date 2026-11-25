/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Riesz's lemma for a prescribed vector

This file records the translated form `TauCeti.riesz_lemma_translate` of Riesz's lemma: in a
seminormed group, for any `r < 1`, a prescribed vector `x` can be moved by an element of a closed
additive submonoid `F` to a vector `x - y` with `r * ‖x - y‖ ≤ ‖x - y - z‖` for every `z ∈ F`.
Unlike Mathlib's `riesz_lemma`, this keeps track of the prescribed vector: the witness `x - y` lies
in `x - F`, which is the coset `x + F` when `F` is an additive subgroup, such as a submodule. This
is what an approximate Gram–Schmidt process needs. No scalar action is involved.

The relative form for subspaces of seminormed spaces is in
`TauCeti.Analysis.Normed.Module.RieszLemma`.
-/

public section

namespace TauCeti

/-- **Riesz's lemma**, translated form: for a closed additive submonoid `F` of a seminormed group
(for instance a closed submodule, via `Submodule.toAddSubmonoid`), a vector `x` and `r < 1`, some
`y ∈ F` satisfies `r * ‖x - y‖ ≤ ‖x - y - z‖` for every `z ∈ F`, so `x - y` is almost as far from
`F` as its norm. For `x ∈ F` one may take `y = x`. -/
theorem riesz_lemma_translate {E : Type*} [SeminormedAddCommGroup E] {F : AddSubmonoid E}
    (hFc : IsClosed (F : Set E)) (x : E) {r : ℝ} (hr : r < 1) :
    ∃ y ∈ F, ∀ z ∈ F, r * ‖x - y‖ ≤ ‖x - y - z‖ := by
  -- This adapts the proof of Mathlib's `riesz_lemma`, which takes `x - y` for a `y ∈ F` with
  -- `r * dist x y < Metric.infDist x F`, from a closed subspace of a normed space to the
  -- prescribed vector `x` and a closed additive submonoid of a seminormed group.
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
