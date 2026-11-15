/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded
import TauCeti.Analysis.Normed.Module.Ball.Radial.OrderIso
import TauCeti.Topology.Homeomorph.Extend

/-!
# Shrinking a compact set inside a Euclidean open piece

Let `θ : E → M` be an open embedding of a finite-dimensional real normed space into a metric space.
Every compact subset of the range of `θ` can be made as small as we like by a homeomorphism of `M`
fixing every point outside the range of `θ`: a radial squeeze of `E`
(`TauCeti.exists_homeomorph_mapsTo_closedBall`), read through `θ` and extended by the identity
(`Topology.IsOpenEmbedding.exists_homeomorph_extend`).

## Main results

* `Topology.IsOpenEmbedding.exists_homeomorph_diam_image_lt`: a compact subset of a Euclidean open
  piece is shrunk by a homeomorphism supported in that piece.
-/

public section

open Set Metric

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M]

namespace Topology.IsOpenEmbedding

/-- **Shrinking inside a Euclidean piece.** Let `θ : E → M` be an open embedding of a
finite-dimensional real normed space and `C` a compact subset of its range. For every `ε > 0` there
is a homeomorphism of `M`, fixing every point outside the range of `θ`, which maps `C` onto a set of
diameter less than `ε`. -/
theorem exists_homeomorph_diam_image_lt {θ : E → M} (hθ : IsOpenEmbedding θ) {C : Set M}
    (hC : IsCompact C) (hCθ : C ⊆ range θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : M ≃ₜ M, (∀ y ∉ range θ, ψ y = y) ∧ diam (ψ '' C) < ε := by
  -- Read in `E`, the set `C` lies in a closed ball `closedBall 0 r`.
  obtain ⟨r, hr⟩ := ((hθ.isInducing.isCompact_preimage_iff hCθ).2 hC).isBounded.subset_closedBall 0
  -- A small ball around `0` is mapped by `θ` into `ball (θ 0) (ε / 4)`.
  obtain ⟨δ, hδ, hδθ⟩ := Metric.continuousAt_iff.1 hθ.continuous.continuousAt (ε / 4)
    (by positivity)
  -- Squeeze `closedBall 0 r` into `closedBall 0 (δ / 2)`, and transport the squeeze to `M`.
  obtain ⟨ρ, hρfix, hρmaps⟩ := TauCeti.exists_homeomorph_mapsTo_closedBall (E := E) (r := r)
    (half_pos hδ)
  have hB : IsClosed (θ '' closedBall 0 (2 * r)) :=
    ((isCompact_closedBall _ _).image hθ.continuous).isClosed
  obtain ⟨ψ, hψθ, hψ⟩ := hθ.exists_homeomorph_extend ρ hB (image_subset_range _ _)
    fun z hz ↦ hρfix z (not_le.1 fun h ↦ hz (mem_image_of_mem θ (mem_closedBall_zero_iff.2 h))).le
  refine ⟨ψ, fun y hy ↦ hψ y fun h ↦ hy (image_subset_range _ _ h), ?_⟩
  have hsub : ψ '' C ⊆ closedBall (θ 0) (ε / 4) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := hCθ hy
    rw [hψθ, mem_closedBall]
    refine (hδθ ?_).le
    rw [dist_zero_right]
    exact (mem_closedBall_zero_iff.1 (hρmaps (hr hy))).trans_lt (half_lt_self hδ)
  calc diam (ψ '' C) ≤ diam (closedBall (θ 0) (ε / 4)) := diam_mono hsub isBounded_closedBall
    _ ≤ 2 * (ε / 4) := diam_closedBall (by positivity)
    _ < ε := by linarith

end Topology.IsOpenEmbedding
