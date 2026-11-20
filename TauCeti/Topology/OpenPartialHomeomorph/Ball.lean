/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Balls of a chart

An open partial homeomorphism `e : M → V` into a pseudometric space pulls the ball of radius `ε`
about `e b` back to the open set `OpenPartialHomeomorph.chartBall e b ε` of `M`, a neighbourhood
of `b` when `b ∈ e.source` and `0 < ε`. When `V` is a seminormed group and the ball lies in the
target of `e`, the map `x ↦ e x - e b` is a homeomorphism of this set with the ball of radius `ε`
about `0` (`OpenPartialHomeomorph.chartBallHomeomorph`).
-/

public section

open Metric Set

namespace OpenPartialHomeomorph

section PseudoMetricSpace

variable {M V : Type*} [TopologicalSpace M] [PseudoMetricSpace V] (e : OpenPartialHomeomorph M V)

/-- The open set `e.source ∩ e⁻¹(D)`, for the ball `D` about `e b` of radius `ε`. It is a
neighbourhood of `b` when `b ∈ e.source` and `0 < ε` (`OpenPartialHomeomorph.mem_chartBall_self`).
-/
def chartBall (b : M) (ε : ℝ) : Set M :=
  e.source ∩ e ⁻¹' ball (e b) ε

@[simp]
lemma mem_chartBall {b x : M} {ε : ℝ} :
    x ∈ chartBall e b ε ↔ x ∈ e.source ∧ e x ∈ ball (e b) ε :=
  Iff.rfl

@[simp]
lemma isOpen_chartBall (b : M) (ε : ℝ) : IsOpen (chartBall e b ε) :=
  e.isOpen_inter_preimage isOpen_ball

lemma chartBall_subset_source (b : M) (ε : ℝ) : chartBall e b ε ⊆ e.source :=
  inter_subset_left

lemma mem_chartBall_self {b : M} (hb : b ∈ e.source) {ε : ℝ} (hε₀ : 0 < ε) :
    b ∈ chartBall e b ε :=
  ⟨hb, mem_ball_self hε₀⟩

/-- A ball about `e b` inside the target of `e` is the image of the corresponding chart ball. -/
lemma image_chartBall {b : M} {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) :
    e '' chartBall e b ε = ball (e b) ε := by
  rw [chartBall, ← e.symm_image_eq_source_inter_preimage hε]
  exact e.image_symm_image_of_subset_target hε

end PseudoMetricSpace

section SeminormedAddCommGroup

variable {M V : Type*} [TopologicalSpace M] [SeminormedAddCommGroup V]
  (e : OpenPartialHomeomorph M V) {b : M} {ε : ℝ} (hε : ball (e b) ε ⊆ e.target)

include hε in
/-- The chart ball `chartBall e b ε` is homeomorphic to the ball of radius `ε` about `0` through
`x ↦ e x - e b`, when the ball about `e b` lies in the target of `e`. -/
def chartBallHomeomorph : chartBall e b ε ≃ₜ ball (0 : V) ε :=
  (e.transHomeomorph (IsometryEquiv.subRight (e b)).toHomeomorph).homeomorphOfImageSubsetSource
    (e.chartBall_subset_source b ε) <| by
      rw [transHomeomorph_apply, image_comp, image_chartBall e hε]
      simp [IsometryEquiv.image_ball]

@[simp]
lemma coe_chartBallHomeomorph_apply (x : chartBall e b ε) :
    (chartBallHomeomorph e hε x : V) = e x - e b :=
  (rfl)

@[simp]
lemma coe_chartBallHomeomorph_symm_apply (v : ball (0 : V) ε) :
    ((chartBallHomeomorph e hε).symm v : M) = e.symm (v + e b) :=
  (rfl)

end SeminormedAddCommGroup

end OpenPartialHomeomorph
