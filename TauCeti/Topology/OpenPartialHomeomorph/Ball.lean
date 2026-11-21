/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Topology.Homotopy.Basic

/-!
# Balls of a chart

An open partial homeomorphism `e : M → V` into a pseudometric space pulls the ball of radius `ε`
about `e b` back to the open set `OpenPartialHomeomorph.chartBall e b ε` of `M`, a neighbourhood
of `b` when `b ∈ e.source` and `0 < ε`. When `V` is a seminormed group and the ball lies in the
target of `e`, the map `x ↦ e x - e b` is a homeomorphism of this set with the ball of radius `ε`
about `0` (`OpenPartialHomeomorph.chartBallHomeomorph`). When moreover `V` is a real normed space,
scaling `e x - e b` down to `0` contracts the chart ball onto `b`
(`OpenPartialHomeomorph.chartBallContraction`), so that, for instance, a local coefficient system
on the chart ball is constant.
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

section NormedSpace

variable {M V : Type*} [TopologicalSpace M] [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  (e : OpenPartialHomeomorph M V) {b : M} (hb : b ∈ e.source) {ε : ℝ}
  (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε)

include hb in
/-- **The straight-line contraction of a chart ball onto its centre.** At time `t` it sends `x` to
the point of the chart ball read as `(1 - t) • (e x - e b)` through
`OpenPartialHomeomorph.chartBallHomeomorph`, so it starts at the identity and ends at the constant
map at `b`. -/
def chartBallContraction :
    (ContinuousMap.id (chartBall e b ε)).Homotopy
      (ContinuousMap.const (chartBall e b ε) ⟨b, e.mem_chartBall_self hb hε₀⟩) where
  toFun tx := (chartBallHomeomorph e hε).symm
    ⟨(1 - (tx.1 : ℝ)) • (chartBallHomeomorph e hε tx.2 : V),
      balanced_ball_zero.smul_mem
        (by
          rw [Real.norm_of_nonneg (sub_nonneg.2 tx.1.property.2)]
          exact sub_le_self _ tx.1.property.1)
        (chartBallHomeomorph e hε tx.2).property⟩
  continuous_toFun := (chartBallHomeomorph e hε).symm.continuous.comp <|
    ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).smul
      (continuous_subtypeVal.comp ((chartBallHomeomorph e hε).continuous.comp
        continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext <| by simp [e.left_inv (e.chartBall_subset_source b ε x.property)]
  map_one_left x := Subtype.ext <| by simp [e.left_inv hb]

@[simp]
lemma coe_chartBallContraction_apply (t : unitInterval) (x : chartBall e b ε) :
    (chartBallContraction e hb hε hε₀ (t, x) : M) = e.symm ((1 - (t : ℝ)) • (e x - e b) + e b) :=
  (rfl)

end NormedSpace

end OpenPartialHomeomorph
