/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.DeltaGeneratedSpace
public import TauCeti.Analysis.Normed.Module.Ball.Retraction
public import TauCeti.Topology.Convenient.GeneratedBy

/-!
# Delta-generated closed balls

A topological space is delta-generated (Mathlib's `DeltaGeneratedSpace`) when its topology is
coinduced by all continuous maps from the spaces `Fin n → ℝ`. This file shows that every closed
ball of a delta-generated real normed space, such as `Fin n → ℝ`, is delta-generated
(`TauCeti.instDeltaGeneratedSpaceClosedBall`). An empty ball is covered by
`TauCeti.instIsGeneratedByOfIsEmpty`. For a nonnegative radius, the radial retraction
`TauCeti.centeredRadialRetraction` is a continuous retraction of the space onto the ball. A
retraction is a quotient map, and quotients of delta-generated spaces are delta-generated.

The closed unit balls of `Fin n → ℝ` are the domains of the characteristic maps of a classical CW
complex, so this is the input for showing that CW complexes are delta-generated, in
`TauCeti.Topology.CWComplex.Classical.DeltaGenerated`.
-/

public section

open Metric Topology

namespace TauCeti

/-- **A closed ball of a delta-generated real normed space is delta-generated.** This holds for
every closed ball, including an empty one. -/
instance instDeltaGeneratedSpaceClosedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DeltaGeneratedSpace E] (x : E) (r : ℝ) : DeltaGeneratedSpace (closedBall x r) := by
  rcases lt_or_ge r 0 with hr | hr
  · have : IsEmpty (closedBall x r) := by simp [closedBall_eq_empty.2 hr]
    infer_instance
  -- The radial retraction onto the ball is continuous and fixes the ball pointwise.
  let ρ : E → closedBall x r := fun y ↦
    ⟨centeredRadialRetraction x r y, centeredRadialRetraction_mem_closedBall hr y⟩
  have hρ : Continuous ρ := (lipschitzWith_centeredRadialRetraction hr).continuous.subtype_mk _
  exact (IsQuotientMap.of_inverse continuous_subtype_val hρ fun z ↦
    Subtype.ext (centeredRadialRetraction_of_mem_closedBall z.2)).isGeneratedBy

end TauCeti
