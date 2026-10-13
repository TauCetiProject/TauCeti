/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Atlas
public import TauCeti.Geometry.Manifold.Orientation.Prod

/-!
# Orientable manifolds with corners

Orientability means the existence of a canonical manifold orientation: a model orientation and
source-indexed locally constant chart signs modulo simultaneous reversal. This includes boundary
and corner points. An oriented atlas is a sufficient condition, rather than the definition.
The model spaces and products of orientable manifolds are orientable.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- A manifold with corners is orientable when it carries an orientation of its tangent spaces
compatible with the within-range chart Jacobians. -/
class Orientable : Prop where
  /-- A canonical manifold orientation exists. -/
  nonempty_orientation : Nonempty (Manifold.Orientation I M (Fin (Module.finrank ℝ E)))

variable {I M}

/-- An oriented atlas gives canonical orientability, including at boundary and corner points. -/
theorem IsOrientedAtlas.orientable {n : ℕ∞ω} [NeZero n]
    {A : Set (OpenPartialHomeomorph M H)} (hA : IsOrientedAtlas I n A) : Orientable I M :=
  ⟨hA.nonempty_orientation⟩

/-- A manifold whose given atlas has positive transition derivatives is canonically orientable. -/
theorem Orientable.of_hasGroupoid [HasGroupoid M (orientationPreservingGroupoid I)] :
    Orientable I M := by
  apply IsOrientedAtlas.orientable (n := 1) (A := atlas H M)
  exact ⟨IsManifold.subset_maximalAtlas,
    fun x ↦ ⟨chartAt H x, chart_mem_atlas H x, mem_chart_source H x⟩,
    fun he he' ↦ HasGroupoid.compatible he he'⟩

/-- Every model with corners carries its constant model orientation. -/
instance : Orientable I H :=
  ⟨⟨Manifold.Orientation.model (I := I) (Module.finBasis ℝ E).orientation
    (Fintype.card_fin _)⟩⟩

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']

/-- Products of canonically orientable manifolds with corners are orientable. -/
instance [Orientable I M] [Orientable I' M'] : Orientable (I.prod I') (M × M') := by
  obtain ⟨o⟩ := Orientable.nonempty_orientation (I := I) (M := M)
  obtain ⟨o'⟩ := Orientable.nonempty_orientation (I := I') (M := M')
  obtain ⟨l, rfl⟩ := o.exists_lift
  obtain ⟨l', rfl⟩ := o'.exists_lift
  exact ⟨l.nonempty_orientation_prod l'⟩

end TauCeti
