/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic

/-!
# Intrinsic normal spaces in tangent coordinates

The intrinsic normal space of an embedding is the quotient of the ambient tangent space
by the image of its differential. In tangent-bundle trivializations this becomes the
quotient of the ambient model space by the range of `inTangentCoordinates` of the differential.
The identification is a continuous linear equivalence and carries ambient tangent classes
to their coordinate classes. Its forward and inverse maps are computed on representatives.

The coordinate differential has a continuous left inverse on the chart overlap. Thus it
is a split-injective operator family, to which local fixed-complement constructions can
be applied when assembling normal-bundle trivializations. No metric, finite-dimensionality,
or choice of a normal complement is needed for these identifications.

The construction uses Mathlib's `ContinuousLinearMap.inCoordinates_eq` and the quotient
transport `ContinuousLinearEquiv.quotientEquiv`.
Reference: M. Hirsch, *Differential Topology*, Chapter 4, §5 (normal bundles).
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {n : ℕ∞ω}

/-- Ambient tangent coordinates send the intrinsic tangent range onto the range of the
coordinate differential. The source coordinate change does not affect that range. -/
theorem map_tangentRange_inTangentCoordinates (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) {x₀ x : M} (hx : x ∈ (chartAt H x₀).source)
    (hy : f x ∈ (chartAt G (f x₀)).source) :
    (f.tangentRange x hn).map
      ((trivializationAt F (TangentSpace J) (f x₀)).continuousLinearEquivAt 𝕜 (f x)
        (by simpa using hy)).toLinearMap =
      (inTangentCoordinates I J _root_.id (f : M → N) (mfderiv I J (f : M → N)) x₀ x).range := by
  rw [inTangentCoordinates,
    ContinuousLinearMap.inCoordinates_eq (by simpa using hx) (by simpa using hy)]
  -- Pass from operator composition to the linear range, then remove the surjective
  -- source-coordinate equivalence.
  rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp]
  congr 1
  symm
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
    (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt 𝕜 x
      (by simpa using hx)).symm.surjective))

/-- The intrinsic normal fibre is the quotient of the ambient model by the coordinate
differential's range on the overlap of the chosen source and target charts. -/
def normalSpaceEquivInTangentCoordinates (f : SmoothEmbedding I J n M N)
    (hn : n ≠ 0) {x₀ x : M} (hx : x ∈ (chartAt H x₀).source)
    (hy : f x ∈ (chartAt G (f x₀)).source) :
    f.NormalSpace x hn ≃L[𝕜]
      (F ⧸ (inTangentCoordinates I J _root_.id (f : M → N) (mfderiv I J (f : M → N)) x₀ x).range) :=
  ((trivializationAt F (TangentSpace J) (f x₀)).continuousLinearEquivAt 𝕜 (f x)
    (by simpa using hy)).quotientEquiv _ _
      (f.map_tangentRange_inTangentCoordinates hn hx hy)

/-- Normal coordinates send an ambient tangent class to its tangent-chart class. -/
@[simp]
theorem normalSpaceEquivInTangentCoordinates_normalClass
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) (hy : f x ∈ (chartAt G (f x₀)).source)
    (v : TangentSpace J (f x)) :
    f.normalSpaceEquivInTangentCoordinates hn hx hy (f.normalClass x hn v) =
      Submodule.Quotient.mk
        ((trivializationAt F (TangentSpace J) (f x₀)) ⟨f x, v⟩).2 := by
  -- The intrinsic fibre's instances wrap the quotient instances; `erw` lets the
  -- quotient computation rules match across these wrappers.
  erw [normalSpaceEquivInTangentCoordinates, normalClass_def, Submodule.mkQ_apply,
    ContinuousLinearEquiv.quotientEquiv_mk]
  rfl

/-- The inverse normal-coordinate map takes the class of a model vector to the class of
the corresponding ambient tangent vector. -/
@[simp]
theorem normalSpaceEquivInTangentCoordinates_symm_mk
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) (hy : f x ∈ (chartAt G (f x₀)).source) (v : F) :
    (f.normalSpaceEquivInTangentCoordinates hn hx hy).symm (Submodule.Quotient.mk v) =
      f.normalClass x hn ((trivializationAt F (TangentSpace J) (f x₀)).symm (f x) v) := by
  rw [← Trivialization.continuousLinearEquivAt_symm_apply 𝕜 _ _ (by simpa using hy)]
  apply (f.normalSpaceEquivInTangentCoordinates hn hx hy).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply,
    normalSpaceEquivInTangentCoordinates_normalClass]
  exact congrArg Submodule.Quotient.mk
    (((trivializationAt F (TangentSpace J) (f x₀)).continuousLinearEquivAt 𝕜 (f x)
      (by simpa using hy)).apply_symm_apply v).symm

end TauCeti.SmoothEmbedding
