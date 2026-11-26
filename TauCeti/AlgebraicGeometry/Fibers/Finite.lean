/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Finite fibres

For a morphism of schemes `f : X ⟶ Y` and a point `y` of `Y`, this file relates finiteness of
the fibre morphism `f⁻¹(y) ⟶ Spec κ(y)` to the set-theoretic fibre `f ⁻¹' {y}`. When the fibre
morphism is finite, the scheme-theoretic fibre is Artinian, the set-theoretic fibre is finite
and discrete, and a morphism locally of finite type is quasi-finite at each point of that fibre.
For `f` locally of finite type, the fibre morphism at `y` is finite exactly when the
set-theoretic fibre is finite.

These are pointwise forms of Mathlib's
`AlgebraicGeometry.locallyQuasiFinite_iff_isFinite_fiber` and
`AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton`, which concern all fibres at
once. They are used for morphisms that are only controlled over some points of the target,
such as alterations over the generic points of their target.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isArtinianScheme_fiber_of_isFinite_fiberToSpecResidueField`:
  a fibre that is finite over the residue field of its point is an Artinian scheme.
* `AlgebraicGeometry.Scheme.Hom.isDiscrete_preimage_singleton_of_isFinite_fiberToSpecResidueField`
  and `AlgebraicGeometry.Scheme.Hom.finite_preimage_singleton_of_isFinite_fiberToSpecResidueField`:
  a finite fibre morphism has a discrete and finite set-theoretic fibre.
* `AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_of_isFinite_fiberToSpecResidueField`: a morphism
  locally of finite type is quasi-finite at each point of a fibre whose fibre morphism is finite.
* `AlgebraicGeometry.Scheme.Hom.isFinite_fiberToSpecResidueField_iff_finite_preimage_singleton`:
  for morphisms locally of finite type, the fibre morphism is finite exactly when the
  set-theoretic fibre is finite.
-/

public section

open CategoryTheory hiding IsDiscrete
open Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}}

/-- The scheme-theoretic fibre of `f` at `y` is an Artinian scheme when it is finite over
`Spec κ(y)`. -/
theorem isArtinianScheme_fiber_of_isFinite_fiberToSpecResidueField (f : X ⟶ Y) (y : Y)
    [IsFinite (f.fiberToSpecResidueField y)] : IsArtinianScheme (f.fiber y) where
  toIsLocallyArtinian := .of_locallyQuasiFinite (f.fiberToSpecResidueField y)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (f.fiberToSpecResidueField y)

/-- If the fibre morphism `f⁻¹(y) ⟶ Spec κ(y)` is finite, the fibre `f ⁻¹' {y}` is
discrete. -/
theorem isDiscrete_preimage_singleton_of_isFinite_fiberToSpecResidueField (f : X ⟶ Y) (y : Y)
    [IsFinite (f.fiberToSpecResidueField y)] : IsDiscrete (f ⁻¹' {y}) := by
  have := f.isArtinianScheme_fiber_of_isFinite_fiberToSpecResidueField y
  simpa [range_fiberι] using
    (isDiscrete_univ_iff.mpr inferInstance).image (f.fiberι y).isEmbedding.toIsInducing

/-- If the fibre morphism `f⁻¹(y) ⟶ Spec κ(y)` is finite, the fibre `f ⁻¹' {y}` is a finite
set. -/
theorem finite_preimage_singleton_of_isFinite_fiberToSpecResidueField (f : X ⟶ Y) (y : Y)
    [IsFinite (f.fiberToSpecResidueField y)] : (f ⁻¹' {y}).Finite := by
  have := f.isArtinianScheme_fiber_of_isFinite_fiberToSpecResidueField y
  simpa [range_fiberι] using Set.finite_univ.image (f.fiberι y)

/-- A morphism locally of finite type is quasi-finite at every point of a fibre that is finite
over the residue field of the target point. -/
theorem quasiFiniteAt_of_isFinite_fiberToSpecResidueField {f : X ⟶ Y} [LocallyOfFiniteType f]
    {x : X} [IsFinite (f.fiberToSpecResidueField (f x))] : f.QuasiFiniteAt x := by
  have := f.isArtinianScheme_fiber_of_isFinite_fiberToSpecResidueField (f x)
  exact quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

/-- For a morphism locally of finite type, the fibre morphism `f⁻¹(y) ⟶ Spec κ(y)` is finite
exactly when the fibre `f ⁻¹' {y}` is a finite set. -/
theorem isFinite_fiberToSpecResidueField_iff_finite_preimage_singleton (f : X ⟶ Y)
    [LocallyOfFiniteType f] (y : Y) :
    IsFinite (f.fiberToSpecResidueField y) ↔ (f ⁻¹' {y}).Finite := by
  refine ⟨fun _ ↦
    f.finite_preimage_singleton_of_isFinite_fiberToSpecResidueField y, fun h ↦ ?_⟩
  have : Finite (f.fiber y) := have := h.to_subtype; .of_equiv _ (f.fiberHomeo y).symm.toEquiv
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.of_isPullback (.of_hasPullback _ _) ‹_›
  have : LocallyQuasiFinite (f.fiberToSpecResidueField y) :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  exact .of_locallyQuasiFinite _

end AlgebraicGeometry.Scheme.Hom
