/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Restricting scalars in boundaryless models

A boundaryless model can be regarded over a smaller scalar field without changing its
coordinate maps or the carrier of its charts. This operation commutes with products,
so the product comparison requires no new atlas.

The construction uses Mathlib's `ModelWithCorners.ofTargetUniv`; no scalar structure is
replaced on the model vector space.

For the underlying real model of a complex manifold, see Huybrechts, *Complex Geometry*,
Chapter 1, and Kobayashi--Nomizu, *Foundations of Differential Geometry*, Volume I, Chapter I.
-/

public section

open Set
open scoped Manifold

namespace ModelWithCorners

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  {H : Type*} [TopologicalSpace H]

variable (𝕜) (I : ModelWithCorners 𝕜' E H) [I.Boundaryless]

/-- Regard a boundaryless model over another scalar field, preserving both coordinate maps
and the caller's normed-space structure. -/
def restrictScalars : ModelWithCorners 𝕜 E H :=
  ofTargetUniv 𝕜 I.toPartialEquiv I.source_eq (I.target_eq.trans I.range_eq_univ)
    I.continuous I.continuous_symm

/-- Restriction of scalars preserves the entire coordinate partial equivalence. -/
@[simp]
theorem restrictScalars_toPartialEquiv :
    (I.restrictScalars 𝕜).toPartialEquiv = I.toPartialEquiv :=
  (rfl)

@[simp, mfld_simps]
theorem coe_restrictScalars : ⇑(I.restrictScalars 𝕜) = I :=
  (rfl)

@[simp, mfld_simps]
theorem coe_restrictScalars_symm : ⇑(I.restrictScalars 𝕜).symm = I.symm :=
  (rfl)

/-- Restricting scalars does not introduce a boundary. -/
instance : (I.restrictScalars 𝕜).Boundaryless where
  range_eq_univ := by simpa using I.range_eq_univ

/-- The trivial model restricts to the trivial model for the caller's scalar action. -/
@[simp]
theorem _root_.modelWithCornersSelf_restrictScalars :
    (𝓘(𝕜', E).restrictScalars 𝕜) = 𝓘(𝕜, E) := by
  ext <;> rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners 𝕜' F H') [J.Boundaryless]

/-- Restricting scalars commutes with the ordinary product model. -/
@[simp]
theorem restrictScalars_prod :
    (I.prod J).restrictScalars 𝕜 = (I.restrictScalars 𝕜).prod (J.restrictScalars 𝕜) := by
  ext <;> rfl

end ModelWithCorners
