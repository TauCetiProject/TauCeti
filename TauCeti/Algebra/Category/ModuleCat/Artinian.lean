/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# Artinian modules as an object property of `ModuleCat`

This file bridges Mathlib's categorical Artinian object property
`CategoryTheory.isArtinianObject : ObjectProperty (ModuleCat R)` with `IsArtinian R M` via
`ModuleCat.subobjectModule M` (`ModuleCat.isArtinianObject_iff`) and records its closure under
quotients and finite products (supplementing Mathlib's closure under subobjects and zero objects).

As a consequence, the full subcategory
`(CategoryTheory.isArtinianObject (C := ModuleCat R)).FullSubcategory` is abelian (via
`Mathlib.CategoryTheory.Abelian.Subcategory`), and its inclusion into `ModuleCat R` preserves
finite limits and finite colimits (via `TauCeti.CategoryTheory.ObjectProperty.Kernels`).
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type v} [Ring R]

/-- A bundled `R`-module is a categorical Artinian object iff it is an Artinian `R`-module. -/
@[simp]
theorem isArtinianObject_iff (M : ModuleCat.{u} R) :
    isArtinianObject M ↔ IsArtinian R M :=
  ⟨fun h ↦ have : WellFoundedLT (Subobject M) := h
    (subobjectModule M).symm.toOrderEmbedding.wellFoundedLT,
   fun h ↦ have : WellFoundedLT (Submodule R M) := h
    (subobjectModule M).toOrderEmbedding.wellFoundedLT⟩

instance : (isArtinianObject (C := ModuleCat.{u} R)).IsClosedUnderQuotients where
  prop_of_epi f _ h :=
    have : IsArtinian R _ := (isArtinianObject_iff _).mp h
    (isArtinianObject_iff _).mpr
      (isArtinian_of_surjective _ f.hom ((ModuleCat.epi_iff_surjective f).1 inferInstance))

instance : (isArtinianObject (C := ModuleCat.{u} R)).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN ↦ by
    have : IsArtinian R M := (isArtinianObject_iff _).mp hM
    have : IsArtinian R N := (isArtinianObject_iff _).mp hN
    exact (isArtinianObject_iff _).mpr
      (isArtinian_of_linearEquiv (ModuleCat.biprodIsoProd M N).toLinearEquiv.symm)

instance : (isArtinianObject (C := ModuleCat.{u} R)).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

end ModuleCat
