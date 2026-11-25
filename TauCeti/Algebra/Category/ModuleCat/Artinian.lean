/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Artinian modules as an object property of `ModuleCat`

This file packages Artinian modules over a ring `R` as the object property
`ModuleCat.isArtinian R : ObjectProperty (ModuleCat R)` and records its closure under subobjects,
quotients, zero objects, and finite products.

As a consequence, the full subcategory `(ModuleCat.isArtinian R).FullSubcategory` is abelian
(via `Mathlib.CategoryTheory.Abelian.Subcategory`), and its inclusion into `ModuleCat R` preserves
finite limits and finite colimits (via `TauCeti.CategoryTheory.ObjectProperty.Kernels`).
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type v} [Ring R]

variable (R) in
/-- The Artinian modules, as a property of objects of `ModuleCat R`. -/
def isArtinian : ObjectProperty (ModuleCat.{u} R) := fun M ↦ IsArtinian R M

@[simp]
theorem isArtinian_iff (M : ModuleCat.{u} R) : isArtinian R M ↔ IsArtinian R M :=
  Iff.rfl

instance : (isArtinian.{u} R).IsClosedUnderSubobjects where
  prop_of_mono f _ h :=
    have : IsArtinian R _ := h
    (isArtinian_iff _).mpr
      (isArtinian_of_injective f.hom ((ModuleCat.mono_iff_injective f).1 inferInstance))

instance : (isArtinian.{u} R).IsClosedUnderQuotients where
  prop_of_epi f _ h :=
    have : IsArtinian R _ := h
    (isArtinian_iff _).mpr
      (isArtinian_of_surjective _ f.hom ((ModuleCat.epi_iff_surjective f).1 inferInstance))

instance : (isArtinian.{u} R).ContainsZero where
  exists_zero :=
    ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _, (isArtinian_iff _).mpr inferInstance⟩

instance : (isArtinian.{u} R).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun M N hM hN ↦ by
    have : IsArtinian R M := hM
    have : IsArtinian R N := hN
    exact (isArtinian_iff _).mpr
      (isArtinian_of_linearEquiv (ModuleCat.biprodIsoProd M N).toLinearEquiv.symm)

instance : (isArtinian.{u} R).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

end ModuleCat
