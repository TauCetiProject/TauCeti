/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Transporting generating sections

This file provides a general transport for generating sections: first carry them along a
colimit-preserving functor, then read them through an isomorphism of the resulting sheaf. The
transport preserves the indexing type, invertibility of the generating morphism, and finiteness.

## Main declarations

* `SheafOfModules.GeneratingSections.equivOfIso_apply_π`: the generating morphism after
  transport along an isomorphism;
* `SheafOfModules.GeneratingSections.mapIso`: generating sections carried along a
  colimit-preserving functor and read through an isomorphism.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u v₁ v₂ u₁ u₂

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

section EquivOfIso

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

/-- Transporting generating sections along an isomorphism preserves their index type. -/
@[simp]
theorem _root_.SheafOfModules.GeneratingSections.equivOfIso_apply_I (e : M ≅ N)
    (σ : M.GeneratingSections) : (GeneratingSections.equivOfIso e σ).I = σ.I :=
  rfl

/-- Transporting generating sections along an isomorphism `e` composes the generating morphism
with `e`. -/
@[simp]
theorem _root_.SheafOfModules.GeneratingSections.equivOfIso_apply_π (e : M ≅ N)
    (σ : M.GeneratingSections) : (GeneratingSections.equivOfIso e σ).π = σ.π ≫ e.hom :=
  GeneratingSections.ofEpi_π _ _

/-- Transporting generating sections along an isomorphism preserves an invertible generating
morphism. -/
instance _root_.SheafOfModules.GeneratingSections.isIso_equivOfIso_π (e : M ≅ N)
    (σ : M.GeneratingSections) [hσ : IsIso σ.π] : IsIso (GeneratingSections.equivOfIso e σ).π := by
  rw [GeneratingSections.equivOfIso_apply_π]
  exact IsIso.comp_isIso' hσ inferInstance

/-- Transporting generating sections along an isomorphism preserves finiteness. -/
instance _root_.SheafOfModules.GeneratingSections.isFiniteType_equivOfIso (e : M ≅ N)
    (σ : M.GeneratingSections) [hσ : σ.IsFiniteType] :
    (GeneratingSections.equivOfIso e σ).IsFiniteType where
  finite := by
    rw [GeneratingSections.equivOfIso_apply_I]
    exact hσ.finite

end EquivOfIso

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R} {N : SheafOfModules.{u} S} (σ : M.GeneratingSections)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
  (η : unit S ≅ F.obj (unit R)) (e : F.obj M ≅ N)

/-- Generating sections carried along a colimit-preserving functor `F` and then read through an
isomorphism `e : F.obj M ≅ N`. -/
noncomputable def _root_.SheafOfModules.GeneratingSections.mapIso : N.GeneratingSections :=
  GeneratingSections.equivOfIso e (σ.map F η)

/-- Carrying generating sections along a functor and an isomorphism preserves their index type. -/
@[simp]
theorem _root_.SheafOfModules.GeneratingSections.mapIso_I : (σ.mapIso F η e).I = σ.I :=
  (rfl)

/-- The generating morphism of carried generating sections is the mapped generating morphism
followed by the isomorphism. -/
@[simp]
theorem _root_.SheafOfModules.GeneratingSections.mapIso_π :
    cast (by rw [GeneratingSections.mapIso_I]) (σ.mapIso F η e).π =
      ((mapFreeIso F σ.I η).hom ≫ F.map σ.π) ≫ e.hom :=
  (by
    simp only [GeneratingSections.mapIso, GeneratingSections.equivOfIso_apply_π,
      GeneratingSections.map_π_eq]
    -- The two sides differ only in the `PreservesColimitsOfSize` instance recorded by `mapFreeIso`.
    rfl)

/-- Carrying generating sections along a functor and an isomorphism preserves an invertible
generating morphism. -/
instance _root_.SheafOfModules.GeneratingSections.isIso_mapIso_π [IsIso σ.π] :
    IsIso (σ.mapIso F η e).π :=
  (GeneratingSections.isIso_equivOfIso_π _ _)

/-- Carrying generating sections along a functor and an isomorphism preserves finiteness. -/
instance _root_.SheafOfModules.GeneratingSections.isFiniteType_mapIso [hσ : σ.IsFiniteType] :
    (σ.mapIso F η e).IsFiniteType :=
  (GeneratingSections.isFiniteType_equivOfIso _ _)

end SheafOfModules

end

end TauCeti
