/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finitely generated modules

This file provides general results about Mathlib's category of finitely generated modules.
Additivity of finite-free rank on biproducts makes dimension a split-additive invariant, which
feeds the Grothendieck-group computation for finite-dimensional vector spaces.

## Main results

* `FGModuleCat.finrank_biprod`: rank is additive on biproducts of finite free modules.
* `FGModuleCat.projective_biprod`: finite projective modules are closed under biproducts.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- A biproduct of finitely generated projective modules is projective. -/
theorem _root_.FGModuleCat.projective_biprod (R : Type u) [Ring R] [Small.{v} R]
    (X Y : FGModuleCat.{v} R) [Module.Projective R X] [Module.Projective R Y] :
    Module.Projective R ((X ⊞ Y : FGModuleCat.{v} R) : Type v) := by
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  let _ : PreservesBinaryBiproduct X Y F :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct F
  have hX : Module.Projective R (F.obj X) := by exact ‹Module.Projective R X›
  have hY : Module.Projective R (F.obj Y) := by exact ‹Module.Projective R Y›
  let : Module.Projective R (F.obj X) := hX
  let : Module.Projective R (F.obj Y) := hY
  let : CategoryTheory.Projective (F.obj X) :=
    ModuleCat.projective_of_categoryTheory_projective (F.obj X)
  let : CategoryTheory.Projective (F.obj Y) :=
    ModuleCat.projective_of_categoryTheory_projective (F.obj Y)
  have h : CategoryTheory.Projective (F.obj (X ⊞ Y)) :=
    CategoryTheory.Projective.of_iso ((F.mapBiprod X Y).symm) inferInstance
  let : CategoryTheory.Projective (F.obj (X ⊞ Y)) := h
  exact ModuleCat.projective_of_module_projective (F.obj (X ⊞ Y))

/-- The rank of a biproduct of finite free modules is the sum of their ranks. -/
@[simp]
theorem _root_.FGModuleCat.finrank_biprod (R : Type u) [Ring R] [StrongRankCondition R]
    (X Y : FGModuleCat.{v} R) [Module.Free R X] [Module.Free R Y] :
    Module.finrank R ((X ⊞ Y : FGModuleCat.{v} R) : Type v) =
      Module.finrank R X + Module.finrank R Y := by
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  let _ : PreservesBinaryBiproduct X Y F :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct F
  let e : F.obj (X ⊞ Y) ≅ ModuleCat.of R (X × Y) :=
    F.mapBiprod X Y ≪≫ ModuleCat.biprodIsoProd X.obj Y.obj
  let e' : (X ⊞ Y : FGModuleCat.{v} R) ≅ FGModuleCat.of R (X × Y) := F.preimageIso e
  exact (FGModuleCat.isoToLinearEquiv e').finrank_eq.trans Module.finrank_prod

end TauCeti
