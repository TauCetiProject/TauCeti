/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finitely generated modules

This file provides general results about Mathlib's category of finitely generated modules.
Additivity of finite-free rank on biproducts makes dimension a split-additive invariant, which
feeds the Grothendieck-group computation for finite-dimensional vector spaces.

## Main results

* `FGModuleCat.hom_hom_ofHom`: the linear map underlying `FGModuleCat.ofHom f` is `f`, the
  analogue of Mathlib's `ModuleCat.hom_ofHom`.
* `FGModuleCat.finrank_biprod`: rank is additive on biproducts of finite free modules.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

/-- The linear map underlying `FGModuleCat.ofHom f` is `f`. -/
@[simp]
theorem _root_.FGModuleCat.hom_hom_ofHom {R : Type u} [Ring R] {V W : Type v} [AddCommGroup V]
    [Module R V] [Module.Finite R V] [AddCommGroup W] [Module R W] [Module.Finite R W]
    (f : V →ₗ[R] W) : (FGModuleCat.ofHom f).hom.hom = f :=
  (rfl)

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

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
