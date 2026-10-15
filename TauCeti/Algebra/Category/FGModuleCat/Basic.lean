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
* `FGModuleCat.hom_hom_add`: morphisms of finitely generated modules add pointwise, the
  companion of Mathlib's `FGModuleCat.hom_hom_comp` and `FGModuleCat.hom_hom_id`.
* `FGModuleCat.biprodIsoProd`: the biproduct of two finitely generated modules is their product,
  the analogue of Mathlib's `ModuleCat.biprodIsoProd`, with its projection lemmas
  `FGModuleCat.biprodIsoProd_inv_comp_fst` and `FGModuleCat.biprodIsoProd_inv_comp_snd`.
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

/-- The linear map underlying a sum of morphisms of finitely generated modules is the sum of the
linear maps underlying them: addition of morphisms in a full subcategory of `ModuleCat R` is the
addition of the underlying linear maps. -/
@[simp]
theorem _root_.FGModuleCat.hom_hom_add {R : Type u} [Ring R] {V W : FGModuleCat.{v} R}
    (f g : V ⟶ W) : (f + g).hom.hom = f.hom.hom + g.hom.hom :=
  (rfl)

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The biproduct of two finitely generated modules is their product, the analogue of Mathlib's
`ModuleCat.biprodIsoProd`. -/
noncomputable def _root_.FGModuleCat.biprodIsoProd {R : Type u} [Ring R]
    (X Y : FGModuleCat.{v} R) : (X ⊞ Y : FGModuleCat.{v} R) ≅ FGModuleCat.of R (X × Y) :=
  letI F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  letI : PreservesBinaryBiproduct X Y F := preservesBinaryBiproduct_of_preservesBinaryCoproduct F
  F.preimageIso (F.mapBiprod X Y ≪≫ ModuleCat.biprodIsoProd X.obj Y.obj)

/-- The inverse of `FGModuleCat.biprodIsoProd` followed by the first biproduct projection is the
first product projection. -/
@[simp, elementwise]
theorem _root_.FGModuleCat.biprodIsoProd_inv_comp_fst {R : Type u} [Ring R]
    (X Y : FGModuleCat.{v} R) :
    (FGModuleCat.biprodIsoProd X Y).inv ≫ biprod.fst = FGModuleCat.ofHom (LinearMap.fst R X Y) := by
  have : PreservesBinaryBiproduct X Y (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)) :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct _
  apply (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).map_injective
  have h : ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapBiprod X Y).inv ≫
      (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).map biprod.fst = biprod.fst := by
    rw [Iso.inv_comp_eq, Functor.mapBiprod_hom, biprod.lift_fst]
  rw [Functor.map_comp, FGModuleCat.biprodIsoProd, Functor.preimageIso_inv, Functor.map_preimage,
    Iso.trans_inv, Category.assoc, h]
  -- The forgetful functor sends `X` to `X.obj` and `FGModuleCat.ofHom f` to `ModuleCat.ofHom f`
  -- definitionally, so Mathlib's projection lemma closes the goal up to that unfolding.
  exact ModuleCat.biprodIsoProd_inv_comp_fst _ _

/-- The inverse of `FGModuleCat.biprodIsoProd` followed by the second biproduct projection is the
second product projection. -/
@[simp, elementwise]
theorem _root_.FGModuleCat.biprodIsoProd_inv_comp_snd {R : Type u} [Ring R]
    (X Y : FGModuleCat.{v} R) :
    (FGModuleCat.biprodIsoProd X Y).inv ≫ biprod.snd = FGModuleCat.ofHom (LinearMap.snd R X Y) := by
  have : PreservesBinaryBiproduct X Y (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)) :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct _
  apply (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).map_injective
  have h : ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).mapBiprod X Y).inv ≫
      (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)).map biprod.snd = biprod.snd := by
    rw [Iso.inv_comp_eq, Functor.mapBiprod_hom, biprod.lift_snd]
  rw [Functor.map_comp, FGModuleCat.biprodIsoProd, Functor.preimageIso_inv, Functor.map_preimage,
    Iso.trans_inv, Category.assoc, h]
  -- As for `biprodIsoProd_inv_comp_fst`.
  exact ModuleCat.biprodIsoProd_inv_comp_snd _ _

/-- The rank of a biproduct of finite free modules is the sum of their ranks. -/
@[simp]
theorem _root_.FGModuleCat.finrank_biprod (R : Type u) [Ring R] [StrongRankCondition R]
    (X Y : FGModuleCat.{v} R) [Module.Free R X] [Module.Free R Y] :
    Module.finrank R ((X ⊞ Y : FGModuleCat.{v} R) : Type v) =
      Module.finrank R X + Module.finrank R Y :=
  (FGModuleCat.isoToLinearEquiv (FGModuleCat.biprodIsoProd X Y)).finrank_eq.trans
    Module.finrank_prod

end TauCeti
