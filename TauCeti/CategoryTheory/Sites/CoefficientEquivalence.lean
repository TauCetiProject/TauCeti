/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Changing sheaf coefficients by an equivalence

An equivalence of coefficient categories induces an equivalence of sheaf categories on a
fixed site. Both directions are ordinary postcomposition: opens are unchanged and restriction
maps are the images of the original restriction maps. This transports constructions on sheaves
between equivalent coefficient models, in particular between modules over isomorphic rings.

Sheafification can also be transported when it is only known to exist for one coefficient
category. Once it exists on both sides, compatibility is supplied by Mathlib's
`sheafifyComposeIso`: the coefficient functors are left adjoints and hence preserve
sheafification. The transport follows the construction for equivalent sites in
`CategoryTheory.Equivalence.transportAndSheafify`.
-/

public section

universe v u v₁ u₁ v₂ u₂

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Equivalence

variable {C : Type u} [Category.{v} C] {A : Type u₁} [Category.{v₁} A]
  {B : Type u₂} [Category.{v₂} B]

/-- An equivalence of coefficient categories induces an equivalence of sheaf categories by
postcomposition on the same site. -/
-- Expose the coefficient functors so dependent section and restriction types elaborate.
@[expose]
noncomputable def sheafCongrRight (e : A ≌ B) (J : GrothendieckTopology C) :
    Sheaf J A ≌ Sheaf J B where
  functor := sheafCompose J e.functor
  inverse := sheafCompose J e.inverse
  unitIso := NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ (isoWhiskerLeft F.obj e.unitIso))
    (by intro F G f; ext U; exact e.unitIso.hom.naturality (f.hom.app U))
  counitIso := NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ (isoWhiskerLeft F.obj e.counitIso))
    (by intro F G f; ext U; exact e.counitIso.hom.naturality (f.hom.app U))
  functor_unitIso_comp F := by
    ext U
    exact e.functor_unitIso_comp (F.obj.obj U)

@[simp]
lemma sheafCongrRight_functor (e : A ≌ B) (J : GrothendieckTopology C) :
    (e.sheafCongrRight J).functor = sheafCompose J e.functor :=
  (rfl)

@[simp]
lemma sheafCongrRight_inverse (e : A ≌ B) (J : GrothendieckTopology C) :
    (e.sheafCongrRight J).inverse = sheafCompose J e.inverse :=
  (rfl)

/-- Change coefficients, sheafify, and change back. This is a sheafification functor for the
original coefficient category even when it has no chosen sheafification yet. -/
noncomputable def transportAndSheafifyRight (e : A ≌ B) (J : GrothendieckTopology C)
    [HasSheafify J B] : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  e.congrRight.functor ⋙ presheafToSheaf J B ⋙ (e.sheafCongrRight J).inverse

/-- Changing coefficients and changing back leaves the underlying presheaf unchanged. -/
noncomputable def sheafCongrRightForgetIso (e : A ≌ B) (J : GrothendieckTopology C) :
    (e.sheafCongrRight J).functor ⋙ sheafToPresheaf J B ⋙ e.congrRight.inverse ≅
      sheafToPresheaf J A :=
  NatIso.ofComponents (fun F ↦ isoWhiskerLeft F.obj e.unitIso.symm)
    (by intro F G f; ext U; exact e.unitIso.inv.naturality (f.hom.app U))

/-- Sheafification transported along a coefficient equivalence has the usual adjunction. -/
noncomputable def transportSheafificationAdjunctionRight (e : A ≌ B)
    (J : GrothendieckTopology C) [HasSheafify J B] :
    e.transportAndSheafifyRight J ⊣ sheafToPresheaf J A :=
  ((e.congrRight.toAdjunction.comp (sheafificationAdjunction J B)).comp
    (e.sheafCongrRight J).symm.toAdjunction).ofNatIsoRight (e.sheafCongrRightForgetIso J)

/-- Transported sheafification remains left exact. -/
noncomputable instance (e : A ≌ B) (J : GrothendieckTopology C) [HasSheafify J B] :
    Limits.PreservesFiniteLimits (e.transportAndSheafifyRight J) := by
  unfold transportAndSheafifyRight
  infer_instance

/-- Existence of left exact sheafification transports along an equivalence of coefficients. -/
theorem hasSheafify_right (e : A ≌ B) (J : GrothendieckTopology C) [HasSheafify J B] :
    HasSheafify J A :=
  HasSheafify.mk' J A (e.transportSheafificationAdjunctionRight J)

end CategoryTheory.Equivalence
