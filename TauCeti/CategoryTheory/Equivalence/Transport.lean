/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Equivalence.Classes
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# Transport of autoequivalence actions

An equivalence `e : C ≌ D` transports a self-equivalence `F` of `C` to
`e.symm.trans (F.trans e)`. On natural-isomorphism classes this is a group
isomorphism, with functional composition as multiplication. Consequently any group
action by autoequivalence classes transports along a supplied equivalence.

`Equivalence.autoequivalenceClassCongr_eq_iff` characterizes this transport by natural
intertwining isomorphisms of the representing functors.

The construction uses Mathlib's `Equivalence.congrLeft`, `Equivalence.congrRight`
and `Equivalence.skeletonIsoCat.objEquiv` on endofunctors, then `Units.mapEquiv` on their
invertible classes. It applies in particular to braid actions on equivalent
homotopy or derived categories; no choice of a Morita equivalence is implicit.

For `ρ : H →* AutoequivalenceClass C`, the transported action is
`e.autoequivalenceClassCongr.toMonoidHom.comp ρ`. Mathlib's
`MulEquiv.monoidHomCongrRightEquiv` packages this as an equivalence on actions.
-/

public section
noncomputable section

namespace CategoryTheory

open TauCeti

universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

attribute [local instance] endofunctorMonoidalCategory

/-- Conjugation along a category equivalence identifies the monoids of
natural-isomorphism classes of endofunctors. -/
def Equivalence.endofunctorClassCongr (e : C ≌ D) :
    Skeleton (C ⥤ C) ≃* Skeleton (D ⥤ D) where
  toEquiv := (e.congrLeft.trans e.congrRight).skeletonIsoCat.objEquiv
  map_mul' x y := by
    have h (F : C ⥤ C) :
        (e.congrLeft.trans e.congrRight).skeletonIsoCat.objEquiv (toSkeleton F) =
          toSkeleton ((e.inverse ⋙ F) ⋙ e.functor) :=
      (e.congrLeft.trans e.congrRight).functor.mapSkeleton_obj_toSkeleton F
    induction x using Quotient.inductionOn with | h F =>
    induction y using Quotient.inductionOn with | h G =>
    -- Quotient induction exposes the underlying quotient; restore the skeleton's monoid type.
    change (e.congrLeft.trans e.congrRight).skeletonIsoCat.objEquiv (toSkeleton F * toSkeleton G) =
      (e.congrLeft.trans e.congrRight).skeletonIsoCat.objEquiv (toSkeleton F) *
        (e.congrLeft.trans e.congrRight).skeletonIsoCat.objEquiv (toSkeleton G)
    rw [← Skeleton.toSkeleton_tensorObj, h, h, h, ← Skeleton.toSkeleton_tensorObj]
    -- Endofunctor tensor is composition; make it explicit before checking naturality.
    change toSkeleton ((e.inverse ⋙ (F ⋙ G)) ⋙ e.functor) =
      toSkeleton (((e.inverse ⋙ F) ⋙ e.functor) ⋙ ((e.inverse ⋙ G) ⋙ e.functor))
    exact congr_toSkeleton_of_iso (NatIso.ofComponents
      (fun X ↦ e.functor.mapIso (G.mapIso (e.unitIso.app (F.obj (e.inverse.obj X)))))
      (by
        intro X Y f
        simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.mapIso_hom,
          ← CategoryTheory.Functor.map_comp]
        exact congrArg (fun f ↦ e.functor.map (G.map f))
          (e.unitIso.hom.naturality (F.map (e.inverse.map f)))))

/-- Transport of an endofunctor class is represented by its conjugate functor. -/
@[simp]
theorem Equivalence.endofunctorClassCongr_toSkeleton (e : C ≌ D) (F : C ⥤ C) :
    e.endofunctorClassCongr (toSkeleton F) =
      toSkeleton ((e.inverse ⋙ F) ⋙ e.functor) :=
  (e.congrLeft.trans e.congrRight).functor.mapSkeleton_obj_toSkeleton F

/-- Transport along the identity equivalence fixes every endofunctor class. -/
@[simp]
theorem Equivalence.endofunctorClassCongr_refl :
    (Equivalence.refl (C := C)).endofunctorClassCongr = MulEquiv.refl _ := by
  ext x
  induction x using Quotient.inductionOn with | h F =>
  rw [Equivalence.endofunctorClassCongr_toSkeleton]
  exact congr_toSkeleton_of_iso
    (CategoryTheory.Functor.isoWhiskerRight F.leftUnitor (𝟭 C) ≪≫ F.rightUnitor)

/-- Successive equivalences transport endofunctor classes successively. -/
theorem Equivalence.endofunctorClassCongr_trans (e : C ≌ D) (f : D ≌ E) :
    (e.trans f).endofunctorClassCongr =
      e.endofunctorClassCongr.trans f.endofunctorClassCongr := by
  ext x
  induction x using Quotient.inductionOn with | h F =>
  -- Restore the skeleton type after quotient induction, before using the class formulas.
  change (e.trans f).endofunctorClassCongr (toSkeleton F) =
    f.endofunctorClassCongr (e.endofunctorClassCongr (toSkeleton F))
  simp only [Equivalence.endofunctorClassCongr_toSkeleton,
    Equivalence.trans_functor, Equivalence.trans_inverse]
  exact congr_toSkeleton_of_iso
    (CategoryTheory.Functor.isoWhiskerRight
      (CategoryTheory.Functor.associator f.inverse e.inverse F)
        (e.functor ⋙ f.functor) ≪≫
      (CategoryTheory.Functor.associator (f.inverse ⋙ (e.inverse ⋙ F)) e.functor f.functor).symm ≪≫
      CategoryTheory.Functor.isoWhiskerRight
        (CategoryTheory.Functor.associator f.inverse (e.inverse ⋙ F) e.functor)
        f.functor)

/-- Reversing the supplied equivalence reverses transport of endofunctor classes. -/
theorem Equivalence.endofunctorClassCongr_symm (e : C ≌ D) :
    e.symm.endofunctorClassCongr = e.endofunctorClassCongr.symm := by
  ext x
  apply e.endofunctorClassCongr.injective
  rw [MulEquiv.apply_symm_apply]
  induction x using Quotient.inductionOn with | h F =>
  simp only [Equivalence.endofunctorClassCongr_toSkeleton]
  exact congr_toSkeleton_of_iso (NatIso.ofComponents
    (fun X ↦ e.counitIso.app (F.obj (e.functor.obj (e.inverse.obj X))) ≪≫
      F.mapIso (e.counitIso.app X))
    (by
      intro X Y f
      simp only [Equivalence.symm_functor, Equivalence.symm_inverse, Iso.trans_hom,
        CategoryTheory.Functor.comp_map, CategoryTheory.Functor.mapIso_hom, Category.assoc]
      erw [e.counitIso.hom.naturality_assoc]
      simp only [CategoryTheory.Functor.id_map]
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
      rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
      erw [e.counitIso.hom.naturality]
      rfl))

/-- Conjugation along an equivalence gives an isomorphism of groups of
autoequivalence classes, in functional composition order. -/
def Equivalence.autoequivalenceClassCongr (e : C ≌ D) :
    AutoequivalenceClass C ≃* AutoequivalenceClass D :=
  (Units.mapEquiv (e.endofunctorClassCongr)).op

/-- The underlying endofunctor class of a transported unit is its transported
endofunctor class. -/
@[simp]
theorem Equivalence.autoequivalenceClassCongr_val (e : C ≌ D)
    (x : AutoequivalenceClass C) :
    (e.autoequivalenceClassCongr x).unop.val =
      e.endofunctorClassCongr x.unop.val := by
  -- Units.mapEquiv and the opposite equivalence compute on the underlying value.
  rfl

/-- Transport sends an explicit self-equivalence to its conjugate. -/
@[simp]
theorem Equivalence.autoequivalenceClassCongr_toAutoequivalenceClass
    (e : C ≌ D) (F : C ≌ C) :
    e.autoequivalenceClassCongr F.toAutoequivalenceClass =
      ((e.symm.trans F).trans e).toAutoequivalenceClass := by
  apply MulOpposite.unop_injective
  apply Units.ext
  rw [Equivalence.autoequivalenceClassCongr_val,
    Equivalence.toAutoequivalenceClass_val, Equivalence.toAutoequivalenceClass_val,
    Equivalence.endofunctorClassCongr_toSkeleton]
  simp only [Equivalence.trans_functor, Equivalence.symm_functor]

/-- Transport along the identity equivalence fixes every autoequivalence class. -/
@[simp]
theorem Equivalence.autoequivalenceClassCongr_refl :
    (Equivalence.refl (C := C)).autoequivalenceClassCongr = MulEquiv.refl _ := by
  ext x
  apply MulOpposite.unop_injective
  apply Units.ext
  simp only [Equivalence.autoequivalenceClassCongr_val,
    Equivalence.endofunctorClassCongr_refl, MulEquiv.refl_apply]

/-- Transport of autoequivalence classes is compatible with composition of
the supplied equivalences. -/
theorem Equivalence.autoequivalenceClassCongr_trans (e : C ≌ D) (f : D ≌ E) :
    (e.trans f).autoequivalenceClassCongr =
      e.autoequivalenceClassCongr.trans f.autoequivalenceClassCongr := by
  ext x
  apply MulOpposite.unop_injective
  apply Units.ext
  simp only [Equivalence.autoequivalenceClassCongr_val, MulEquiv.trans_apply,
    Equivalence.endofunctorClassCongr_trans]

/-- Reversing the supplied equivalence reverses transport of autoequivalence classes. -/
theorem Equivalence.autoequivalenceClassCongr_symm (e : C ≌ D) :
    e.symm.autoequivalenceClassCongr = e.autoequivalenceClassCongr.symm := by
  simp only [Equivalence.autoequivalenceClassCongr,
    Equivalence.endofunctorClassCongr_symm, ← Units.mapEquiv_symm]
  -- Taking MulEquiv.op commutes definitionally with MulEquiv.symm.
  rfl

/-- The endofunctor transported across an equivalence intertwines with the original
endofunctor across that equivalence. -/
def Equivalence.transportedEndofunctorIso (e : C ≌ D) (F : C ⥤ C) :
    e.functor ⋙ ((e.inverse ⋙ F) ⋙ e.functor) ≅ F ⋙ e.functor :=
  (CategoryTheory.Functor.associator e.functor (e.inverse ⋙ F) e.functor).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight (e.funInvIdAssoc F) e.functor

/-- The intertwiner is induced by the inverse of the equivalence's unit. -/
@[simp]
theorem Equivalence.transportedEndofunctorIso_hom_app
    (e : C ≌ D) (F : C ⥤ C) (X : C) :
    (e.transportedEndofunctorIso F).hom.app X =
      e.functor.map (F.map (e.unitIso.inv.app X)) := by
  simp [Equivalence.transportedEndofunctorIso]

/-- The inverse intertwiner is induced by the equivalence's unit. -/
@[simp]
theorem Equivalence.transportedEndofunctorIso_inv_app
    (e : C ≌ D) (F : C ⥤ C) (X : C) :
    (e.transportedEndofunctorIso F).inv.app X =
      e.functor.map (F.map (e.unitIso.hom.app X)) := by
  simp [Equivalence.transportedEndofunctorIso]

/-- A self-equivalence represents the transported class precisely when the supplied
equivalence intertwines its functor with the original functor. -/
theorem Equivalence.autoequivalenceClassCongr_eq_iff (e : C ≌ D)
    (F : C ≌ C) (F' : D ≌ D) :
    e.autoequivalenceClassCongr F.toAutoequivalenceClass = F'.toAutoequivalenceClass ↔
      Nonempty (e.functor ⋙ F'.functor ≅ F.functor ⋙ e.functor) := by
  rw [Equivalence.autoequivalenceClassCongr_toAutoequivalenceClass,
    Equivalence.toAutoequivalenceClass_eq_iff]
  constructor
  · rintro ⟨h⟩
    exact ⟨(CategoryTheory.Functor.isoWhiskerLeft e.functor h).symm ≪≫
      e.transportedEndofunctorIso F.functor⟩
  · rintro ⟨h⟩
    exact ⟨(e.symm.congrLeft (E := D)).functor.preimageIso
      (e.transportedEndofunctorIso F.functor ≪≫ h.symm)⟩

end CategoryTheory
