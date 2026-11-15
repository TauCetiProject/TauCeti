/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Point.Comap

/-!
# Stalks of sheaf pullbacks along points with isomorphic fiber functors

Mathlib's `CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso` identifies the stalk
`(Φ.comap F hF).sheafFiber` of a pulled-back point with `F.sheafPullback A J K ⋙ Φ.sheafFiber`.
In geometric situations (for instance, geometric points of the small étale site under base change
of schemes), the composite `F ⋙ Φ.fiber` is not definitionally equal to the fiber functor of the
expected point `Ψ` on `(C, J)`, but only naturally isomorphic to it.

This file provides:
* `CategoryTheory.NatIso.mapElementsEquiv` and `CategoryTheory.initiallySmall_elements_of_iso`:
  equivalence of categories of elements and invariance of `InitiallySmall` under natural
  isomorphisms of functors to types;
* `CategoryTheory.GrothendieckTopology.Point.isoMk`,
  `CategoryTheory.GrothendieckTopology.Point.presheafFiberIsoOfFiberIso`, and
  `CategoryTheory.GrothendieckTopology.Point.sheafFiberIsoOfFiberIso`: isomorphisms of points and
  of their presheaf/sheaf fiber functors from natural isomorphisms of fiber functors;
* `CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIsoOfFiberIso`: the stalk comparison
  `F.sheafPullback A J K ⋙ Φ.sheafFiber ≅ Ψ.sheafFiber` induced by a natural isomorphism
  `F ⋙ Φ.fiber ≅ Ψ.fiber`.
-/

public section

universe w w' v v' u u'

namespace CategoryTheory

open Limits Opposite

/-- A natural isomorphism of functors to types induces an equivalence between their categories of
elements. -/
def NatIso.mapElementsEquiv {C : Type*} [Category* C] {F G : C ⥤ Type w} (e : F ≅ G) :
    F.Elements ≌ G.Elements where
  functor := e.hom.mapElements
  inverse := e.inv.mapElements
  unitIso := NatIso.ofComponents fun x ↦ Functor.Elements.isoMk (Iso.refl x.obj) (by simp)
  counitIso := NatIso.ofComponents fun x ↦ Functor.Elements.isoMk (Iso.refl x.obj) (by simp)

@[simp]
lemma NatIso.mapElementsEquiv_functor {C : Type*} [Category* C] {F G : C ⥤ Type w} (e : F ≅ G) :
    (NatIso.mapElementsEquiv e).functor = e.hom.mapElements :=
  (rfl)

@[simp]
lemma NatIso.mapElementsEquiv_inverse {C : Type*} [Category* C] {F G : C ⥤ Type w} (e : F ≅ G) :
    (NatIso.mapElementsEquiv e).inverse = e.inv.mapElements :=
  (rfl)

/-- An isomorphism of functors to types transports `InitiallySmall` across their categories of
elements. -/
lemma initiallySmall_elements_of_iso {C : Type*} [Category* C]
    {F G : C ⥤ Type w} (e : F ≅ G) [InitiallySmall.{w'} G.Elements] :
    InitiallySmall.{w'} F.Elements :=
  initiallySmall_of_initial_of_initiallySmall (NatIso.mapElementsEquiv e).inverse

namespace GrothendieckTopology.Point

section FiberIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Constructor for isomorphisms in `Point.{w} J` from a natural isomorphism of fiber functors in
the contravariant direction. -/
def isoMk {Φ₁ Φ₂ : Point.{w} J} (e : Φ₂.fiber ≅ Φ₁.fiber) : Φ₁ ≅ Φ₂ where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩

@[simp]
lemma isoMk_hom {Φ₁ Φ₂ : Point.{w} J} (e : Φ₂.fiber ≅ Φ₁.fiber) :
    (isoMk e).hom = ⟨e.hom⟩ :=
  (rfl)

@[simp]
lemma isoMk_inv {Φ₁ Φ₂ : Point.{w} J} (e : Φ₂.fiber ≅ Φ₁.fiber) :
    (isoMk e).inv = ⟨e.inv⟩ :=
  (rfl)

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- Natural isomorphism between presheaf fiber functors induced by a natural isomorphism between
the fiber functors of two points. -/
noncomputable def presheafFiberIsoOfFiberIso {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) :
    Φ₁.presheafFiber (A := A) ≅ Φ₂.presheafFiber where
  hom := (Hom.mk e.hom).presheafFiber
  inv := (Hom.mk e.inv).presheafFiber
  hom_inv_id := by
    rw [← Hom.presheafFiber_comp (Hom.mk e.inv) (Hom.mk e.hom), ← Hom.presheafFiber_id]
    congr 1
    ext : 1
    exact e.hom_inv_id
  inv_hom_id := by
    rw [← Hom.presheafFiber_comp (Hom.mk e.hom) (Hom.mk e.inv), ← Hom.presheafFiber_id]
    congr 1
    ext : 1
    exact e.inv_hom_id

@[simp]
lemma presheafFiberIsoOfFiberIso_hom {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁.fiber ≅ Φ₂.fiber) :
    (presheafFiberIsoOfFiberIso (A := A) e).hom = (Hom.mk e.hom).presheafFiber :=
  (rfl)

@[simp]
lemma presheafFiberIsoOfFiberIso_inv {Φ₁ Φ₂ : Point.{w} J} (e : Φ₁.fiber ≅ Φ₂.fiber) :
    (presheafFiberIsoOfFiberIso (A := A) e).inv = (Hom.mk e.inv).presheafFiber :=
  (rfl)

@[reassoc]
lemma toPresheafFiber_presheafFiberIsoOfFiberIso_hom_app {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) (X : C) (x : Φ₁.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    Φ₁.toPresheafFiber X x P ≫ (presheafFiberIsoOfFiberIso (A := A) e).hom.app P =
      Φ₂.toPresheafFiber X (e.hom.app X x) P := by
  simp

@[reassoc]
lemma toPresheafFiber_presheafFiberIsoOfFiberIso_inv_app {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) (X : C) (x : Φ₂.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    Φ₂.toPresheafFiber X x P ≫ (presheafFiberIsoOfFiberIso (A := A) e).inv.app P =
      Φ₁.toPresheafFiber X (e.inv.app X x) P := by
  simp

/-- Natural isomorphism between sheaf fiber functors induced by a natural isomorphism between the
fiber functors of two points. -/
noncomputable def sheafFiberIsoOfFiberIso {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) :
    Φ₁.sheafFiber (A := A) ≅ Φ₂.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (presheafFiberIsoOfFiberIso e)

@[simp]
lemma sheafFiberIsoOfFiberIso_hom_app {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) (F : Sheaf J A) :
    (sheafFiberIsoOfFiberIso (A := A) e).hom.app F =
      (presheafFiberIsoOfFiberIso (A := A) e).hom.app F.obj :=
  (rfl)

@[simp]
lemma sheafFiberIsoOfFiberIso_inv_app {Φ₁ Φ₂ : Point.{w} J}
    (e : Φ₁.fiber ≅ Φ₂.fiber) (F : Sheaf J A) :
    (sheafFiberIsoOfFiberIso (A := A) e).inv.app F =
      (presheafFiberIsoOfFiberIso (A := A) e).inv.app F.obj :=
  (rfl)

end FiberIso

section Comap

variable {C D : Type*} [Category* C] [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (Φ : Point.{w} K) (Ψ : Point.{w} J)
  (F : C ⥤ D) [RepresentablyFlat F] (hF : CoverPreserving J K F)
  (e : F ⋙ Φ.fiber ≅ Ψ.fiber)

/-- If `F ⋙ Φ.fiber ≅ Ψ.fiber`, then `Ψ` is isomorphic in `Point.{w} J` to `Φ.comap F hF`. -/
def comapIsoOfFiberIso :
    letI := initiallySmall_elements_of_iso e
    Ψ ≅ Φ.comap F hF :=
  letI := initiallySmall_elements_of_iso e
  isoMk e

/-- Given a representably flat, cover-preserving, continuous functor `F : C ⥤ D` between sites
`(C, J)` and `(D, K)`, points `Φ` of `(D, K)` and `Ψ` of `(C, J)`, and a natural isomorphism
`F ⋙ Φ.fiber ≅ Ψ.fiber`, the stalk at `Φ` of `F.sheafPullback A J K` identifies naturally with the
stalk at `Ψ`. -/
noncomputable def sheafFiberComapIsoOfFiberIso
    (A : Type*) [Category.{v} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    F.sheafPullback A J K ⋙ Φ.sheafFiber ≅ Ψ.sheafFiber :=
  letI := initiallySmall_elements_of_iso e
  (Φ.sheafFiberComapIso F hF A).symm ≪≫ sheafFiberIsoOfFiberIso e

end Comap

end GrothendieckTopology.Point

end CategoryTheory
