/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Point.Comap

/-!
# Isomorphisms of points and fibres of pullback sheaves

For points `Φ₁, Φ₂` of a site `(C, J)`, a natural isomorphism `Φ₂.fiber ≅ Φ₁.fiber` of their fibre
functors gives an isomorphism `Φ₁ ≅ Φ₂` in `Point J` (`Point.isoMk`), which induces natural
isomorphisms of presheaf and sheaf fibre functors (`Point.presheafFiberIso`, `Point.sheafFiberIso`).

Combining this with `Point.comap` and `Point.sheafFiberComapIso`: if `F : C ⥤ D` is a continuous,
representably flat, cover-preserving functor between sites `(C, J)` and `(D, K)`, `Φ` is a point of
`(D, K)`, and `Ψ` is a point of `(C, J)` equipped with a natural isomorphism `F ⋙ Φ.fiber ≅
Ψ.fiber`, then `(F ⋙ Φ.fiber).Elements` inherits initial smallness from `Ψ`, `Φ.comap F hF ≅ Ψ`,
and the stalk of a pullback sheaf `F^* G` at `Φ` identifies naturally with the stalk of `G` at `Ψ`
(`Point.sheafPullbackCompSheafFiberIso`).

## References

* A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IV, §3.2 and §6.2.
-/

public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.GrothendieckTopology.Point

section Iso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {Φ₁ Φ₂ : Point.{w} J}

/-- Construct an isomorphism `Φ₁ ≅ Φ₂` of points of `J` from a natural isomorphism
`Φ₂.fiber ≅ Φ₁.fiber` of their fibre functors. -/
def isoMk (e : Φ₂.fiber ≅ Φ₁.fiber) : Φ₁ ≅ Φ₂ where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩

@[simp]
lemma isoMk_hom_hom (e : Φ₂.fiber ≅ Φ₁.fiber) :
    (isoMk e).hom.hom = e.hom :=
  (rfl)

@[simp]
lemma isoMk_inv_hom (e : Φ₂.fiber ≅ Φ₁.fiber) :
    (isoMk e).inv.hom = e.inv :=
  (rfl)

/-- An isomorphism `Φ₁ ≅ Φ₂` of points induces a natural isomorphism of presheaf fibre functors. -/
noncomputable def presheafFiberIso (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A]
    [HasColimitsOfSize.{w, w} A] :
    Φ₁.presheafFiber (A := A) ≅ Φ₂.presheafFiber where
  hom := e.inv.presheafFiber
  inv := e.hom.presheafFiber
  hom_inv_id := by rw [← Hom.presheafFiber_comp, e.hom_inv_id, Hom.presheafFiber_id]
  inv_hom_id := by rw [← Hom.presheafFiber_comp, e.inv_hom_id, Hom.presheafFiber_id]

@[simp]
lemma presheafFiberIso_hom (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A] [HasColimitsOfSize.{w, w} A] :
    (presheafFiberIso e A).hom = e.inv.presheafFiber :=
  (rfl)

@[simp]
lemma presheafFiberIso_inv (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A] [HasColimitsOfSize.{w, w} A] :
    (presheafFiberIso e A).inv = e.hom.presheafFiber :=
  (rfl)

/-- An isomorphism `Φ₁ ≅ Φ₂` of points induces a natural isomorphism of sheaf fibre functors. -/
noncomputable def sheafFiberIso (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A]
    [HasColimitsOfSize.{w, w} A] :
    Φ₁.sheafFiber (A := A) ≅ Φ₂.sheafFiber :=
  Functor.isoWhiskerLeft _ (presheafFiberIso e A)

@[simp]
lemma sheafFiberIso_hom (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A] [HasColimitsOfSize.{w, w} A] :
    (sheafFiberIso e A).hom = Functor.whiskerLeft (sheafToPresheaf J A) e.inv.presheafFiber :=
  (rfl)

@[simp]
lemma sheafFiberIso_inv (e : Φ₁ ≅ Φ₂) (A : Type*) [Category* A] [HasColimitsOfSize.{w, w} A] :
    (sheafFiberIso e A).inv = Functor.whiskerLeft (sheafToPresheaf J A) e.hom.presheafFiber :=
  (rfl)

end Iso

section Comap

variable {C D : Type*} [Category* C] [Category* D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (Φ : Point.{w} K) (F : C ⥤ D) {Ψ : Point.{w} J}

/-- When `F ⋙ Φ.fiber` is naturally isomorphic to the fibre functor of a point `Ψ`, its category
of elements inherits `InitiallySmall` from `Ψ`. -/
lemma initiallySmall_elements_of_fiberIso (e : F ⋙ Φ.fiber ≅ Ψ.fiber) :
    InitiallySmall.{w} (F ⋙ Φ.fiber).Elements := by
  let eqv : (F ⋙ Φ.fiber).Elements ≌ Ψ.fiber.Elements :=
    { functor := e.hom.mapElements
      inverse := e.inv.mapElements
      unitIso := NatIso.ofComponents (fun _ ↦ Functor.Elements.isoMk (Iso.refl _) (by simp))
      counitIso := NatIso.ofComponents (fun _ ↦ Functor.Elements.isoMk (Iso.refl _) (by simp)) }
  have : eqv.inverse.Initial := Functor.initial_of_adjunction eqv.symm.toAdjunction
  exact initiallySmall_of_initial_of_initiallySmall eqv.inverse

variable [RepresentablyFlat F] (hF : CoverPreserving J K F)

/-- When `F ⋙ Φ.fiber ≅ Ψ.fiber`, the inverse image point `Φ.comap F hF` is isomorphic to `Ψ`. -/
def comapIsoOfFiberIso (e : F ⋙ Φ.fiber ≅ Ψ.fiber) :
    letI := initiallySmall_elements_of_fiberIso Φ F e
    Φ.comap F hF ≅ Ψ :=
  letI := initiallySmall_elements_of_fiberIso Φ F e
  isoMk e.symm

@[simp]
lemma comapIsoOfFiberIso_hom_hom (e : F ⋙ Φ.fiber ≅ Ψ.fiber) :
    letI := initiallySmall_elements_of_fiberIso Φ F e
    (comapIsoOfFiberIso Φ F hF e).hom.hom = e.inv :=
  (rfl)

@[simp]
lemma comapIsoOfFiberIso_inv_hom (e : F ⋙ Φ.fiber ≅ Ψ.fiber) :
    letI := initiallySmall_elements_of_fiberIso Φ F e
    (comapIsoOfFiberIso Φ F hF e).inv.hom = e.hom :=
  (rfl)

/-- When `F : (C, J) ⥤ (D, K)` is continuous, representably flat, and cover-preserving and
`F ⋙ Φ.fiber ≅ Ψ.fiber`, taking the stalk at `Φ` after sheaf pullback along `F` is naturally
isomorphic to taking the stalk at `Ψ`. -/
noncomputable def sheafPullbackCompSheafFiberIso (e : F ⋙ Φ.fiber ≅ Ψ.fiber)
    (A : Type*) [Category* A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    [F.IsContinuous J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    F.sheafPullback A J K ⋙ Φ.sheafFiber ≅ Ψ.sheafFiber :=
  letI := initiallySmall_elements_of_fiberIso Φ F e
  (Φ.sheafFiberComapIso F hF A).symm ≪≫ sheafFiberIso (comapIsoOfFiberIso Φ F hF e) A

end Comap

end CategoryTheory.GrothendieckTopology.Point
