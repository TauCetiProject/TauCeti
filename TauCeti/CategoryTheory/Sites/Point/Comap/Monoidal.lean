/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import TauCeti.CategoryTheory.Sites.Point.Comap

/-!
# Pullback of sheaves commutes with tensor products on stalks

Let `A` be a monoidal category and `u : (C, J) ⥤ (D, K)` a continuous functor between sites whose
sheaf pushforward `u_*` has a left adjoint, the pullback `u^*`. Equip `Sheaf J A` and `Sheaf K A`
with the tensor product obtained by sheafifying the sectionwise tensor product
(`CategoryTheory.Sheaf.monoidalCategory`). This file constructs the canonical comparison
`u^* (F ⊗ G) ⟶ u^* F ⊗ u^* G` and shows that it is an isomorphism on the stalk at every point `Φ`
of `(D, K)` whose fibre functor restricts along `u` to the fibre functor of a point `Ψ` of
`(C, J)`: under the identification of the stalks of `u^* F` at `Φ` with the stalks of `F` at `Ψ`
(`CategoryTheory.GrothendieckTopology.Point.sheafPullbackCompSheafFiberIso`), it is the identity
of `Ψ F ⊗ Ψ G`. When such points jointly reflect isomorphisms of sheaves on `D`, the comparison
is an isomorphism.

## Main declarations

* `CategoryTheory.Sheaf.toTensorObj F G`: the canonical map `F.obj ⊗ G.obj ⟶ (F ⊗ G).obj` from
  the sectionwise tensor product of two sheaves to their tensor product.
* `CategoryTheory.GrothendieckTopology.Point.presheafFiberTensorIso`: the stalk of `F ⊗ G` at a
  point is the tensor product of the stalks, with its action on germs
  `toTensorObj_app_comp_toPresheafFiber_comp_presheafFiberTensorIso_hom`.
* `CategoryTheory.Functor.sheafPullbackTensorHom u A J K F G`: the comparison
  `u^* (F ⊗ G) ⟶ u^* F ⊗ u^* G`, adjoint to the map `F ⊗ G ⟶ u_* (u^* F ⊗ u^* G)` induced by the
  units of the adjunction `u^* ⊣ u_*`.
* `CategoryTheory.GrothendieckTopology.Point.isIso_sheafFiber_map_sheafPullbackTensorHom`: the
  comparison is an isomorphism on the stalk at a point `Φ` with `u ⋙ Φ.fiber ≅ Ψ.fiber`.
* `CategoryTheory.Functor.isIso_sheafPullbackTensorHom`: if such points jointly reflect
  isomorphisms, the comparison is an isomorphism.
-/

public section

universe w

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

attribute [local instance] Sheaf.monoidalCategory

namespace Sheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]
  [MonoidalCategory A] [HasWeakSheafify J A] [(J.W (A := A)).IsMonoidal]

/-- The canonical map from the sectionwise tensor product of the underlying presheaves of two
sheaves to the underlying presheaf of their tensor product: the unit of sheafification followed by
the identification of the sheafified tensor product with `F ⊗ G`. -/
noncomputable def toTensorObj (F G : Sheaf J A) : F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  CategoryTheory.toSheafify J (F.obj ⊗ G.obj) ≫
    ((Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).inv ≫
      ((sheafificationIso F).inv ⊗ₘ (sheafificationIso G).inv)).hom

end Sheaf

namespace GrothendieckTopology.Point

section Fiber

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type*} [Category* A] [MonoidalCategory A] [HasColimitsOfSize.{w, w} A]
  [HasProducts.{w} A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

/-- On stalks, the comparison `Sheaf.toTensorObj F G` is an isomorphism: the unit of
sheafification is inverted by the fibre functor of a point. -/
instance isIso_presheafFiber_map_toTensorObj (F G : Sheaf J A) :
    IsIso (Φ.presheafFiber.map (Sheaf.toTensorObj F G)) := by
  rw [Sheaf.toTensorObj, Functor.map_comp]
  infer_instance

end Fiber

section FiberTensor

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type*} [Category* A] [MonoidalCategory A] [HasColimitsOfSize.{w, w} A]
  [HasProducts.{w} A] [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [LocallySmall.{w} C]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]

/-- The stalk at a point of the tensor product of two sheaves is the tensor product of their
stalks: the stalk of `Sheaf.toTensorObj F G`, followed by the tensor comparison of the presheaf
fibre functor. -/
noncomputable def presheafFiberTensorIso (F G : Sheaf J A) :
    Φ.presheafFiber.obj (F ⊗ G).obj ≅ Φ.presheafFiber.obj F.obj ⊗ Φ.presheafFiber.obj G.obj :=
  haveI : IsIso (Φ.presheafFiber.map (Sheaf.toTensorObj F G)) := by infer_instance
  (asIso (Φ.presheafFiber.map (Sheaf.toTensorObj F G))).symm ≪≫
    (Functor.Monoidal.μIso Φ.presheafFiber F.obj G.obj).symm

/-- On germs, `presheafFiberTensorIso` sends the germ of the image of a section of the sectionwise
tensor product to the tensor product of the germs. -/
@[reassoc]
lemma toTensorObj_app_comp_toPresheafFiber_comp_presheafFiberTensorIso_hom (F G : Sheaf J A)
    (X : C) (x : Φ.fiber.obj X) :
    (Sheaf.toTensorObj F G).app (op X) ≫ Φ.toPresheafFiber X x (F ⊗ G).obj ≫
        (Φ.presheafFiberTensorIso F G).hom =
      Φ.toPresheafFiber X x F.obj ⊗ₘ Φ.toPresheafFiber X x G.obj := by
  rw [← toPresheafFiber_naturality_assoc, presheafFiberTensorIso, Iso.trans_hom, Iso.symm_hom,
    Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc, Functor.Monoidal.μIso_inv,
    toPresheafFiber_δ]

end FiberTensor

end GrothendieckTopology.Point

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (u : C ⥤ D) (A : Type*) [Category* A]
  [MonoidalCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A] [(J.W (A := A)).IsMonoidal]
  [(K.W (A := A)).IsMonoidal] [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- The sectionwise map `F.obj ⊗ G.obj ⟶ u_* (u^* F ⊗ u^* G)` given over `X` by the units of the
adjunction `u^* ⊣ u_*` at `F` and `G` followed by `Sheaf.toTensorObj` over `u X`. -/
noncomputable def sheafPullbackTensorAux (F G : Sheaf J A) :
    F.obj ⊗ G.obj ⟶ ((u.sheafPushforwardContinuous A J K).obj
      ((u.sheafPullback A J K).obj F ⊗ (u.sheafPullback A J K).obj G)).obj :=
  (((u.sheafAdjunctionContinuous A J K).unit.app F).hom ⊗ₘ
      ((u.sheafAdjunctionContinuous A J K).unit.app G).hom) ≫
    Functor.whiskerLeft u.op (Sheaf.toTensorObj _ _)

/-- The map `F ⊗ G ⟶ u_* (u^* F ⊗ u^* G)` of sheaves induced by `sheafPullbackTensorAux`. -/
noncomputable def sheafPullbackTensorAdj (F G : Sheaf J A) :
    F ⊗ G ⟶ (u.sheafPushforwardContinuous A J K).obj
      ((u.sheafPullback A J K).obj F ⊗ (u.sheafPullback A J K).obj G) :=
  ((sheafificationIso F).hom ⊗ₘ (sheafificationIso G).hom) ≫
    (Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).hom ≫
      ((sheafificationAdjunction J A).homEquiv _ _).symm (u.sheafPullbackTensorAux A J K F G)

/-- On underlying presheaves, `sheafPullbackTensorAdj` restricts along `Sheaf.toTensorObj` to
`sheafPullbackTensorAux`. -/
lemma toTensorObj_comp_sheafPullbackTensorAdj_hom (F G : Sheaf J A) :
    Sheaf.toTensorObj F G ≫ (u.sheafPullbackTensorAdj A J K F G).hom =
      u.sheafPullbackTensorAux A J K F G := by
  have h : ((Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).inv ≫
      ((sheafificationIso F).inv ⊗ₘ (sheafificationIso G).inv)) ≫
        u.sheafPullbackTensorAdj A J K F G =
      ((sheafificationAdjunction J A).homEquiv _ _).symm (u.sheafPullbackTensorAux A J K F G) := by
    simp [sheafPullbackTensorAdj, tensorHom_comp_tensorHom_assoc]
  have h' := congrArg (fun f ↦ CategoryTheory.toSheafify J (F.obj ⊗ G.obj) ≫ f.hom) h
  rw [Sheaf.toTensorObj, Category.assoc]
  refine h'.trans ?_
  exact ((sheafificationAdjunction J A).homEquiv_unit (F.obj ⊗ G.obj)
    ((u.sheafPushforwardContinuous A J K).obj
      ((u.sheafPullback A J K).obj F ⊗ (u.sheafPullback A J K).obj G)) _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- **The tensor comparison of sheaf pullback.** The canonical map
`u^* (F ⊗ G) ⟶ u^* F ⊗ u^* G`, adjoint to the map `F ⊗ G ⟶ u_* (u^* F ⊗ u^* G)` induced by the
units of `u^* ⊣ u_*`. -/
noncomputable def sheafPullbackTensorHom (F G : Sheaf J A) :
    (u.sheafPullback A J K).obj (F ⊗ G) ⟶
      (u.sheafPullback A J K).obj F ⊗ (u.sheafPullback A J K).obj G :=
  ((u.sheafAdjunctionContinuous A J K).homEquiv _ _).symm (u.sheafPullbackTensorAdj A J K F G)

/-- The comparison `sheafPullbackTensorHom` is adjoint to `sheafPullbackTensorAdj`. -/
lemma unit_comp_sheafPullbackTensorHom (F G : Sheaf J A) :
    (u.sheafAdjunctionContinuous A J K).unit.app (F ⊗ G) ≫
      (u.sheafPushforwardContinuous A J K).map (u.sheafPullbackTensorHom A J K F G) =
        u.sheafPullbackTensorAdj A J K F G := by
  exact (((u.sheafAdjunctionContinuous A J K).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _))

/-- Over `X : C`, the sectionwise comparison `Sheaf.toTensorObj F G` followed by the unit of
`u^* ⊣ u_*` at `F ⊗ G` and the tensor comparison of `u^*` is `sheafPullbackTensorAux`. -/
lemma toTensorObj_app_comp_unit_app_comp_sheafPullbackTensorHom_app (F G : Sheaf J A) (X : C) :
    (Sheaf.toTensorObj F G).app (op X) ≫
        ((u.sheafAdjunctionContinuous A J K).unit.app (F ⊗ G)).hom.app (op X) ≫
          (u.sheafPullbackTensorHom A J K F G).hom.app (op (u.obj X)) =
      (u.sheafPullbackTensorAux A J K F G).app (op X) := by
  have h := congrArg (fun f ↦ (Sheaf.toTensorObj F G ≫ f.hom).app (op X))
    (u.unit_comp_sheafPullbackTensorHom A J K F G)
  simp only [toTensorObj_comp_sheafPullbackTensorAdj_hom] at h
  exact h

end Functor

namespace GrothendieckTopology.Point

variable {C D : Type*} [Category* C] [Category* D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (Φ : Point.{w} K) (u : C ⥤ D) {Ψ : Point.{w} J}
  (e : u ⋙ Φ.fiber ≅ Ψ.fiber) (A : Type*) [Category* A] [MonoidalCategory A]
  [HasColimitsOfSize.{w, w} A] [HasProducts.{w} A] [LocallySmall.{w} C] [LocallySmall.{w} D]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [HasWeakSheafify J A] [HasWeakSheafify K A] [(J.W (A := A)).IsMonoidal]
  [(K.W (A := A)).IsMonoidal] [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]

include e in
/-- The stalk at `Φ` of the comparison `u^* (F ⊗ G) ⟶ u^* F ⊗ u^* G` is an isomorphism, given
identifications `NF`, `NG`, `NT` of the stalks at `Φ` of the pullbacks with the stalks at `Ψ` and
maps `ηF`, `ηG`, `ηT` on sections, compatible with germs and with the comparison. -/
private lemma isIso_presheafFiber_map_sheafPullbackTensorHom_hom_of_germs {F G : Sheaf J A}
    (NF : Φ.presheafFiber.obj ((u.sheafPullback A J K).obj F).obj ≅ Ψ.presheafFiber.obj F.obj)
    (NG : Φ.presheafFiber.obj ((u.sheafPullback A J K).obj G).obj ≅ Ψ.presheafFiber.obj G.obj)
    (NT : Φ.presheafFiber.obj ((u.sheafPullback A J K).obj (F ⊗ G)).obj ≅
      Ψ.presheafFiber.obj (F ⊗ G).obj)
    (ηF : ∀ X : C, F.obj.obj (op X) ⟶ ((u.sheafPullback A J K).obj F).obj.obj (op (u.obj X)))
    (ηG : ∀ X : C, G.obj.obj (op X) ⟶ ((u.sheafPullback A J K).obj G).obj.obj (op (u.obj X)))
    (ηT : ∀ X : C, (F ⊗ G).obj.obj (op X) ⟶
      ((u.sheafPullback A J K).obj (F ⊗ G)).obj.obj (op (u.obj X)))
    (hF : ∀ (X : C) (x : Φ.fiber.obj (u.obj X)),
      ηF X ≫ Φ.toPresheafFiber (u.obj X) x ((u.sheafPullback A J K).obj F).obj ≫ NF.hom =
        Ψ.toPresheafFiber X (e.hom.app X x) F.obj)
    (hG : ∀ (X : C) (x : Φ.fiber.obj (u.obj X)),
      ηG X ≫ Φ.toPresheafFiber (u.obj X) x ((u.sheafPullback A J K).obj G).obj ≫ NG.hom =
        Ψ.toPresheafFiber X (e.hom.app X x) G.obj)
    (hT : ∀ (X : C) (y : Ψ.fiber.obj X), Ψ.toPresheafFiber X y (F ⊗ G).obj ≫ NT.inv =
      ηT X ≫ Φ.toPresheafFiber (u.obj X) (e.inv.app X y)
        ((u.sheafPullback A J K).obj (F ⊗ G)).obj)
    (hη : ∀ X : C, (Sheaf.toTensorObj F G).app (op X) ≫ ηT X ≫
        (u.sheafPullbackTensorHom A J K F G).hom.app (op (u.obj X)) =
      (ηF X ⊗ₘ ηG X) ≫ (Sheaf.toTensorObj _ _).app (op (u.obj X))) :
    IsIso (Φ.presheafFiber.map (u.sheafPullbackTensorHom A J K F G).hom) := by
  have key : NT.inv ≫ Φ.presheafFiber.map (u.sheafPullbackTensorHom A J K F G).hom ≫
      (Φ.presheafFiberTensorIso _ _).hom ≫ (NF.hom ⊗ₘ NG.hom) =
      (Ψ.presheafFiberTensorIso F G).hom := by
    refine (cancel_epi (Ψ.presheafFiber.map (Sheaf.toTensorObj F G))).1 ?_
    refine Ψ.presheafFiber_hom_ext fun X y ↦ ?_
    rw [toPresheafFiber_naturality_assoc, toPresheafFiber_naturality_assoc,
      toTensorObj_app_comp_toPresheafFiber_comp_presheafFiberTensorIso_hom,
      reassoc_of% (hT X y)]
    erw [toPresheafFiber_naturality_assoc]
    erw [reassoc_of% (hη X)]
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (toTensorObj_app_comp_toPresheafFiber_comp_presheafFiberTensorIso_hom_assoc Φ _ _
        (u.obj X) (e.inv.app X y) (NF.hom ⊗ₘ NG.hom))).trans ?_)
    erw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    rw [hF, hG]
    simp
  have : IsIso (Φ.presheafFiber.map (u.sheafPullbackTensorHom A J K F G).hom ≫
      ((Φ.presheafFiberTensorIso _ _).hom ≫ (NF.hom ⊗ₘ NG.hom))) := by
    rw [(Iso.inv_comp_eq _).mp key]
    infer_instance
  have hg : IsIso ((Φ.presheafFiberTensorIso ((u.sheafPullback A J K).obj F)
      ((u.sheafPullback A J K).obj G)).hom ≫ (NF.hom ⊗ₘ NG.hom)) := by
    infer_instance
  exact IsIso.of_isIso_comp_right (Φ.presheafFiber.map (u.sheafPullbackTensorHom A J K F G).hom)
    ((Φ.presheafFiberTensorIso _ _).hom ≫ (NF.hom ⊗ₘ NG.hom))

include e in
/-- **Stalks of the tensor comparison of sheaf pullback.** At a point `Φ` of `(D, K)` with
`u ⋙ Φ.fiber ≅ Ψ.fiber` for a point `Ψ` of `(C, J)`, the stalk of the comparison
`u^* (F ⊗ G) ⟶ u^* F ⊗ u^* G` is an isomorphism: under the identifications of the stalks of
pullbacks at `Φ` with stalks at `Ψ` (`Point.sheafPullbackCompSheafFiberIso`) and of stalks of
tensor products with tensor products of stalks, it is the identity of `Ψ F ⊗ Ψ G`. -/
theorem isIso_sheafFiber_map_sheafPullbackTensorHom (F G : Sheaf J A) :
    IsIso (Φ.sheafFiber.map (u.sheafPullbackTensorHom A J K F G)) :=
  isIso_presheafFiber_map_sheafPullbackTensorHom_hom_of_germs Φ u e A
    ((Φ.sheafPullbackCompSheafFiberIso u e A).app F)
    ((Φ.sheafPullbackCompSheafFiberIso u e A).app G)
    ((Φ.sheafPullbackCompSheafFiberIso u e A).app (F ⊗ G))
    (fun X ↦ ((u.sheafAdjunctionContinuous A J K).unit.app F).hom.app (op X))
    (fun X ↦ ((u.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X))
    (fun X ↦ ((u.sheafAdjunctionContinuous A J K).unit.app (F ⊗ G)).hom.app (op X))
    (Φ.unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app u e A F)
    (Φ.unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app u e A G)
    (Φ.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app u e A (F ⊗ G))
    (u.toTensorObj_app_comp_unit_app_comp_sheafPullbackTensorHom_app A J K F G)

end GrothendieckTopology.Point

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (u : C ⥤ D) (A : Type*) [Category* A]
  [MonoidalCategory A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasColimitsOfSize.{w, w} A] [HasProducts.{w} A] [LocallySmall.{w} C] [LocallySmall.{w} D]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)]
  [HasWeakSheafify J A] [HasWeakSheafify K A] [(J.W (A := A)).IsMonoidal]
  [(K.W (A := A)).IsMonoidal] [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- **Pullback of sheaves commutes with tensor products.** If the stalk functors at a family of
points `Φ i` of `(D, K)` jointly reflect isomorphisms, and each `u ⋙ (Φ i).fiber` is the fibre
functor of a point `Ψ i` of `(C, J)`, then the comparison `u^* (F ⊗ G) ⟶ u^* F ⊗ u^* G` is an
isomorphism. -/
theorem isIso_sheafPullbackTensorHom {ι : Type*} (Φ : ι → GrothendieckTopology.Point.{w} K)
    (Ψ : ι → GrothendieckTopology.Point.{w} J) (e : ∀ i, u ⋙ (Φ i).fiber ≅ (Ψ i).fiber)
    (hΦ : JointlyReflectIsomorphisms fun i ↦ (Φ i).sheafFiber (A := A)) (F G : Sheaf J A) :
    IsIso (u.sheafPullbackTensorHom A J K F G) :=
  have := fun i ↦ (Φ i).isIso_sheafFiber_map_sheafPullbackTensorHom u (e i) A F G
  hΦ.isIso _

end Functor

end CategoryTheory
