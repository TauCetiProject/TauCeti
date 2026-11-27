/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Point.Comap
public import TauCeti.CategoryTheory.Sites.Point.Monoidal

/-!
# Pullback of sheaves commutes with tensor products on stalks

Let `A` be a monoidal category and `u : (C, J) ⥤ (D, K)` a continuous functor between sites whose
sheaf pushforward `u_*` has a left adjoint, the pullback `u^*`. Equip `Sheaf J A` and `Sheaf K A`
with the tensor product obtained by sheafifying the sectionwise tensor product
(`CategoryTheory.Sheaf.monoidalCategory`). This file constructs the canonical comparison
`u^* (F ⊗ G) ⟶ u^* F ⊗ u^* G` and shows that it is an isomorphism on the stalk at every point `Φ`
of `(D, K)` whose fibre functor restricts along `u` to the fibre functor of a point `Ψ` of
`(C, J)`; this is checked on germs, through the identification of the stalks of `u^* F` at `Φ`
with the stalks of `F` at `Ψ`
(`CategoryTheory.GrothendieckTopology.Point.sheafPullbackCompSheafFiberIso`). When such points
jointly reflect isomorphisms of sheaves on `D`, the comparison is an isomorphism.

## Main declarations

* `CategoryTheory.Functor.sheafPullbackTensorHom u A J K F G`: the comparison
  `u^* (F ⊗ G) ⟶ u^* F ⊗ u^* G`, adjoint to the map `F ⊗ G ⟶ u_* (u^* F ⊗ u^* G)` induced by the
  units of the adjunction `u^* ⊣ u_*`; it is characterised by
  `toTensorObj_app_comp_unit_app_comp_sheafPullbackTensorHom_app` and natural
  (`sheafPullbackTensorHom_naturality`).
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

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] (u : C ⥤ D) (A : Type*) [Category* A]
  [MonoidalCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A] [(J.W (A := A)).IsMonoidal]
  [(K.W (A := A)).IsMonoidal] [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- The sectionwise map `F.obj ⊗ G.obj ⟶ u_* (u^* F ⊗ u^* G)` given over `X` by the units of the
adjunction `u^* ⊣ u_*` at `F` and `G` followed by `Sheaf.toTensorObj` over `u X`. -/
private noncomputable def sheafPullbackTensorAux (F G : Sheaf J A) :
    F.obj ⊗ G.obj ⟶ ((u.sheafPushforwardContinuous A J K).obj
      ((u.sheafPullback A J K).obj F ⊗ (u.sheafPullback A J K).obj G)).obj :=
  (((u.sheafAdjunctionContinuous A J K).unit.app F).hom ⊗ₘ
      ((u.sheafAdjunctionContinuous A J K).unit.app G).hom) ≫
    Functor.whiskerLeft u.op (Sheaf.toTensorObj _ _)

/-- The map `F ⊗ G ⟶ u_* (u^* F ⊗ u^* G)` of sheaves induced by `sheafPullbackTensorAux`. -/
private noncomputable def sheafPullbackTensorAdj (F G : Sheaf J A) :
    F ⊗ G ⟶ (u.sheafPushforwardContinuous A J K).obj
      ((u.sheafPullback A J K).obj F ⊗ (u.sheafPullback A J K).obj G) :=
  ((sheafificationIso F).hom ⊗ₘ (sheafificationIso G).hom) ≫
    (Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).hom ≫
      ((sheafificationAdjunction J A).homEquiv _ _).symm (sheafPullbackTensorAux u A J K F G)

/-- On underlying presheaves, `sheafPullbackTensorAdj` restricts along `Sheaf.toTensorObj` to
`sheafPullbackTensorAux`. -/
private lemma toTensorObj_comp_sheafPullbackTensorAdj_hom (F G : Sheaf J A) :
    Sheaf.toTensorObj F G ≫ (sheafPullbackTensorAdj u A J K F G).hom =
      sheafPullbackTensorAux u A J K F G := by
  have h : ((Functor.Monoidal.μIso (presheafToSheaf J A) F.obj G.obj).inv ≫
      ((sheafificationIso F).inv ⊗ₘ (sheafificationIso G).inv)) ≫
        sheafPullbackTensorAdj u A J K F G =
      ((sheafificationAdjunction J A).homEquiv _ _).symm (sheafPullbackTensorAux u A J K F G) := by
    simp [sheafPullbackTensorAdj, tensorHom_comp_tensorHom_assoc]
  rw [Sheaf.toTensorObj, Category.assoc, ← ObjectProperty.FullSubcategory.comp_hom, h]
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
  ((u.sheafAdjunctionContinuous A J K).homEquiv _ _).symm (sheafPullbackTensorAdj u A J K F G)

/-- The comparison `sheafPullbackTensorHom` is adjoint to `sheafPullbackTensorAdj`. -/
private lemma unit_comp_sheafPullbackTensorHom (F G : Sheaf J A) :
    (u.sheafAdjunctionContinuous A J K).unit.app (F ⊗ G) ≫
      (u.sheafPushforwardContinuous A J K).map (u.sheafPullbackTensorHom A J K F G) =
        sheafPullbackTensorAdj u A J K F G := by
  simp [sheafPullbackTensorHom, Adjunction.homEquiv_counit]

/-- Over `X : C`, the comparison `Sheaf.toTensorObj F G` followed by the unit of `u^* ⊣ u_*` at
`F ⊗ G` and the tensor comparison of `u^*` is the tensor product of the units at `F` and `G`
followed by `Sheaf.toTensorObj` over `u X`: this characterises `sheafPullbackTensorHom`. -/
@[reassoc]
lemma toTensorObj_app_comp_unit_app_comp_sheafPullbackTensorHom_app (F G : Sheaf J A) (X : C) :
    (Sheaf.toTensorObj F G).app (op X) ≫
        ((u.sheafAdjunctionContinuous A J K).unit.app (F ⊗ G)).hom.app (op X) ≫
          (u.sheafPullbackTensorHom A J K F G).hom.app (op (u.obj X)) =
      (((u.sheafAdjunctionContinuous A J K).unit.app F).hom.app (op X) ⊗ₘ
          ((u.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X)) ≫
        (Sheaf.toTensorObj _ _).app (op (u.obj X)) := by
  have h := congrArg (fun φ ↦ (Sheaf.toTensorObj F G ≫ φ.hom).app (op X))
    (unit_comp_sheafPullbackTensorHom u A J K F G)
  simp only [toTensorObj_comp_sheafPullbackTensorAdj_hom] at h
  exact h

/-- The tensor comparison of sheaf pullback is natural in both sheaves. -/
@[reassoc]
lemma sheafPullbackTensorHom_naturality {F F' G G' : Sheaf J A} (f : F ⟶ F') (g : G ⟶ G') :
    (u.sheafPullback A J K).map (f ⊗ₘ g) ≫ u.sheafPullbackTensorHom A J K F' G' =
      u.sheafPullbackTensorHom A J K F G ≫
        ((u.sheafPullback A J K).map f ⊗ₘ (u.sheafPullback A J K).map g) := by
  refine ((u.sheafAdjunctionContinuous A J K).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [sheafPullbackTensorHom, Equiv.apply_symm_apply]
  refine Sheaf.tensorObj_hom_ext ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ← Sheaf.toTensorObj_naturality_assoc, toTensorObj_comp_sheafPullbackTensorAdj_hom,
    reassoc_of% toTensorObj_comp_sheafPullbackTensorAdj_hom]
  ext ⟨X⟩
  -- The units over `X`, typed as maps into the sections of the pullbacks over `u X`.
  let η (H : Sheaf J A) :
      H.obj.obj (op X) ⟶ ((u.sheafPullback A J K).obj H).obj.obj (op (u.obj X)) :=
    ((u.sheafAdjunctionContinuous A J K).unit.app H).hom.app (op X)
  have hη {H H' : Sheaf J A} (φ : H ⟶ H') :
      φ.hom.app (op X) ≫ η H' = η H ≫ ((u.sheafPullback A J K).map φ).hom.app (op (u.obj X)) :=
    congr_app (congrArg (·.hom) ((u.sheafAdjunctionContinuous A J K).unit.naturality φ)) (op X)
  have hN := congr_app (Sheaf.toTensorObj_naturality ((u.sheafPullback A J K).map f)
    ((u.sheafPullback A J K).map g)) (op (u.obj X))
  simp only [NatTrans.comp_app, Monoidal.tensorHom_app] at hN
  have key : (f.hom.app (op X) ⊗ₘ g.hom.app (op X)) ≫ (η F' ⊗ₘ η G') ≫
        (Sheaf.toTensorObj _ _).app (op (u.obj X)) =
      ((η F ⊗ₘ η G) ≫ (Sheaf.toTensorObj _ _).app (op (u.obj X))) ≫
        ((u.sheafPullback A J K).map f ⊗ₘ (u.sheafPullback A J K).map g).hom.app
          (op (u.obj X)) := by
    -- `erw` crosses the pointwise tensor product of presheaves: the source of
    -- `(Sheaf.toTensorObj _ _).app` is `(P ⊗ Q).obj _`, which is `P.obj _ ⊗ Q.obj _` only by
    -- unfolding the monoidal structure on the functor category.
    erw [tensorHom_comp_tensorHom_assoc, hη, hη, ← tensorHom_comp_tensorHom_assoc, hN]
    exact (Category.assoc _ _ _).symm
  exact key

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
  have key : Ψ.presheafFiber.map (Sheaf.toTensorObj F G) ≫ NT.inv ≫
      Φ.presheafFiber.map (u.sheafPullbackTensorHom A J K F G).hom ≫
        δ Φ.sheafFiber _ _ ≫ (NF.hom ⊗ₘ NG.hom) = δ Ψ.presheafFiber F.obj G.obj := by
    refine Ψ.presheafFiber_hom_ext fun X y ↦ ?_
    rw [toPresheafFiber_δ, toPresheafFiber_naturality_assoc, reassoc_of% (hT X y),
      Φ.toPresheafFiber_naturality_assoc (u.sheafPullbackTensorHom A J K F G).hom _ _
        (δ Φ.sheafFiber _ _ ≫ (NF.hom ⊗ₘ NG.hom)),
      reassoc_of% (hη X)]
    -- Reassociate by hand: `reassoc_of%` leaves this composite left-associated.
    refine (Category.assoc _ _ _).trans ?_
    -- `erw` crosses the pointwise tensor product of presheaves, `(P ⊗ Q).obj _` being
    -- `P.obj _ ⊗ Q.obj _` only after unfolding, and the definition of `Point.sheafFiber`.
    erw [Φ.toTensorObj_app_comp_toPresheafFiber_comp_δ_assoc, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom]
    rw [hF, hG]
    simp
  -- Instance search does not see through the `Point.sheafFiber` boundary in this composite.
  have hg : IsIso (δ Φ.sheafFiber ((u.sheafPullback A J K).obj F) ((u.sheafPullback A J K).obj G) ≫
      (NF.hom ⊗ₘ NG.hom)) :=
    IsIso.comp_isIso' inferInstance (inferInstanceAs (IsIso (NF ⊗ᵢ NG).hom))
  have h : IsIso (Ψ.presheafFiber.map (Sheaf.toTensorObj F G) ≫ NT.inv ≫
      Φ.presheafFiber.map (u.sheafPullbackTensorHom A J K F G).hom ≫
        δ Φ.sheafFiber _ _ ≫ (NF.hom ⊗ₘ NG.hom)) := by
    rw [key]
    infer_instance
  rw [isIso_comp_left_iff, isIso_comp_left_iff] at h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hg h

include e in
/-- **Stalks of the tensor comparison of sheaf pullback.** At a point `Φ` of `(D, K)` with
`u ⋙ Φ.fiber ≅ Ψ.fiber` for a point `Ψ` of `(C, J)`, the stalk of the comparison
`u^* (F ⊗ G) ⟶ u^* F ⊗ u^* G` is an isomorphism. This is checked on germs, using the
identifications of the stalks of pullbacks at `Φ` with stalks at `Ψ`
(`Point.sheafPullbackCompSheafFiberIso`) and of stalks of tensor products with tensor products
of stalks (`OplaxMonoidal.δ` of the fibre functors). -/
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
