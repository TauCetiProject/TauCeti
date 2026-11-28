/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Point.Comap
public import TauCeti.CategoryTheory.Sites.Point.Monoidal
public import TauCeti.CategoryTheory.Sites.Pullback.Monoidal

/-!
# Pullback of sheaves commutes with tensor products and units on stalks

Let `A` be a monoidal category and `u : (C, J) ⥤ (D, K)` a continuous functor between sites whose
sheaf pushforward `u_*` has a left adjoint, the pullback `u^*`. Equip `Sheaf J A` and `Sheaf K A`
with the tensor product obtained by sheafifying the sectionwise tensor product
(`CategoryTheory.Sheaf.monoidalCategory`), so that `u^*` is oplax monoidal
(`CategoryTheory.Functor.sheafPullbackOplaxMonoidal`). This file shows that its tensor comparison
`OplaxMonoidal.δ (u.sheafPullback A J K) F G : u^* (F ⊗ G) ⟶ u^* F ⊗ u^* G` is an isomorphism on
the stalk at every point `Φ` of `(D, K)` whose fibre functor restricts along `u` to the fibre
functor of a point `Ψ` of `(C, J)`; this is checked on germs, through the identification of the
stalks of `u^* F` at `Φ` with the stalks of `F` at `Ψ`
(`CategoryTheory.GrothendieckTopology.Point.sheafPullbackCompSheafFiberIso`). The same holds for
the unit comparison `OplaxMonoidal.η (u.sheafPullback A J K) : u^* 𝟙_ ⟶ 𝟙_`. When such points
jointly reflect isomorphisms of sheaves on `D`, both comparisons are isomorphisms.

## Main declarations

* `CategoryTheory.GrothendieckTopology.Point.isIso_sheafFiber_map_sheafPullback_δ`: the
  comparison is an isomorphism on the stalk at a point `Φ` with `u ⋙ Φ.fiber ≅ Ψ.fiber`.
* `CategoryTheory.Functor.isIso_sheafPullback_δ`: if such points jointly reflect isomorphisms,
  the comparison is an isomorphism.
* `CategoryTheory.GrothendieckTopology.Point.isIso_sheafFiber_map_sheafPullback_η`,
  `CategoryTheory.Functor.isIso_sheafPullback_η`: the same for the unit comparison.
-/

public section

universe w

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

attribute [local instance] Sheaf.monoidalCategory

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
private lemma isIso_presheafFiber_map_sheafPullback_δ_hom_of_germs {F G : Sheaf J A}
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
        (δ (u.sheafPullback A J K) F G).hom.app (op (u.obj X)) =
      (ηF X ⊗ₘ ηG X) ≫ (Sheaf.toTensorObj _ _).app (op (u.obj X))) :
    IsIso (Φ.presheafFiber.map (δ (u.sheafPullback A J K) F G).hom) := by
  have key : Ψ.presheafFiber.map (Sheaf.toTensorObj F G) ≫ NT.inv ≫
      Φ.presheafFiber.map (δ (u.sheafPullback A J K) F G).hom ≫
        δ Φ.sheafFiber _ _ ≫ (NF.hom ⊗ₘ NG.hom) = δ Ψ.presheafFiber F.obj G.obj := by
    refine Ψ.presheafFiber_hom_ext fun X y ↦ ?_
    rw [toPresheafFiber_δ, toPresheafFiber_naturality_assoc, reassoc_of% (hT X y),
      Φ.toPresheafFiber_naturality_assoc (δ (u.sheafPullback A J K) F G).hom _ _
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
      Φ.presheafFiber.map (δ (u.sheafPullback A J K) F G).hom ≫
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
theorem isIso_sheafFiber_map_sheafPullback_δ (F G : Sheaf J A) :
    IsIso (Φ.sheafFiber.map (δ (u.sheafPullback A J K) F G)) :=
  -- The germ lemma concludes `IsIso (Φ.presheafFiber.map (δ …).hom)`, which is this goal after
  -- unfolding the definition `Point.sheafFiber` (`sheafToPresheaf K A ⋙ Φ.presheafFiber`), so
  -- that `Φ.sheafFiber.map f` is `Φ.presheafFiber.map f.hom`.
  isIso_presheafFiber_map_sheafPullback_δ_hom_of_germs Φ u e A
    ((Φ.sheafPullbackCompSheafFiberIso u e A).app F)
    ((Φ.sheafPullbackCompSheafFiberIso u e A).app G)
    ((Φ.sheafPullbackCompSheafFiberIso u e A).app (F ⊗ G))
    (fun X ↦ ((u.sheafAdjunctionContinuous A J K).unit.app F).hom.app (op X))
    (fun X ↦ ((u.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op X))
    (fun X ↦ ((u.sheafAdjunctionContinuous A J K).unit.app (F ⊗ G)).hom.app (op X))
    (Φ.unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app u e A F)
    (Φ.unit_toPresheafFiber_sheafPullbackCompSheafFiberIso_hom_app u e A G)
    (Φ.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app u e A (F ⊗ G))
    (u.toTensorObj_app_comp_unit_app_comp_sheafPullback_δ_app A J K F G)

omit [LocallySmall.{w} C] [LocallySmall.{w} D]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)] in
include e in
/-- **Stalks of the unit comparison of sheaf pullback.** At a point `Φ` of `(D, K)` with
`u ⋙ Φ.fiber ≅ Ψ.fiber` for a point `Ψ` of `(C, J)`, the stalk of the comparison
`u^* 𝟙_ ⟶ 𝟙_` is an isomorphism. This is checked on germs, as for the tensor comparison
(`Point.isIso_sheafFiber_map_sheafPullback_δ`), using the stalks of `Sheaf.toTensorUnit` and the
unit comparisons `OplaxMonoidal.η` of the fibre functors on presheaves. -/
theorem isIso_sheafFiber_map_sheafPullback_η :
    IsIso (Φ.sheafFiber.map (η (u.sheafPullback A J K))) := by
  let N := (Φ.sheafPullbackCompSheafFiberIso u e A).app (𝟙_ (Sheaf J A))
  have key : Ψ.presheafFiber.map (Sheaf.toTensorUnit J A) ≫ N.inv ≫
      Φ.presheafFiber.map (η (u.sheafPullback A J K)).hom ≫
        inv (Φ.presheafFiber.map (Sheaf.toTensorUnit K A)) ≫ η Φ.presheafFiber =
      η Ψ.presheafFiber := by
    refine Ψ.presheafFiber_hom_ext fun X y ↦ ?_
    rw [toPresheafFiber_naturality_assoc, toPresheafFiber_η]
    -- `erw` crosses the definition of `Point.sheafFiber`, through which the germ formula for
    -- `sheafPullbackCompSheafFiberIso` types the stalks of `u^* 𝟙_`.
    erw [Φ.toPresheafFiber_sheafPullbackCompSheafFiberIso_inv_app_assoc u e A,
      Φ.toPresheafFiber_naturality_assoc (η (u.sheafPullback A J K)).hom]
    -- Reassociate by hand to apply the sections formula for `η`: `Category.assoc` does not
    -- rewrite across the sections of `u_* (u^* 𝟙_)` over `X`, which are those of `u^* 𝟙_` over
    -- `u X` only after unfolding `Functor.sheafPushforwardContinuous`.
    refine (((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm.trans
      (congrArg (· ≫ _) (u.toTensorUnit_app_comp_unit_app_comp_sheafPullback_η_app A J K X))).trans
        ?_
    rw [← Φ.toPresheafFiber_naturality_assoc, IsIso.hom_inv_id_assoc, toPresheafFiber_η]
  have h : IsIso (Ψ.presheafFiber.map (Sheaf.toTensorUnit J A) ≫ N.inv ≫
      Φ.presheafFiber.map (η (u.sheafPullback A J K)).hom ≫
        inv (Φ.presheafFiber.map (Sheaf.toTensorUnit K A)) ≫ η Φ.presheafFiber) := by
    rw [key]
    infer_instance
  rw [isIso_comp_left_iff] at h
  -- Instance search does not see through the `Point.sheafFiber` boundary in the type of `N.inv`.
  have h' := @IsIso.of_isIso_comp_left _ _ _ _ _ N.inv _ inferInstance h
  -- This closes the goal `IsIso (Φ.sheafFiber.map (η …))` with a proof of
  -- `IsIso (Φ.presheafFiber.map (η …).hom)`: the two agree after unfolding the definition
  -- `Point.sheafFiber` (`sheafToPresheaf K A ⋙ Φ.presheafFiber`).
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    (Φ.presheafFiber.map (η (u.sheafPullback A J K)).hom)
    (inv (Φ.presheafFiber.map (Sheaf.toTensorUnit K A)) ≫ η Φ.presheafFiber) inferInstance h'

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
theorem isIso_sheafPullback_δ {ι : Type*} (Φ : ι → GrothendieckTopology.Point.{w} K)
    (Ψ : ι → GrothendieckTopology.Point.{w} J) (e : ∀ i, u ⋙ (Φ i).fiber ≅ (Ψ i).fiber)
    (hΦ : JointlyReflectIsomorphisms fun i ↦ (Φ i).sheafFiber (A := A)) (F G : Sheaf J A) :
    IsIso (δ (u.sheafPullback A J K) F G) :=
  have := fun i ↦ (Φ i).isIso_sheafFiber_map_sheafPullback_δ u (e i) A F G
  hΦ.isIso _

omit [LocallySmall.{w} C] [LocallySmall.{w} D]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{w, w} (tensorRight X)] in
/-- **Pullback of sheaves preserves the unit.** If the stalk functors at a family of points `Φ i`
of `(D, K)` jointly reflect isomorphisms, and each `u ⋙ (Φ i).fiber` is the fibre functor of a
point `Ψ i` of `(C, J)`, then the comparison `u^* 𝟙_ ⟶ 𝟙_` is an isomorphism. -/
theorem isIso_sheafPullback_η {ι : Type*} (Φ : ι → GrothendieckTopology.Point.{w} K)
    (Ψ : ι → GrothendieckTopology.Point.{w} J) (e : ∀ i, u ⋙ (Φ i).fiber ≅ (Ψ i).fiber)
    (hΦ : JointlyReflectIsomorphisms fun i ↦ (Φ i).sheafFiber (A := A)) :
    IsIso (η (u.sheafPullback A J K)) :=
  have := fun i ↦ (Φ i).isIso_sheafFiber_map_sheafPullback_η u (e i) A
  hΦ.isIso _

end Functor

end CategoryTheory
