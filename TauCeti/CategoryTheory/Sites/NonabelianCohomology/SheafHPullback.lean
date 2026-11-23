/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Pullback
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.SheafH
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Pullback

/-!
# Torsor classes, `H¹` and pullback along a morphism of sites

Let `u : C ⥤ D` be a continuous and representably flat functor between sites `(C, J)` and
`(D, K)` whose sheaf pullback `u^*` on abelian sheaves is exact. For an abelian sheaf `F` on `C`,
pulling back `F`-torsors along the unit `F ⟶ u_* u^* F` gives a map from torsor classes of `F` to
torsor classes of `u^* F` (`CategoryTheory.Sheaf.NonabelianH1.pullback`), and sheaf cohomology has
the pullback `H¹(C, F) → H¹(D, u^* F)` (`CategoryTheory.Sheaf.H.pullback`). This file shows that
the bijection `CategoryTheory.Sheaf.NonabelianH1.equivSheafH` between torsor classes and `H¹`
intertwines the two.

The proof writes a torsor class as the class of a torsor of lifts for an embedding of `F` into an
injective sheaf, pulls back that short exact sequence along the exact functor `u^*`, and compares
the connecting maps: on torsors by `NonabelianH1.pullback_connecting_of_comp_eq`, on cohomology by
`Sheaf.H.pullback_δ`, and in degree zero by `Sheaf.H.zeroMulEquivSections_pullback`.

## Main declarations

* `CategoryTheory.Functor.abelianSheafToGrpSheafUnit u J K F`: the unit `F ⟶ u_* u^* F`, as a
  morphism from the sheaf of groups underlying `F` to the pushforward of the one underlying
  `u^* F`.
* `CategoryTheory.Sheaf.H.zeroMulEquivSections_pullback`: in degree zero, the pullback of
  cohomology sends a global section `s` of `F` to the global section of `u^* F` whose value over
  `u(U)` is the image of `s` over `U` under the unit.
* `CategoryTheory.Sheaf.NonabelianH1.equivSheafH_pullback`, `equivSheafH_symm_pullback`:
  `equivSheafH` commutes with pullback.

## References

* [The Stacks project, Lemma 21.4.3 (03AJ)](https://stacks.math.columbia.edu/tag/03AJ), for the
  bijection between torsor classes and `H¹`.
-/

public noncomputable section

open CategoryTheory Opposite Abelian AddCommGrpCat Limits

universe w₁ w₂ w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

namespace Functor

/-- The unit `F ⟶ u_* u^* F` of the adjunction `u^* ⊣ u_*` on abelian sheaves, as a morphism from
the sheaf of groups underlying `F` to the pushforward of the sheaf of groups underlying
`u^* F`. Use `abelianSheafToGrpSheafUnit_hom_app` to compute it. -/
def abelianSheafToGrpSheafUnit (F : Sheaf J AddCommGrpCat.{w}) :
    (abelianSheafToGrpSheaf J).obj F ⟶ (u.sheafPushforwardContinuous GrpCat.{w} J K).obj
      ((abelianSheafToGrpSheaf K).obj ((u.sheafPullback AddCommGrpCat.{w} J K).obj F)) :=
  ObjectProperty.homMk
    { app U := GrpCat.ofHom ((abelianSheafToGrpSheafObjEquiv _ (u.op.obj U)).toMonoidHom.comp
        ((AddMonoidHom.toMultiplicative
          (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom.app U).hom).comp
            (abelianSheafToGrpSheafObjEquiv F U).symm.toMonoidHom))
      naturality U V f := by
        ext x
        obtain ⟨a, rfl⟩ := (abelianSheafToGrpSheafObjEquiv F U).surjective x
        -- Unfold the components and the restriction maps of the pushforward.
        change abelianSheafToGrpSheafObjEquiv _ (u.op.obj V) (.ofAdd
            (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom.app V
              ((abelianSheafToGrpSheafObjEquiv F V).symm (((abelianSheafToGrpSheaf J).obj F).obj.map
                f (abelianSheafToGrpSheafObjEquiv F U a))).toAdd)) =
          ((abelianSheafToGrpSheaf K).obj ((u.sheafPullback AddCommGrpCat.{w} J K).obj F)).obj.map
            (u.map f.unop).op (abelianSheafToGrpSheafObjEquiv _ (u.op.obj U) (.ofAdd
              (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom.app U
                ((abelianSheafToGrpSheafObjEquiv F U).symm
                  (abelianSheafToGrpSheafObjEquiv F U a)).toAdd)))
        simp only [abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv,
          MulEquiv.symm_apply_apply, toAdd_ofAdd]
        exact (congrArg (fun b ↦ abelianSheafToGrpSheafObjEquiv _ (u.op.obj V) (.ofAdd b))
          (NatTrans.naturality_apply
            ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom f a.toAdd)).trans
          (abelianSheafToGrpSheaf_map_abelianSheafToGrpSheafObjEquiv
            ((u.sheafPullback AddCommGrpCat.{w} J K).obj F) (u.map f.unop).op _).symm }

/-- The unit `F ⟶ u_* u^* F` on the underlying sheaves of groups applies the unit to sections. -/
@[simp]
lemma abelianSheafToGrpSheafUnit_hom_app (F : Sheaf J AddCommGrpCat.{w}) (U : Cᵒᵖ)
    (a : Multiplicative (F.obj.obj U)) :
    (u.abelianSheafToGrpSheafUnit J K F).hom.app U (abelianSheafToGrpSheafObjEquiv F U a) =
      abelianSheafToGrpSheafObjEquiv _ (u.op.obj U) (.ofAdd
        (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom.app U a.toAdd)) :=
  congrArg (fun b ↦ abelianSheafToGrpSheafObjEquiv _ (u.op.obj U) (.ofAdd
    (((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom.app U b.toAdd)))
    ((abelianSheafToGrpSheafObjEquiv F U).symm_apply_apply a)

variable {J K} in
/-- The unit `F ⟶ u_* u^* F` on underlying sheaves of groups is natural in `F`. -/
lemma abelianSheafToGrpSheafUnit_naturality {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) :
    (abelianSheafToGrpSheaf J).map f ≫ u.abelianSheafToGrpSheafUnit J K G =
      u.abelianSheafToGrpSheafUnit J K F ≫ (u.sheafPushforwardContinuous GrpCat.{w} J K).map
        ((abelianSheafToGrpSheaf K).map ((u.sheafPullback AddCommGrpCat.{w} J K).map f)) := by
  ext U x
  obtain ⟨a, rfl⟩ := (abelianSheafToGrpSheafObjEquiv F U).surjective x
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, abelianSheafToGrpSheaf_map_hom_app_abelianSheafToGrpSheafObjEquiv,
    abelianSheafToGrpSheafUnit_hom_app, toAdd_ofAdd]
  exact (congrArg (fun b ↦ abelianSheafToGrpSheafObjEquiv _ (u.op.obj U) (.ofAdd b))
    (ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (·.hom)
      ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.naturality f)) U) a.toAdd)).trans
    (abelianSheafToGrpSheaf_map_hom_app_abelianSheafToGrpSheafObjEquiv
      ((u.sheafPullback AddCommGrpCat.{w} J K).map f) (u.op.obj U) _).symm

end Functor

variable {J K}

namespace Sheaf.H

variable [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  [u.Final] [PreservesFiniteLimits (u.sheafPullback AddCommGrpCat.{w} J K)]

/-- In degree zero, the pullback of cohomology along a morphism of sites, read on global
sections, is the unit `F ⟶ u_* u^* F`: the global section of `u^* F` given by the pullback of a
class `x` has value over `u(U)` the image under the unit of the value over `U` of the global
section of `F` given by `x`. -/
lemma zeroMulEquivSections_pullback (F : Sheaf J AddCommGrpCat.{w}) (x : H F 0) (U : Cᵒᵖ) :
    (zeroMulEquivSections ((u.sheafPullback AddCommGrpCat.{w} J K).obj F)
      (.ofAdd (H.pullback (u.sheafPullback AddCommGrpCat.{w} J K)
        (u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv F 0 x))).val
          (u.op.obj U) =
      (u.abelianSheafToGrpSheafUnit J K F).hom.app U
        ((zeroMulEquivSections F (.ofAdd x)).val U) := by
  obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  rw [zeroMulEquivSections_apply_coe, zeroMulEquivSections_apply_coe, toAdd_ofAdd, toAdd_ofAdd,
    addEquiv₀_pullback, AddEquiv.apply_symm_apply, Functor.abelianSheafToGrpSheafUnit_hom_app,
    toAdd_ofAdd]
  -- Both sides evaluate at `1` morphisms out of the constant presheaf `ℤ` on `C`; compare them
  -- through the description of `ℤ_K ⟶ u^* ℤ_J` by the unit on constant sections.
  have key := u.whiskerLeft_toSheafify_comp_sheafPullbackConstantSheafIso_inv
    AddCommGrpCat.{w} J K (of (ULift ℤ))
  have nat := congrArg (·.hom)
    ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit_naturality f)
  simp only [ObjectProperty.FullSubcategory.comp_hom] at nat
  have h : Functor.whiskerLeft u.op (toSheafify K _ ≫
      ((u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv ≫
        (u.sheafPullback AddCommGrpCat.{w} J K).map f).hom) =
      toSheafify J _ ≫ f.hom ≫
        ((u.sheafAdjunctionContinuous AddCommGrpCat.{w} J K).unit.app F).hom := by
    rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, Functor.whiskerLeft_comp, key]
    exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) nat)
  have inner := ConcreteCategory.congr_hom (NatTrans.congr_app h U) ⟨1⟩
  simp only [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app]
  exact congrArg (fun a ↦ abelianSheafToGrpSheafObjEquiv
    ((u.sheafPullback AddCommGrpCat.{w} J K).obj F) (u.op.obj U) (.ofAdd a)) inner

end Sheaf.H

namespace Sheaf.NonabelianH1

attribute [local instance] final_of_representablyFlat

variable [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w₂} (Sheaf K AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})] [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]
  [RepresentablyFlat u] [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)]
  [PreservesFiniteLimits (u.sheafPullback AddCommGrpCat.{w} J K)]

/-- The bijection `equivSheafH` between torsor classes and `H¹` commutes with pullback along a
morphism of sites: pulling back an `F`-torsor along the unit `F ⟶ u_* u^* F` corresponds to the
pullback `H¹(C, F) → H¹(D, u^* F)` of sheaf cohomology. -/
theorem equivSheafH_pullback (F : Sheaf J AddCommGrpCat.{w})
    (x : NonabelianH1 ((abelianSheafToGrpSheaf J).obj F)) :
    equivSheafH ((u.sheafPullback AddCommGrpCat.{w} J K).obj F)
        (pullback (u.abelianSheafToGrpSheafUnit J K F) x) =
      H.pullback (u.sheafPullback AddCommGrpCat.{w} J K)
        (u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv F 1
          (equivSheafH F x) := by
  have hF := TauCeti.injectiveCokernelSequence_shortExact F
  have hF' := hF.map_of_exact (u.sheafPullback AddCommGrpCat.{w} J K)
  -- Write `x` as the class of the torsor of lifts of a global section `q` of the cokernel of an
  -- injective embedding of `F`, and pull back the short exact sequence along `u^*`.
  obtain ⟨q, rfl⟩ := connecting_surjective_of_injective hF.isGroupExtension x
  rw [pullback_connecting_of_comp_eq hF.isGroupExtension hF'.isGroupExtension
    (u.abelianSheafToGrpSheafUnit J K _) (u.abelianSheafToGrpSheafUnit J K _)
    (u.abelianSheafToGrpSheafUnit J K _) (u.abelianSheafToGrpSheafUnit_naturality _)
    (u.abelianSheafToGrpSheafUnit_naturality _).symm q
    (H.zeroMulEquivSections _ (.ofAdd (H.pullback (u.sheafPullback AddCommGrpCat.{w} J K)
      (u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv _ 0
        ((H.zeroMulEquivSections _).symm q).toAdd))) fun U ↦ ?_]
  · refine (equivSheafH_connecting hF' _).trans ?_
    rw [MulEquiv.symm_apply_apply, toAdd_ofAdd, ← H.pullback_δ _ _ hF]
    exact congrArg _ (equivSheafH_connecting hF q).symm
  · refine Eq.trans ?_ (H.zeroMulEquivSections_pullback u _ _ U).symm
    rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]

/-- The inverse of `equivSheafH` commutes with pullback along a morphism of sites. -/
theorem equivSheafH_symm_pullback (F : Sheaf J AddCommGrpCat.{w}) (z : H F 1) :
    (equivSheafH ((u.sheafPullback AddCommGrpCat.{w} J K).obj F)).symm
        (H.pullback (u.sheafPullback AddCommGrpCat.{w} J K)
          (u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv F 1 z) =
      pullback (u.abelianSheafToGrpSheafUnit J K F) ((equivSheafH F).symm z) := by
  rw [Equiv.symm_apply_eq, equivSheafH_pullback, Equiv.apply_symm_apply]

end Sheaf.NonabelianH1

end CategoryTheory
