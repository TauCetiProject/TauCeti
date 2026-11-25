/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Abelian.Pullback
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Pullback
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.SheafH.Basic
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
`Sheaf.H.pullback_δ`, and in degree zero by `Sheaf.H.zeroMulEquivSections_pullback`. The torsors
are pulled back along `CategoryTheory.Functor.abelianSheafToGrpSheafUnit u J K`, the unit
`F ⟶ u_* u^* F` on the underlying sheaves of groups.

## Main declarations

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
      ((u.abelianSheafToGrpSheafUnit J K).app F).hom.app U
        ((zeroMulEquivSections F (.ofAdd x)).val U) := by
  obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  rw [zeroMulEquivSections_apply_coe, zeroMulEquivSections_apply_coe, toAdd_ofAdd, toAdd_ofAdd,
    addEquiv₀_pullback, AddEquiv.apply_symm_apply, Functor.abelianSheafToGrpSheafUnit_app_hom_app,
    toAdd_ofAdd]
  simp only [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app]
  -- Both sides evaluate at `1` morphisms out of the constant presheaf `ℤ` on `C`, which agree by
  -- the description of the pulled-back morphism by the unit.
  exact congrArg (fun a ↦ abelianSheafToGrpSheafObjEquiv
    ((u.sheafPullback AddCommGrpCat.{w} J K).obj F) (u.op.obj U) (.ofAdd a))
    (ConcreteCategory.congr_hom
      (NatTrans.congr_app (whiskerLeft_toSheafify_comp_sheafPullback_map (K := K) u F f) U) ⟨1⟩)

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
        (pullback ((u.abelianSheafToGrpSheafUnit J K).app F) x) =
      H.pullback (u.sheafPullback AddCommGrpCat.{w} J K)
        (u.sheafPullbackConstantSheafIso AddCommGrpCat.{w} J K (of (ULift ℤ))).inv F 1
          (equivSheafH F x) := by
  have hF := TauCeti.injectiveCokernelSequence_shortExact F
  have hF' := hF.map_of_exact (u.sheafPullback AddCommGrpCat.{w} J K)
  -- Write `x` as the class of the torsor of lifts of a global section `q` of the cokernel of an
  -- injective embedding of `F`, and pull back the short exact sequence along `u^*`.
  obtain ⟨q, rfl⟩ := connecting_surjective_of_injective hF.isGroupExtension x
  rw [pullback_connecting_of_comp_eq hF.isGroupExtension hF'.isGroupExtension
    ((u.abelianSheafToGrpSheafUnit J K).app _) ((u.abelianSheafToGrpSheafUnit J K).app _)
    ((u.abelianSheafToGrpSheafUnit J K).app _) ((u.abelianSheafToGrpSheafUnit J K).naturality _)
    ((u.abelianSheafToGrpSheafUnit J K).naturality _).symm q
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
      pullback ((u.abelianSheafToGrpSheafUnit J K).app F) ((equivSheafH F).symm z) := by
  rw [Equiv.symm_apply_eq, equivSheafH_pullback, Equiv.apply_symm_apply]

end Sheaf.NonabelianH1

end CategoryTheory
