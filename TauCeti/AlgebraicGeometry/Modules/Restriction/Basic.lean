/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExtensionByZero
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Restriction of module sheaves preserves limits, injectives, and free modules

Restriction along an open immersion has a left adjoint, given by sheafifying the corresponding
presheaf pullback along the functor taking an open to its image. It therefore preserves limits,
in addition to preserving colimits by Mathlib's restriction--pushforward adjunction. In
particular, ambient kernels can be computed after restriction to an open subscheme. Pullback
along an open immersion also preserves limits, since it is naturally isomorphic to restriction.

Restriction preserves injective module sheaves because its left adjoint, extension by zero,
is exact. Thus injective resolutions may be restricted to an open subscheme without losing
injectivity of their terms. Being a left adjoint that preserves the structure sheaf, restriction
also sends free module sheaves to free module sheaves on the same generators.

A module sheaf is zero exactly when its restrictions to the members of an open cover are zero
(`AlgebraicGeometry.Scheme.Modules.isZero_iff_of_iSup_eq_top`), by the sheaf condition.

The adjunction is Mathlib's `SheafOfModules.PullbackConstruction.adjunction`; the underlying
presheaf right adjoint is `PresheafOfModules.instIsRightAdjointPushforward`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- Restriction of module sheaves along an open immersion is a right adjoint, so it preserves
limits. Its left adjoint is the sheafified presheaf pullback along the open-image functor. -/
noncomputable instance _root_.AlgebraicGeometry.Scheme.Modules.restrictFunctorIsRightAdjoint
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion f] :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).IsRightAdjoint := by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  let φ : X.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous RingCat _ _).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  -- The sheaf-pushforward projection hides its site functor from instance search.
  -- Instantiate the existing presheaf right adjoint with that functor explicitly.
  have := PresheafOfModules.instIsRightAdjointPushforward (F := f.opensFunctor) φ.hom
  exact inferInstanceAs (SheafOfModules.pushforward φ).IsRightAdjoint

/-- Restriction along an open immersion is additive. In particular it preserves the zero
morphisms used in kernel diagrams. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.restrictFunctorAdditive
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion f] :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).Additive :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctor f).additive_of_preserves_binary_products

end TauCeti

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Limits

/-- Restriction to an open subscheme preserves injective module sheaves. In particular,
restricting the terms of an injective resolution gives injective terms. -/
private instance restrictFunctorPreservesInjectiveObjectsInclusion {X : Scheme.{u}} (U : X.Opens) :
    (restrictFunctor U.ι).PreservesInjectiveObjects where
  injective_obj {M} hM := by
    exact Injective.of_iso ((overFunctorEquiv U).app M)
      ((overEquiv U).functor.injective_obj_of_injective
        ((SheafOfModules.overFunctor X.ringCatSheaf U).injective_obj_of_injective hM))

/-- Restriction along any open immersion preserves injective module sheaves. -/
instance (priority := low) restrictFunctorPreservesInjectiveObjects {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctor f).PreservesInjectiveObjects where
  injective_obj {M} hM := by
    -- Factor through the open image. Restriction along the intervening isomorphism
    -- is an equivalence, with comparison isomorphisms supplied by functoriality.
    let e := f.isoOpensRange
    let E : f.opensRange.toScheme.Modules ≌ X.Modules :=
      CategoryTheory.Equivalence.mk (restrictFunctor e.hom) (restrictFunctor e.inv)
        ((restrictFunctorId).symm ≪≫ restrictFunctorCongr e.inv_hom_id.symm ≪≫
          restrictFunctorComp e.inv e.hom)
        ((restrictFunctorComp e.hom e.inv).symm ≪≫
          restrictFunctorCongr e.hom_inv_id ≪≫ restrictFunctorId)
    have : (restrictFunctor e.hom).PreservesInjectiveObjects :=
      inferInstanceAs E.functor.PreservesInjectiveObjects
    let i : restrictFunctor f ≅ restrictFunctor f.opensRange.ι ⋙ restrictFunctor e.hom :=
      restrictFunctorCongr f.isoOpensRange_hom_ι.symm ≪≫
        restrictFunctorComp e.hom f.opensRange.ι
    exact Injective.of_iso (i.app M).symm
      ((restrictFunctor e.hom).injective_obj_of_injective
        ((restrictFunctor f.opensRange.ι).injective_obj_of_injective hM))

/-- Pullback along an open immersion preserves limits, since it is restriction. -/
noncomputable instance
    _root_.AlgebraicGeometry.Scheme.Hom.preservesLimits_pullback_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesLimits (pullback f) :=
  preservesLimits_of_natIso (restrictFunctorIsoPullback f)

/-- Restriction along an open immersion sends the free module on `ι` to the free module on `ι`. -/
noncomputable def restrictFreeIso {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (ι : Type u) :
    restrict (SheafOfModules.free (R := X.ringCatSheaf) ι) f ≅
      SheafOfModules.free (R := Y.ringCatSheaf) ι :=
  -- The functor is rebound with its type as a functor between categories of sheaves of modules,
  -- where `SheafOfModules.mapFreeIso` seeks its colimit-preservation instance.
  let G : SheafOfModules X.ringCatSheaf ⥤ SheafOfModules Y.ringCatSheaf := restrictFunctor f
  have : PreservesColimitsOfShape (Discrete ι) G :=
    (restrictAdjunction f).leftAdjoint_preservesColimits.preservesColimitsOfShape
  (SheafOfModules.mapFreeIso G ι (restrictUnitIso f).symm).symm

/-- A section of `M` over the image of an open of `U` is zero when the restriction `M|_U` is zero.
-/
private lemma eq_zero_of_isZero_restrict {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (h : IsZero (M.restrict U.ι)) (W : U.toScheme.Opens) (s : Γ(M, U.ι ''ᵁ W)) : s = 0 := by
  have h₀ : (M.restrictAppIso U.ι W).inv s = 0 := by
    simpa using ConcreteCategory.congr_hom
      congr(Hom.app $(h.eq_of_src (𝟙 _) 0) W) ((M.restrictAppIso U.ι W).inv s)
  rw [← Iso.inv_hom_id_apply (M.restrictAppIso U.ι W) s, h₀, map_zero]

/-- A sheaf of modules on a scheme is zero exactly when its restrictions to the members of an open
cover are zero. -/
theorem isZero_iff_of_iSup_eq_top {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (M : X.Modules) :
    IsZero M ↔ ∀ i, IsZero (M.restrict (U i).ι) := by
  refine ⟨fun h i ↦ (restrictFunctor (U i).ι).map_isZero h, fun h ↦ ?_⟩
  rw [IsZero.iff_id_eq_zero]
  refine hom_ext _ _ fun V ↦ ?_
  ext s
  simp only [Hom.id_app, Hom.zero_app, AddCommGrpCat.hom_id, AddCommGrpCat.hom_zero,
    AddMonoidHom.id_apply, AddMonoidHom.zero_apply]
  -- `s` vanishes on each `V ⊓ U i`, the image of the preimage of `V` in `U i`
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    (fun i ↦ (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ V)) V (fun i ↦ homOfLE ((U i).ι.image_preimage_le V))
    ?_ s 0 fun i ↦ ?_
  · simp_rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      ← iSup_inf_eq, hU, top_inf_eq, le_rfl]
  · rw [map_zero]
    exact eq_zero_of_isZero_restrict (h i) _ _

end AlgebraicGeometry.Scheme.Modules
