/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExtensionByZero

/-!
# Restriction of module sheaves preserves limits and injectives

Restriction along an open immersion has a left adjoint, given by sheafifying the corresponding
presheaf pullback along the functor taking an open to its image. It therefore preserves limits,
in addition to preserving colimits by Mathlib's restriction--pushforward adjunction. In
particular, ambient kernels can be computed after restriction to an open subscheme. Pullback
along an open immersion also preserves limits, since it is naturally isomorphic to restriction.

Restriction preserves injective module sheaves because its left adjoint, extension by zero,
is exact. Thus injective resolutions may be restricted to an open subscheme without losing
injectivity of their terms.

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

end AlgebraicGeometry.Scheme.Modules
