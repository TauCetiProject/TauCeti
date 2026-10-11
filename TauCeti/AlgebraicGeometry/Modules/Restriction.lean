/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Restriction of module sheaves preserves limits

Restriction along an open immersion has a left adjoint, given by sheafifying the corresponding
presheaf pullback along the functor taking an open to its image. It therefore preserves limits,
in addition to preserving colimits by Mathlib's restriction--pushforward adjunction. In
particular, ambient kernels can be computed after restriction to an open subscheme.

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
