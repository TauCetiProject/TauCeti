/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Injective
public import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra

import TauCeti.Algebra.Category.ModuleCat.Algebra

/-!
# Enough injectives for finitely generated modules over an Artin algebra

The finitely generated injective envelopes obtained from Matlis duality give enough injectives
in the category of finitely generated modules over an Artin algebra.
-/

public section

open CategoryTheory

universe u v w

namespace TauCeti.FGModuleCat

/-- The category of finitely generated modules over an Artin algebra has enough injectives. -/
theorem enoughInjectives_of_artinAlgebra (R : Type u) [CommRing R] [IsArtinianRing R]
    (A : Type v) [Ring A] [Algebra R A] [Module.Finite R A] :
    EnoughInjectives (FGModuleCat.{max u v w} A) where
  presentation X := by
    let := ModuleCat.moduleOfAlgebra R X.obj
    let := ModuleCat.isScalarTower_moduleOfAlgebra R X.obj
    obtain ⟨Q, _, _, _, i, hi⟩ := exists_isInjectiveEnvelope_finite R (A := A) X.obj
    -- Take the hull in the same universe as X by lifting the codomain.
    let e : ULift.{w} Q ≃ₗ[A] Q := ULift.moduleEquiv
    let f : X ⟶ FGModuleCat.of A (ULift.{w} Q) := FGModuleCat.ofHom (e.symm.toLinearMap ∘ₗ i)
    have : Module.Injective A (ULift.{w} Q) :=
      Module.ulift_injective_of_injective A hi.moduleInjective
    exact ⟨{
      J := FGModuleCat.of A (ULift.{w} Q)
      f := f
      injective := FGModuleCat.injective_of_moduleInjective _
      mono := ConcreteCategory.mono_of_injective f (e.symm.injective.comp hi.injective) }⟩

end TauCeti.FGModuleCat
