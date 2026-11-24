/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.NullSequence.Discrete.Families
public import TauCeti.Condensed.Light.Solid.Basic

/-!
# Discrete light condensed modules are solid

Compactness makes a family of null sequences with discrete coefficients uniformly finitely
supported. The inverse of one minus the shift is consequently the finite tail sum.

This generalizes the integer case of Juan Esteban Rodríguez Camargo, *Notes on Solid Geometry*,
[Theorem 3.2.4(1) and its proof in Proposition 3.2.5](https://arxiv.org/abs/2603.03012v1),
Section 3.2, to discrete modules over any commutative ring.
-/

public section

universe u

open CategoryTheory Category MonoidalCategory LightCondensed Opposite TauCeti

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The locally constant realization of every discrete coefficient module is solid. -/
lemma isLightSolid_locallyConstant (M : ModuleCat.{u} R) :
    IsLightSolid ((LightCondMod.LocallyConstant.functor R).obj M) := by
  rw [isLightSolid_iff_bijective]
  intro S
  let E := nullSeqDiscreteTensorHomEquivFinsupp M S
  have h : E ∘ (fun g ↦ g - (nullShift R ▷ _) ≫ g) = Finsupp.oneSubShiftEquiv ∘ E := by
    funext g
    exact nullSeqDiscreteTensorHomEquivFinsupp_difference M S g
  have hb : Function.Bijective (E ∘ (fun g ↦ g - (nullShift R ▷ _) ≫ g)) := by
    rw [h]
    exact Finsupp.oneSubShiftEquiv.bijective.comp E.bijective
  exact (Function.Bijective.of_comp_iff' E.bijective _).mp hb

/-- Every discrete light condensed module is solid. -/
lemma isLightSolid_discrete (M : ModuleCat.{u} R) :
    IsLightSolid ((LightCondensed.discrete (ModuleCat R)).obj M) :=
  IsLightSolid.prop_of_iso
    ((LightCondMod.LocallyConstant.functorIsoDiscrete R).app M) (isLightSolid_locallyConstant M)

end ModuleCat
