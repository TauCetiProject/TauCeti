/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.DividedPowerScheme.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.OpenImmersion

/-!
# Restricting divided power schemes along open immersions

The section ring isomorphisms of an open immersion transport the divided powers to the
inverse image ideal sheaf. The open immersion then becomes a morphism of divided power schemes,
and the closed fibre restricts by the same pullback square as the ideal sheaf.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.IdealSheafData

universe u

namespace TauCeti.DividedPowerScheme

noncomputable section

variable (X : DividedPowerScheme.{u}) {T : Scheme.{u}} (f : T ⟶ X.scheme) [IsOpenImmersion f]

/-- Divided powers on the preimage ideal over an open of the source of an open immersion. -/
def comapDividedPowers (U : T.Opens) : DividedPowers ((X.ideal.comap f).sections U) :=
  DividedPowers.ofRingEquiv (e := (f.appIso U).commRingCatIsoToRingEquiv)
    (sections_comap_of_isOpenImmersion X.ideal f U).symm
    (X.dividedPowers (f ''ᵁ U))

/-- The transported divided powers are computed by applying the section isomorphism to
the original divided powers. -/
@[simp]
theorem comapDividedPowers_dpow (U : T.Opens) (n : ℕ) (s : Γ(X.scheme, f ''ᵁ U)) :
    (X.comapDividedPowers f U).dpow n ((f.appIso U).hom s) =
      (f.appIso U).hom ((X.dividedPowers (f ''ᵁ U)).dpow n s) := by
  unfold comapDividedPowers
  have h := DividedPowers.ofRingEquiv_dpow_apply (e := (f.appIso U).commRingCatIsoToRingEquiv)
    (sections_comap_of_isOpenImmersion X.ideal f U).symm
    (X.dividedPowers (f ''ᵁ U)) (n := n) (a := s)
  rw [← RingEquiv.coe_toRingHom, Iso.commRingCatIsoToRingEquiv_toRingHom] at h
  exact h

/-- The ring isomorphism on an open immersion preserves the transported divided powers. -/
theorem isDPMorphism_appIso (U : T.Opens) :
    DividedPowers.IsDPMorphism (X.dividedPowers (f ''ᵁ U)) (X.comapDividedPowers f U)
      (f.appIso U).hom.hom where
  ideal_comp := (sections_comap_of_isOpenImmersion X.ideal f U).ge
  dpow_comp s _ := X.comapDividedPowers_dpow f U _ s

/-- An open subscheme of a divided power scheme carries the restricted divided powers. -/
@[expose, implicit_reducible] def comapOfIsOpenImmersion : DividedPowerScheme.{u} where
  scheme := T
  ideal := X.ideal.comap f
  dividedPowers := X.comapDividedPowers f
  isDPMorphism_res {U V} i := by
    refine ⟨Ideal.map_le_iff_le_comap.mpr
      (fun _ hs ↦ (X.ideal.comap f).map_mem_sections i hs), ?_⟩
    intro n x hx
    obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.appIso U).hom).surjective x
    have hs := (X.ideal.appIso_hom_mem_sections_comap_iff f s).mp hx
    simp only [comapDividedPowers_dpow, ← f.appIso_hom_naturality_apply,
      (X.isDPMorphism_res (f.opensFunctor.map i)).map_dpow hs]

/-- The ambient scheme of the restricted divided power scheme is the source of the immersion. -/
@[simp]
theorem comapOfIsOpenImmersion_scheme : (X.comapOfIsOpenImmersion f).scheme = T := (rfl)

/-- The ideal of the restricted divided power scheme is the pullback of the original ideal. -/
@[simp]
theorem comapOfIsOpenImmersion_ideal : (X.comapOfIsOpenImmersion f).ideal = X.ideal.comap f := (rfl)

/-- The divided powers of the restricted scheme are transported by the section isomorphisms. -/
@[simp]
theorem comapOfIsOpenImmersion_dividedPowers (U : T.Opens) :
    (X.comapOfIsOpenImmersion f).dividedPowers U = X.comapDividedPowers f U := (rfl)

/-- An open immersion into a divided power scheme is a divided power morphism for the
restricted structure. -/
def comapHom : X.comapOfIsOpenImmersion f ⟶ X :=
  Hom.mkOfApp f fun U ↦ by
    let V := f ⁻¹ᵁ U
    let i : (f ''ᵁ V) ⟶ U := homOfLE (Set.image_preimage_subset _ _)
    have h : X.scheme.presheaf.map i.op ≫ (f.appIso V).hom = f.app U :=
      (Iso.eq_comp_inv _).mp (f.app_appIso_inv U).symm
    rw [← h, CommRingCat.hom_comp]
    exact (X.isDPMorphism_appIso f V).comp _ (X.isDPMorphism_res i)

/-- The underlying morphism of the restricted divided power scheme is the given open immersion. -/
@[simp]
theorem comapHom_hom : (X.comapHom f).hom = f := Hom.mkOfApp_hom _ _

/-- The closed fibre of the restriction is the inverse image of the original closed fibre. -/
theorem isPullback_comapHom_closedFiberι :
    IsPullback (X.comapHom f).closedFiberMap (X.comapOfIsOpenImmersion f).closedFiberι
      X.closedFiberι f :=
  (isPullback_of_isClosedImmersion _ _ _ _ (by simp) (by simp)).flip

/-- Restriction along an open immersion preserves divided power thickenings. -/
instance isPDThickening_comapOfIsOpenImmersion [X.IsPDThickening] :
    (X.comapOfIsOpenImmersion f).IsPDThickening :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsThickening)
    (X.isPullback_comapHom_closedFiberι f) ‹X.IsPDThickening›

end

end TauCeti.DividedPowerScheme
