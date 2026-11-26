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

/-- The ring isomorphism on an open immersion preserves the transported divided powers. -/
theorem isDPMorphism_appIso (U : T.Opens) :
    DividedPowers.IsDPMorphism (X.dividedPowers (f ''ᵁ U)) (X.comapDividedPowers f U)
      (f.appIso U).hom.hom where
  ideal_comp := (sections_comap_of_isOpenImmersion X.ideal f U).ge
  dpow_comp _ _ := by
    unfold comapDividedPowers
    exact DividedPowers.ofRingEquiv_dpow_apply _ _

/-- An open subscheme of a divided power scheme carries the restricted divided powers. -/
abbrev comapOfIsOpenImmersion : DividedPowerScheme.{u} where
  scheme := T
  ideal := X.ideal.comap f
  dividedPowers := X.comapDividedPowers f
  isDPMorphism_res {U V} i := by
    refine ⟨Ideal.map_le_iff_le_comap.mpr
      (fun _ hs ↦ (X.ideal.comap f).map_mem_sections i hs), ?_⟩
    intro n x hx
    let e := (f.appIso U).commRingCatIsoToRingEquiv
    obtain ⟨s, rfl⟩ := e.surjective x
    have he : (e : Γ(X.scheme, f ''ᵁ U) →+* Γ(T, U)) = (f.appIso U).hom.hom := rfl
    have he_apply (a : Γ(X.scheme, f ''ᵁ U)) : e a = (f.appIso U).hom a :=
      congrArg (fun g : Γ(X.scheme, f ''ᵁ U) →+* Γ(T, U) ↦ g a) he
    have hs : s ∈ X.ideal.sections (f ''ᵁ U) := by
      rw [sections_comap_of_isOpenImmersion, ← he, Ideal.map_comap_of_equiv e, Ideal.mem_comap,
        RingEquiv.symm_apply_apply] at hx
      exact hx
    have hnat (a : Γ(X.scheme, f ''ᵁ U)) :
        (f.appIso V).hom (X.scheme.presheaf.map (f.opensFunctor.map i).op a) =
          T.presheaf.map i.op (e a) := by
      simpa only [CommRingCat.comp_apply, Quiver.Hom.unop_op, he_apply] using
        congrArg (fun g : Γ(X.scheme, f ''ᵁ U) ⟶ Γ(T, V) ↦ g a)
          (f.appIso_hom_naturality i.op)
    rw [← hnat, ← (X.isDPMorphism_appIso f V).map_dpow
      (X.ideal.map_mem_sections (f.opensFunctor.map i) hs),
      ← (X.isDPMorphism_res (f.opensFunctor.map i)).map_dpow hs, hnat]
    apply congrArg (T.presheaf.map i.op).hom
    simpa only [he_apply] using (X.isDPMorphism_appIso f U).map_dpow (n := n) hs

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
      X.closedFiberι f := by
  refine IsPullback.of_iso_pullback ⟨by rw [Hom.closedFiberMap_comp_ι, comapHom_hom]⟩
    ((X.ideal.comapIso f) ≪≫ pullbackSymmetry f X.closedFiberι) ?_ ?_
  · rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
    rw [← cancel_mono X.closedFiberι, Category.assoc, ← pullback.condition, ← Category.assoc,
      comapIso_hom_fst, Hom.closedFiberMap_comp_ι, comapHom_hom]
  · rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact X.ideal.comapIso_hom_fst f

/-- Restriction along an open immersion preserves divided power thickenings. -/
theorem IsPDThickening.comapOfIsOpenImmersion {X : DividedPowerScheme.{u}}
    (hX : X.IsPDThickening) {T : Scheme.{u}} (f : T ⟶ X.scheme) [IsOpenImmersion f] :
    (X.comapOfIsOpenImmersion f).IsPDThickening :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsThickening)
    (X.isPullback_comapHom_closedFiberι f) hX

end

end TauCeti.DividedPowerScheme
