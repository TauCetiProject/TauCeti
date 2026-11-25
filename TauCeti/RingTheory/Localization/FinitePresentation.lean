/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.Category.CommAlgCat.Localization

/-!
# Factoring finitely presented maps through principal localizations

A map from a finitely presented algebra to a localization factors through the inversion of
one denominator. The base ring of the presentation may differ from the ring being localized.
This is the affine finite-presentation argument for spreading out from a local scheme.

We use the filtered presentation of a localization by principal localizations and Mathlib's
finite-presentation factorization theorem for filtered colimits of rings (Stacks 05N9).
-/

public section

open CategoryTheory Limits

universe u

namespace RingHom

/-- A map from a finitely presented algebra to `M⁻¹R` factors, over its base, through
`R[1/∏ s]` for some finite set `s` of elements of `M`, as a stage of the filtered presentation
`Submonoid.localizationAwayRingCocone`. The base map `a` need not be injective or of finite
type. -/
theorem exists_factorization_localizationAwayRingCocone
    {A B R S : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    [Algebra R S] (f : A →+* B) (hf : f.FinitePresentation)
    (M : Submonoid R) [IsLocalization M S] (a : A →+* R) (g : B →+* S)
    (h : g.comp f = (algebraMap R S).comp a) :
    ∃ s : Finset M, ∃ g' : B →+* M.localizationAwayDiagram.obj s,
      g'.comp f = (algebraMap R (M.localizationAwayDiagram.obj s)).comp a ∧
      ((M.localizationAwayRingCocone S).ι.app s).hom.comp g' = g := by
  let D := M.localizationAwayDiagram
  let α : (Functor.const (Finset M)).obj (CommRingCat.of A) ⟶
      D ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u} :=
    { app := fun s ↦ CommRingCat.ofHom ((algebraMap R (D.obj s)).comp a)
      naturality := fun s t i ↦ by
        ext x
        exact ((D.map i).hom.commutes (a x)).symm }
  obtain ⟨s, g', hg', hg⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (CommRingCat.of A) _ α (CommRingCat.ofHom f) (M.localizationAwayRingCocone S)
      (M.localizationAwayRingCoconeIsColimit S) hf (CommRingCat.ofHom g) (fun s ↦ by
        ext x
        exact (congrArg (fun k : A →+* S ↦ k x) h).trans
          (RingHom.congr_fun (M.localizationAwayRingCocone_ι_app_comp_algebraMap S s) (a x)).symm)
  exact ⟨s, g'.hom, congrArg CommRingCat.Hom.hom hg', (congrArg CommRingCat.Hom.hom hg).symm⟩

/-- A map from a finitely presented algebra to `M⁻¹R` factors, over its base, through `R[1/s]`
for some `s ∈ M`. The base map `a` need not be injective or of finite type. -/
theorem exists_factorization_localizationAway
    {A B R S : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    [Algebra R S] (f : A →+* B) (hf : f.FinitePresentation)
    (M : Submonoid R) [IsLocalization M S] (a : A →+* R) (g : B →+* S)
    (h : g.comp f = (algebraMap R S).comp a) :
    ∃ s : M, ∃ g' : B →+* Localization.Away (s : R),
      g'.comp f = (algebraMap R (Localization.Away (s : R))).comp a ∧
      (IsLocalization.Away.lift (S := Localization.Away (s : R)) (s : R)
        (g := algebraMap R S) (IsLocalization.map_units S s)).comp g' = g := by
  obtain ⟨s, g', hg', hg⟩ := f.exists_factorization_localizationAwayRingCocone hf M a g h
  let e := (eqToHom (M.localizationAwayDiagram_obj s)).hom.toRingHom
  refine ⟨⟨∏ x ∈ s, (x : R), M.prod_mem fun x _ ↦ x.property⟩, e.comp g', ?_, ?_⟩
  · ext x
    exact (congrArg (fun k : A →+* M.localizationAwayDiagram.obj s ↦ e (k x)) hg').trans
      ((eqToHom (M.localizationAwayDiagram_obj s)).hom.commutes (a x))
  · have hleg := congrArg (fun k ↦ eqToHom (M.localizationAwayDiagram_obj s) ≫ k)
      (M.localizationAwayCocone_ι_app S s)
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] at hleg
    rw [← hg, Submonoid.localizationAwayRingCocone_ι_app_hom, hleg]
    ext x
    simp [e]

end RingHom
