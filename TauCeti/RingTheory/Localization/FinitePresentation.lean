/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.Basic
import TauCeti.Algebra.Category.CommAlgCat.FilteredColimits
-- The cocone and diagram definitions identify the ring maps in the factorization below.
import all TauCeti.Algebra.Category.CommAlgCat.Localization

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
  classical
  let U := forget₂ (CommAlgCat.{u} R) CommRingCat.{u}
  let D := M.localizationAwayDiagram
  let c := M.localizationAwayCocone S
  -- Forgetting the algebra structure preserves this filtered colimit: the forgetful functor
  -- to types preserves it, and the forgetful functor from rings to types reflects it.
  have : PreservesColimitsOfShape (Finset M) (U ⋙ forget CommRingCat) :=
    preservesColimitsOfShape_of_natIso (eqToIso HasForget₂.forget_comp).symm
  have : ReflectsColimit (D ⋙ U) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  have : PreservesColimit D U :=
    preservesColimit_of_reflects_of_preserves U (forget CommRingCat)
  let α : (Functor.const (Finset M)).obj (CommRingCat.of A) ⟶ D ⋙ U :=
    { app := fun s ↦ CommRingCat.ofHom ((algebraMap R (D.obj s)).comp a)
      naturality := fun s t i ↦ by
        ext x
        exact ((D.map i).hom.commutes (a x)).symm }
  obtain ⟨s, g', hg', hg⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (CommRingCat.of A) (D ⋙ U) α (CommRingCat.ofHom f) (U.mapCocone c)
      (isColimitOfPreserves U (M.localizationAwayCoconeIsColimit S)) hf
      (CommRingCat.ofHom g) (fun s ↦ by
        ext x
        exact (congrArg (fun k : A →+* S ↦ k x) h).trans
          ((c.ι.app s).hom.commutes (a x)).symm)
  refine ⟨⟨∏ x ∈ s, (x : R), M.prod_mem fun x _ ↦ x.property⟩, g'.hom, ?_, ?_⟩
  · exact congrArg CommRingCat.Hom.hom hg'
  · exact (congrArg CommRingCat.Hom.hom hg).symm

end RingHom
