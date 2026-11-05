/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Topology.Sheaves.LocallySurjective
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Basic

/-!
# The thickenings of the formal spectrum

For an ideal of definition `J` of an adic ring `A`, the ordinary spectrum `Spec (A ⧸ J)`
embeds into the formal spectrum `Spf A`. This file constructs that morphism of locally
ringed spaces. Its underlying map is a homeomorphism, and its sheaf map is the canonical
projection to the quotient structure sheaf. This projection is surjective on basic opens,
hence on stalks. Thus these are actual quotient thickenings of the formal spectrum.

The construction works for any ideal of definition, without a noetherianity or finite
generation assumption on `J`. It supplies the quotient morphisms used to recover formal
schemes from their infinitesimal thickenings.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*,
  Ch. I, 10.1.2 and 10.3.2.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

namespace TauCeti.FormalScheme.Spf

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {I J K : Ideal A}

/-- Projection to an infinitesimal thickening is surjective on every basic open. -/
theorem quotientProjection_app_basicOpen_surjective (hI : IsAdic I) (f : A) (n : ℕ) :
    Function.Surjective ((quotientProjection hI n).hom.app (op (basicOpen f))) := by
  have h : Function.Surjective
      ((basicOpenSectionsAdicCompletionIso hI f).hom ≫ CommRingCat.ofHom
        (AdicCompletion.evalₐ (I.map (algebraMap A (Localization.Away f))) (n + 1)).toRingHom) :=
    (AdicCompletion.surjective_evalₐ _ _).comp
      (ConcreteCategory.bijective_of_isIso (basicOpenSectionsAdicCompletionIso hI f).hom).surjective
  simp only [AlgHom.toRingHom_eq_coe] at h
  rw [basicOpenSectionsAdicCompletionIso_hom_comp_evalₐ] at h
  intro s
  obtain ⟨x, hx⟩ := h ((Ideal.quotEquivOfEq (Ideal.map_pow _ I (n + 1)))
    ((quotientSheafBasicOpenIso (is_ideal_adic_pow hI n.succ_pos) f).hom s))
  refine ⟨x, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (quotientSheafBasicOpenIso (is_ideal_adic_pow hI n.succ_pos) f).hom).injective
  exact (Ideal.quotEquivOfEq (Ideal.map_pow _ I (n + 1))).injective hx

omit [IsTopologicalRing A] in
/-- Reduction between two ideals of definition is surjective on every basic open. -/
theorem quotientTransition_app_basicOpen_surjective (hJ : IsAdic J) (hK : IsAdic K)
    (hJK : J ≤ K) (f : A) :
    Function.Surjective ((quotientTransition hJ hK hJK).hom.app (op (basicOpen f))) := by
  have h : Function.Surjective ((quotientSheafBasicOpenIso hJ f).hom ≫
      CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.map_mono hJK))) :=
    (Ideal.Quotient.factor_surjective (Ideal.map_mono hJK)).comp
      (ConcreteCategory.bijective_of_isIso (quotientSheafBasicOpenIso hJ f).hom).surjective
  rw [← quotientTransition_app_basicOpen_comp_quotientSheafBasicOpenIso_hom hJ hK hJK f] at h
  intro s
  obtain ⟨x, hx⟩ := h ((quotientSheafBasicOpenIso hK f).hom s)
  exact ⟨x, (ConcreteCategory.bijective_of_isIso (quotientSheafBasicOpenIso hK f).hom).injective hx⟩

/-- The projection to the structure sheaf modulo any ideal of definition is surjective on
basic opens. This does not assert surjectivity on arbitrary opens. -/
theorem toQuotientSheaf_app_basicOpen_surjective (hI : IsAdic I) (hJ : IsAdic J) (f : A) :
    Function.Surjective ((toQuotientSheaf hI hJ).hom.app (op (basicOpen f))) := by
  obtain ⟨n, hn⟩ := hI.exists_pow_succ_le (by simpa using hJ.isOpen_pow 1)
  rw [toQuotientSheaf_eq hI hJ hn]
  exact (quotientTransition_app_basicOpen_surjective _ hJ hn f).comp
    (quotientProjection_app_basicOpen_surjective hI f n)

/-- The structure-sheaf projection to an ideal-of-definition quotient is locally surjective. -/
theorem toQuotientSheaf_isLocallySurjective (hI : IsAdic I) (hJ : IsAdic J) :
    TopCat.Presheaf.IsLocallySurjective (toQuotientSheaf hI hJ).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U s p hp
  obtain ⟨V, ⟨f, rfl⟩, hpf, hfU⟩ := (Opens.isBasis_iff_nbhd.mp isBasis_basicOpen) hp
  obtain ⟨t, ht⟩ := toQuotientSheaf_app_basicOpen_surjective hI hJ f
    ((quotientSheaf hJ).obj.map (homOfLE hfU).op s)
  exact ⟨basicOpen f, hfU, ⟨t, ht⟩, hpf⟩

variable [IsAdicRing A]

/-- The canonical quotient inclusion `Spec (A ⧸ J) → Spf A`, as a morphism of presheafed spaces.
Its sheaf component is `toQuotientSheaf`. -/
private noncomputable def quotientPresheafedSpaceHom (hJ : IsAdic J) :
    (Spec.locallyRingedSpaceObj (CommRingCat.of (A ⧸ J))).toPresheafedSpace ⟶
      (Spf A).toPresheafedSpace where
  base := quotientInclusion hJ
  c := (toQuotientSheaf (IsAdicRing.ideal_spec A).2.1 hJ).hom

private theorem quotientPresheafedSpaceHom_stalk_surjective (hJ : IsAdic J)
    (q : PrimeSpectrum (A ⧸ J)) :
    Function.Surjective ((quotientPresheafedSpaceHom hJ).stalkMap q) := by
  have hsurj := (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mp
    (toQuotientSheaf_isLocallySurjective (IsAdicRing.ideal_spec A).2.1 hJ)
    (quotientInclusion hJ q)
  have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing CommRingCat
    (f := quotientInclusion hJ) (by
      have h : (quotientInclusion hJ : _ → _) = (homeomorphSpecQuotient hJ).symm :=
        funext (quotientInclusion_apply hJ)
      rw [h]
      exact (homeomorphSpecQuotient hJ).symm.isInducing)
    (Spec.structureSheaf (A ⧸ J)).obj q
  exact (ConcreteCategory.bijective_of_isIso
    (TopCat.Presheaf.stalkPushforward CommRingCat (quotientInclusion hJ)
      (Spec.structureSheaf (A ⧸ J)).obj q)).2.comp
      hsurj

/-- The canonical morphism `Spec (A ⧸ J) → Spf A` for an ideal of definition `J`. It identifies
all the points, and on structure sheaves is the quotient projection. -/
noncomputable def fromSpecQuotient (hJ : IsAdic J) :
    Spec.locallyRingedSpaceObj (CommRingCat.of (A ⧸ J)) ⟶ Spf A where
  base := quotientInclusion hJ
  c := (toQuotientSheaf (IsAdicRing.ideal_spec A).2.1 hJ).hom
  prop q := IsLocalHom.of_surjective _ (quotientPresheafedSpaceHom_stalk_surjective hJ q)

/-- The underlying continuous map of the quotient morphism is `quotientInclusion`. -/
@[simp]
theorem fromSpecQuotient_base (hJ : IsAdic J) :
    (fromSpecQuotient hJ).base = quotientInclusion hJ :=
  (rfl)

/-- The quotient morphism has underlying map `quotientInclusion` and sheaf map
`toQuotientSheaf`. Stating both components together avoids transports between pushforwards. -/
theorem fromSpecQuotient_toHom (hJ : IsAdic J) :
    (fromSpecQuotient hJ).toHom =
      { base := quotientInclusion hJ
        c := (toQuotientSheaf (IsAdicRing.ideal_spec A).2.1 hJ).hom } :=
  (rfl)

/-- On points the quotient morphism sends a prime to its inverse image in `A`. -/
theorem fromSpecQuotient_points (hJ : IsAdic J) (q : PrimeSpectrum (A ⧸ J)) :
    ((fromSpecQuotient hJ).base q : carrier A) = (homeomorphSpecQuotient hJ).symm q :=
  quotientInclusion_apply hJ q

/-- The quotient morphism is a homeomorphism on the underlying spaces. -/
theorem fromSpecQuotient_isHomeomorph (hJ : IsAdic J) :
    IsHomeomorph (fromSpecQuotient hJ).base := by
  -- The source and target carriers are wrapped in `LocallyRingedSpace` and `TopCat`.
  convert (homeomorphSpecQuotient hJ).symm.isHomeomorph using 1 <;> try rfl
  exact heq_of_eq (funext (fromSpecQuotient_points hJ))

/-- The quotient morphism is surjective on stalks. -/
theorem fromSpecQuotient_stalk_surjective (hJ : IsAdic J) (q : PrimeSpectrum (A ⧸ J)) :
    Function.Surjective ((fromSpecQuotient hJ).stalkMap q) :=
  quotientPresheafedSpaceHom_stalk_surjective hJ q

/-- On global sections the quotient morphism is `A → A ⧸ J`. -/
@[reassoc (attr := simp)]
theorem fromSpecQuotient_globalSections (hJ : IsAdic J) :
    have := (IsAdicRing.ideal_spec A).2.2
    (globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv ≫
        (fromSpecQuotient hJ).c.app (op ⊤) ≫ (quotientSheafGlobalSectionsIso hJ).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk J) := by
  intro
  have h := globalSectionsIso_inv_comp_toQuotientSheaf
    (IsAdicRing.ideal_spec A).2.1 hJ
  -- Global sections of a pushforward are the source global sections, through the top-open
  -- identification. Use the component description before composing with their comparison.
  exact (congrArg (· ≫ (quotientSheafGlobalSectionsIso hJ).hom) h).trans (by simp)

/-- The quotient thickenings form a compatible system: reducing further and then including
in the formal spectrum is the same as the direct quotient inclusion. -/
@[reassoc (attr := simp)]
theorem fromSpecQuotient_naturality (hJ : IsAdic J) (hK : IsAdic K) (hJK : J ≤ K) :
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (Ideal.Quotient.factor hJK)) ≫
      fromSpecQuotient hJ = fromSpecQuotient hK := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ ?_ ?_
  · apply ConcreteCategory.hom_ext
    intro q
    exact (quotientInclusion_apply hJ _).trans
      ((homeomorphSpecQuotient_symm_comap_factor hJ hK hJK q).trans
        (quotientInclusion_apply hK q).symm)
  · -- Equality of the base maps transports sections by a restriction. Composing that
    -- restriction with the scheme's comap gives exactly `quotientTransition`.
    ext U s
    erw [NatTrans.comp_app, Functor.whiskerRight_app]
    erw [PresheafedSpace.comp_c_app]
    dsimp only [fromSpecQuotient]
    dsimp only [Spec.locallyRingedSpaceMap, Spec.sheafedSpaceMap]
    erw [Spec.locallyRingedSpaceObj_presheaf_map]
    dsimp only [CommRingCat.hom_ofHom]
    erw [CommRingCat.hom_comp, CommRingCat.hom_comp, ← RingHom.comp_assoc]
    erw [StructureSheaf.map_comp_comap]
    have h := congrArg (fun η ↦ η.hom.app (op U))
      (toQuotientSheaf_comp_quotientTransition (IsAdicRing.ideal_spec A).2.1 hJ hK hJK)
    erw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      quotientTransition_hom_app] at h
    exact ConcreteCategory.congr_hom h s

/-- An ideal-of-definition quotient embeds as a subobject of the formal spectrum. -/
instance fromSpecQuotient_mono (hJ : IsAdic J) : Mono (fromSpecQuotient hJ) := by
  have : Mono (fromSpecQuotient hJ).toShHom :=
    SheafedSpace.mono_of_base_injective_of_stalk_epi _
      (fromSpecQuotient_isHomeomorph hJ).injective fun q ↦
        ConcreteCategory.epi_of_surjective _ (fromSpecQuotient_stalk_surjective hJ q)
  exact LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map this

end TauCeti.FormalScheme.Spf
