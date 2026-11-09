/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Blowup
public import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Blowup
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Regular

/-!
# Separating the branches of a nodal curve

For a nodal curve over a field, blowing up the singular subscheme is finite, surjective, and has
regular source. No properness, connectedness, or perfection of the field is assumed. Over the
smooth locus the blowup is an isomorphism. Over the singular subscheme its exceptional divisor
is the branch scheme, which is étale over the field. Regularity lifts from this effective
Cartier divisor to the ambient blowup. Thus a single finite modification resolves all the nodes.

These results supply the finite regular scheme used to construct the normalization of a nodal
curve and its normalization exact sequence.

## References

* The Stacks Project, Section 53.19, Nodal curves, Tag 0C46.
* The Stacks Project, Lemma 31.32.4, Tag 02OG (the exceptional divisor of a blowup).
* The Stacks Project, Lemma 10.106.7, Tag 00NU (lifting regularity from a Cartier divisor).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

/-- The blowup of a nodal curve at its singular subscheme is finite, including when the curve
is not proper. Its fibres are singletons over smooth points and finite over nodes. -/
theorem isFinite_blowupToBase_singularLocus
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    IsFinite (X.singularLocus K).blowupToBase := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := hnodal.syntomic
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  let f := (X.singularLocus K).blowupToBase
  have : IsProper f := inferInstance
  have : IsFinite (X.branchSchemeToSingularLocus K) :=
    X.isFinite_branchSchemeToSingularLocus hnodal
  have : IsIso (f ∣_ (X ↘ Spec (.of K)).smoothLocus) :=
    X.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  have : LocallyQuasiFinite f := by
    apply LocallyQuasiFinite.of_finite_preimage_singleton
    intro x
    by_cases hx : x ∈ (X.singularLocus K).support
    · -- Over a node the fibre is the fibre of the finite branch scheme.
      obtain ⟨s, rfl⟩ := (IdealSheafData.range_subschemeι _).ge hx
      have h := image_preimage_eq_of_isPullback (X.isPullback_branchScheme K) {s}
      rw [Set.image_singleton] at h
      rw [← h]
      exact ((X.branchSchemeToSingularLocus K).finite_preimage_singleton s).image _
    · -- Over a smooth point use the finite fibre of the restriction isomorphism.
      have hxU : x ∈ (X ↘ Spec (.of K)).smoothLocus := by
        simpa only [mem_support_singularLocus_iff_notMem_smoothLocus, not_not] using hx
      have h := image_preimage_eq_of_isPullback
        (isPullback_morphismRestrict f (X ↘ Spec (.of K)).smoothLocus) {⟨x, hxU⟩}
      rw [Set.image_singleton (f := (X ↘ Spec (.of K)).smoothLocus.ι)
        (a := (⟨x, hxU⟩ : (X ↘ Spec (.of K)).smoothLocus.toScheme)),
      Scheme.Opens.ι_apply] at h
      rw [← h]
      exact ((f ∣_ (X ↘ Spec (.of K)).smoothLocus).finite_preimage_singleton
        ⟨x, hxU⟩).image _
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- The blowup separating the branches of a nodal curve is surjective. In particular it does
not discard any component, even when the curve is disconnected or has self-nodes. -/
theorem surjective_blowupToBase_singularLocus
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    Surjective (X.singularLocus K).blowupToBase := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := hnodal.syntomic
  have : IsFinite (X.branchSchemeToSingularLocus K) :=
    X.isFinite_branchSchemeToSingularLocus hnodal
  have : Etale (X.branchSchemeToSingularLocus K) :=
    X.etale_branchSchemeToSingularLocus hnodal
  have hbr : Surjective (X.branchSchemeToSingularLocus K) :=
    (X.branchSchemeToSingularLocus K).one_le_finrank_iff_surjective.mp fun s ↦ by
      rw [X.finrank_branchSchemeToSingularLocus hnodal s]
      simp
  refine ⟨fun x ↦ ?_⟩
  by_cases hx : x ∈ (X.singularLocus K).support
  · obtain ⟨s, rfl⟩ := (IdealSheafData.range_subschemeι _).ge hx
    obtain ⟨b, hb⟩ := (X.branchSchemeToSingularLocus K).surjective s
    refine ⟨X.branchSchemeToBlowup K b, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← X.branchSchemeToSingularLocus_subschemeι K,
      Scheme.Hom.comp_apply, hb]
  · have hxU : x ∈ (X ↘ Spec (.of K)).smoothLocus := by
      simpa only [mem_support_singularLocus_iff_notMem_smoothLocus, not_not] using hx
    let f := (X.singularLocus K).blowupToBase
    have := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus (R := K)
    have h := image_preimage_eq_of_isPullback
      (isPullback_morphismRestrict f (X ↘ Spec (.of K)).smoothLocus) {⟨x, hxU⟩}
    rw [Set.image_singleton (f := (X ↘ Spec (.of K)).smoothLocus.ι)
        (a := (⟨x, hxU⟩ : (X ↘ Spec (.of K)).smoothLocus.toScheme)),
      Scheme.Opens.ι_apply] at h
    have hne := (Set.preimage_singleton_nonempty.mpr
      ((f ∣_ (X ↘ Spec (.of K)).smoothLocus).surjective ⟨x, hxU⟩)).image
        (f ⁻¹ᵁ (X ↘ Spec (.of K)).smoothLocus).ι
    rw [h] at hne
    exact Set.preimage_singleton_nonempty.mp hne

/-- Blowing up the singular subscheme resolves a nodal curve over any field: every local ring
of the blowup is regular. -/
theorem isRegular_blowup_singularLocus
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) :
    letI := hnodal.syntomic
    IsRegular (X.singularLocus K).blowup := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := hnodal.syntomic
  have := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  let I := X.singularLocus K
  let f := I.blowupToBase
  have : IsLocallyNoetherian I.blowup := LocallyOfFiniteType.isLocallyNoetherian f
  have : Etale (X.branchSchemeToSingularLocus K) :=
    X.etale_branchSchemeToSingularLocus hnodal
  have : Etale (I.subschemeι ≫ (X ↘ Spec (.of K))) :=
    X.etale_singularLocus_subschemeι_comp hnodal
  let e : (I.comap f).subscheme ≅ X.branchScheme K :=
    I.comapIso f ≪≫ pullbackSymmetry _ _ ≪≫ (X.isPullback_branchScheme K).isoPullback.symm
  let g := e.hom ≫ X.branchSchemeToSingularLocus K ≫ I.subschemeι ≫ (X ↘ Spec (.of K))
  have : Smooth g := inferInstance
  have hE : IsRegular (I.comap f).subscheme := IsRegular.of_smooth g
  have : IsIso (f ∣_ (X ↘ Spec (.of K)).smoothLocus) :=
    X.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  have hU : IsRegular ((X ↘ Spec (.of K)).smoothLocus.toScheme) :=
    IsRegular.of_smooth ((X ↘ Spec (.of K)).smoothLocus.ι ≫ (X ↘ Spec (.of K)))
  refine ⟨fun y ↦ ?_⟩
  by_cases hy : y ∈ (I.comap f).support
  · exact I.isEffectiveCartier_comap_blowupToBase.isRegularLocalRing_stalk_of_mem_support
      (fun _ ↦ inferInstance) hy
  · have hyU : y ∈ f ⁻¹ᵁ (X ↘ Spec (.of K)).smoothLocus := by
      rw [IdealSheafData.support_comap, ← SetLike.mem_coe,
        TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage, SetLike.mem_coe] at hy
      apply f.mem_preimage.mpr
      simpa only [I, mem_support_singularLocus_iff_notMem_smoothLocus, not_not] using hy
    let y' : (f ⁻¹ᵁ (X ↘ Spec (.of K)).smoothLocus).toScheme := ⟨y, hyU⟩
    have : IsRegular (f ⁻¹ᵁ (X ↘ Spec (.of K)).smoothLocus).toScheme :=
      IsRegular.of_isOpenImmersion (f ∣_ (X ↘ Spec (.of K)).smoothLocus)
    exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion
      (f ⁻¹ᵁ (X ↘ Spec (.of K)).smoothLocus).ι y').mpr inferInstance

end AlgebraicGeometry.Scheme
