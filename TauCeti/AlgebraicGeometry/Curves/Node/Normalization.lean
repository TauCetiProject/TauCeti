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
import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Separating the branches of a nodal curve

For a nodal curve over a field, blowing up the singular subscheme is finite, surjective, and has
regular source. No properness, connectedness, or perfection of the field is assumed. Over the
smooth locus the blowup is an isomorphism. Over the singular subscheme its exceptional divisor
is the branch scheme, which is étale over the field. Regularity lifts from this effective
Cartier divisor to the ambient blowup. Thus a single finite modification resolves all the nodes.

These results supply the finite regular scheme used to construct the normalization of a nodal
curve and its normalization exact sequence.

Over an algebraically closed field the blowup separates the branches point by point: exactly one
point lies over each smooth point, and exactly two lie over each node, one on each branch. Over a
node, these are the points of the branch scheme, which is finite étale of rank two over the
singular subscheme. These counts are the incidence data of the dual graph of the curve.

## Main results

* `AlgebraicGeometry.Scheme.isFinite_blowupToBase_singularLocus`,
  `AlgebraicGeometry.Scheme.surjective_blowupToBase_singularLocus` and
  `AlgebraicGeometry.Scheme.isRegular_blowup_singularLocus`: blowing up the singular subscheme is
  a finite surjective morphism from a regular scheme.
* `AlgebraicGeometry.Scheme.natCard_preimage_blowupToBase_singularLocus_of_mem_smoothLocus`: one
  point of the blowup lies over each smooth point.
* `AlgebraicGeometry.Scheme.natCard_preimage_blowupToBase_singularLocus_of_mem_support`: over an
  algebraically closed field, two points of the blowup lie over each node.

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

/-- **One point of the blowup lies over each smooth point.** Blowing up the singular subscheme of
a syntomic relative curve changes nothing over its smooth locus. -/
theorem natCard_preimage_blowupToBase_singularLocus_of_mem_smoothLocus
    [SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K))] {x : X}
    (hx : x ∈ (X ↘ Spec (.of K)).smoothLocus) :
    Nat.card ((X.singularLocus K).blowupToBase ⁻¹' {x}) = 1 := by
  let U := (X ↘ Spec (.of K)).smoothLocus
  let f := (X.singularLocus K).blowupToBase
  have : IsIso (f ∣_ U) := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  have hf (p : f ⁻¹ᵁ U) : ((f ∣_ U) p).1 = f p.1 := by rw [morphismRestrict_base]; rfl
  -- over the smooth locus, `f` is an isomorphism, hence bijective on points
  have hbij := (f ∣_ U).homeomorph.bijective
  rw [Nat.card_eq_one_iff_exists]
  obtain ⟨⟨b, hb⟩, hbx⟩ := hbij.2 ⟨x, hx⟩
  have hbx' : f b = x := (hf ⟨b, hb⟩).symm.trans congr(($hbx).1)
  refine ⟨⟨b, hbx'⟩, fun ⟨b', hb'⟩ ↦ Subtype.ext ?_⟩
  have hb'U : b' ∈ f ⁻¹ᵁ U := by
    change f b' ∈ U
    rw [show f b' = x from hb']
    exact hx
  have := hbij.1 (a₁ := ⟨b', hb'U⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext ((hf ⟨b', hb'U⟩).trans
    ((show f b' = x from hb').trans (hbx'.symm.trans (hf ⟨b, hb⟩).symm))))
  exact congr(($this).1)

/-- **Two points of the blowup lie over each node.** Over an algebraically closed field, the
points of the blowup of a nodal curve along its singular subscheme lying over a node are the two
points of the branch scheme over it, one on each branch. -/
theorem natCard_preimage_blowupToBase_singularLocus_of_mem_support [IsAlgClosed K]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) {x : X}
    (hx : (letI := hnodal.syntomic; x ∈ (X.singularLocus K).support)) :
    letI := hnodal.syntomic
    Nat.card ((X.singularLocus K).blowupToBase ⁻¹' {x}) = 2 := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := hnodal.syntomic
  have := X.isFinite_branchSchemeToSingularLocus hnodal
  have := X.etale_branchSchemeToSingularLocus hnodal
  have := X.etale_singularLocus_subschemeι_comp hnodal
  let I := X.singularLocus K
  have : IsClosedImmersion (X.branchSchemeToBlowup K) :=
    MorphismProperty.of_isPullback (X.isPullback_branchScheme K) inferInstance
  obtain ⟨z, rfl⟩ : x ∈ Set.range I.subschemeι := by rwa [IdealSheafData.range_subschemeι]
  have : IsAlgClosed (I.subscheme.residueField z) :=
    (I.subschemeι ≫ X ↘ Spec (.of K)).isAlgClosed_residueField_of_formallyUnramified z
  rw [← X.finrank_branchSchemeToSingularLocus hnodal z,
    ← Scheme.Hom.natCard_preimage_singleton_eq_finrank]
  -- the branch scheme is the inverse image of the singular subscheme in the blowup
  have hmaps (e : X.branchSchemeToSingularLocus K ⁻¹' {z}) :
      X.branchSchemeToBlowup K e.1 ∈ I.blowupToBase ⁻¹' {I.subschemeι z} := by
    have := congr($(X.branchSchemeToSingularLocus_subschemeι K) e.1)
    simp only [Scheme.Hom.comp_apply] at this
    rw [Set.mem_preimage, Set.mem_singleton_iff, ← this, e.2]
  let φ : X.branchSchemeToSingularLocus K ⁻¹' {z} → I.blowupToBase ⁻¹' {I.subschemeι z} :=
    fun e ↦ ⟨_, hmaps e⟩
  refine (Nat.card_congr (Equiv.ofBijective φ
    ⟨fun e e' h ↦ Subtype.ext ((X.branchSchemeToBlowup K).isClosedEmbedding.injective
      (congrArg Subtype.val h :)), fun b ↦ ?_⟩)).symm
  obtain ⟨e, he, hb⟩ := Scheme.Pullback.exists_preimage_pullback (f := I.subschemeι)
    (g := I.blowupToBase) z b.1 b.2.symm
  let H := X.isPullback_branchScheme K
  refine ⟨⟨H.isoPullback.inv e, ?_⟩, Subtype.ext ?_⟩
  · rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply,
      IsPullback.isoPullback_inv_fst, he]
  · change (H.isoPullback.inv ≫ X.branchSchemeToBlowup K) e = b.1
    rw [IsPullback.isoPullback_inv_snd, hb]

end AlgebraicGeometry.Scheme
