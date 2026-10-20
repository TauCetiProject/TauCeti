/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.AffineCharts
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.AlgebraicGeometry.AffineScheme

/-!
# The blowup of an affine scheme away from its center

Let `I` be an ideal of a commutative ring `R`. The blowup of `Spec R` along `V(I)` is
`Proj R[It] ⟶ Spec R`. This file proves that it changes nothing away from the center: over every
open subset of `Spec R` disjoint from `V(I)` it restricts to an isomorphism.

Locally this is explicit. For `a ∈ I`, the part of the blowup lying over the basic open `D(a)`
is the basic open `D(a)` of the chart `Spec R[I/a]`, and over it the chart is `Spec` of the
isomorphism `R_a ≅ R[I/a]_a`, because `R ⊆ R[I/a] ⊆ R_a`.

For instance, if `π ∈ I`, this applies to `U = D(π)`: blowing up a center contained in `V(π)`
changes nothing over `D(π)`. When `R` is an algebra over a discrete valuation ring with
uniformizer `π`, the open `D(π)` is the generic fibre, so such a blowup of a model is again a
model of the same generic fibre.

## Main results

* `TauCeti.AlgebraicGeometry.affineBlowupι_image_basicOpen`: for `a ∈ I`, the inverse image of
  `D(a)` in the blowup is the image of the basic open `D(a)` of the chart `Spec R[I/a]`.
* `TauCeti.AlgebraicGeometry.isIso_morphismRestrict_affineBlowup_of_disjoint_zeroLocus`: the blowup
  `Proj R[It] ⟶ Spec R` restricts to an isomorphism over every open subset of `Spec R` that is
  disjoint from `V(I)`.

## References

* [The Stacks Project, Section *Blowing up*](https://stacks.math.columbia.edu/tag/01OF)
-/

public section

noncomputable section

open CategoryTheory reesAlgebra

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} {a : R}

/-- Over `D(a)`, the blowup lies inside the chart of `a`: the inverse image of `D(a)` in
`Proj R[It]` is contained in the standard open `D₊(a t)`. -/
private theorem preimage_basicOpen_le_basicOpen_monomialDegreeOne (ha : a ∈ I) :
    (Proj.toSpecZero (grade I) ≫ Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom) ⁻¹ᵁ
        PrimeSpectrum.basicOpen a ≤
      Proj.basicOpen (grade I) (monomialDegreeOne ha) := by
  intro x hx
  -- A point over `D(a)` is a homogeneous prime not containing `a`.
  have hxa :
      x ∈ Proj.basicOpen (grade I) ((gradeZeroEquiv I a : grade I 0) : reesAlgebra I) := by
    have : x ∈ Proj.toSpecZero (grade I) ⁻¹ᵁ PrimeSpectrum.basicOpen (gradeZeroEquiv I a) := hx
    rwa [Proj.toSpecZero_preimage_basicOpen] at this
  -- It also avoids some `b t` with `b ∈ I`, since these generate the irrelevant ideal.
  have hcover := Proj.iSup_basicOpen_eq_top (grade I) (fun b : I ↦ monomialDegreeOne b.2)
    (irrelevant_eq_span_monomialDegreeOne (s := fun b : I ↦ (b : R)) (by simp)).le
  obtain ⟨b, hxb⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover.ge (by trivial : x ∈ ⊤))
  -- Then `x` avoids `a · (b t) = b · (a t)`, hence `a t`.
  have hab : ((gradeZeroEquiv I a : grade I 0) : reesAlgebra I) * monomialDegreeOne b.2 =
      ((gradeZeroEquiv I b : grade I 0) : reesAlgebra I) * monomialDegreeOne ha := by
    ext1
    simp [Polynomial.C_mul_monomial, mul_comm]
  have hmem : x ∈ Proj.basicOpen (grade I)
      (((gradeZeroEquiv I b : grade I 0) : reesAlgebra I) * monomialDegreeOne ha) :=
    hab ▸ (Proj.basicOpen_mul _ _ _).ge ⟨hxa, hxb⟩
  exact ((Proj.basicOpen_mul _ _ _).le hmem).2

variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away a S]

/-- **The blowup over `D(a)`.** For `a ∈ I`, the inverse image of the basic open `D(a)` of
`Spec R` in the blowup `Proj R[It]` is the image of the basic open `D(a)` of the chart
`Spec R[I/a]`. -/
theorem affineBlowupι_image_basicOpen (ha : a ∈ I) :
    affineBlowupι S ha ''ᵁ PrimeSpectrum.basicOpen (algebraMap R (I.affineBlowup a S) a) =
      (Proj.toSpecZero (grade I) ≫ Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom) ⁻¹ᵁ
        PrimeSpectrum.basicOpen a := by
  set f := Proj.toSpecZero (grade I) ≫ Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom
  have hle := preimage_basicOpen_le_basicOpen_monomialDegreeOne ha
  rw [← opensRange_affineBlowupι S ha] at hle
  -- On the chart, the inverse image of `D(a)` is the basic open of `a`.
  have h : affineBlowupι S ha ⁻¹ᵁ (f ⁻¹ᵁ PrimeSpectrum.basicOpen a) =
      PrimeSpectrum.basicOpen (algebraMap R (I.affineBlowup a S) a) :=
    congrArg (fun g : Spec (.of (I.affineBlowup a S)) ⟶ Spec (.of R) ↦
      g ⁻¹ᵁ (PrimeSpectrum.basicOpen a : (Spec (.of R)).Opens)) (affineBlowupι_toSpecZero S ha)
  calc _ = affineBlowupι S ha ''ᵁ (affineBlowupι S ha ⁻¹ᵁ (f ⁻¹ᵁ PrimeSpectrum.basicOpen a)) :=
        congrArg (affineBlowupι S ha ''ᵁ ·) h.symm
    _ = _ := by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hle]

/-- Over an open subset `W` of `D(a)`, for `a ∈ I`, the blowup restricts to an isomorphism. -/
private theorem isIso_morphismRestrict_of_le_basicOpen (ha : a ∈ I) {W : (Spec (.of R)).Opens}
    (hW : W ≤ PrimeSpectrum.basicOpen a) :
    IsIso ((Proj.toSpecZero (grade I) ≫
      Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom) ∣_ W) := by
  set f := Proj.toSpecZero (grade I) ≫ Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom
  set g := Spec.map (CommRingCat.ofHom (algebraMap R (I.affineBlowup a (Localization.Away a))))
  -- Over `D(a)`, the chart `Spec R[I/a] ⟶ Spec R` is an isomorphism, as `R ⊆ R[I/a] ⊆ R_a`.
  have hga : IsIso (g ∣_ PrimeSpectrum.basicOpen a) :=
    isIso_SpecMap_morphismRestrict_basicOpen_of_injective (S := Localization.Away a) a
      Subtype.val_injective
  -- Hence also over `W ⊆ D(a)`.
  set D : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen a
  have himage : D.ι ''ᵁ (D.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hW
  have hgW : IsIso (g ∣_ W) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict g _ _ ≪≫ morphismRestrictEq g himage)).mp
      (inferInstanceAs (IsIso ((g ∣_ _) ∣_ _)))
  -- Over `W`, the blowup lies in the chart of `a`, so `g ∣_ W` is `f ∣_ W` up to an isomorphism.
  have hle : f ⁻¹ᵁ W ≤ (affineBlowupι (Localization.Away a) ha).opensRange := by
    rw [opensRange_affineBlowupι]
    exact (f.preimage_mono hW).trans (preimage_basicOpen_le_basicOpen_monomialDegreeOne ha)
  have : IsIso (affineBlowupι (Localization.Away a) ha ∣_ f ⁻¹ᵁ W) := by
    refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
    obtain ⟨z, hz⟩ := hle y.2
    exact ⟨⟨z, (Scheme.Hom.mem_preimage _).mpr (hz ▸ y.2)⟩,
      Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hz)⟩
  have hcomp : IsIso ((affineBlowupι (Localization.Away a) ha ≫ f) ∣_ W) := by
    rwa [affineBlowupι_toSpecZero]
  rw [morphismRestrict_comp] at hcomp
  -- `hcomp` is passed explicitly: the source of the composite in its type is written
  -- `(ι ≫ f) ⁻¹ᵁ W` rather than `ι ⁻¹ᵁ f ⁻¹ᵁ W`, which instance search does not unfold.
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (affineBlowupι (Localization.Away a) ha ∣_ f ⁻¹ᵁ W)
    (f ∣_ W) _ hcomp

/-- **The blowup is an isomorphism away from its center.** The blowup `Proj R[It] ⟶ Spec R` of
`Spec R` along `V(I)` restricts to an isomorphism over every open subset `U` of `Spec R` that is
disjoint from `V(I)`. -/
theorem isIso_morphismRestrict_affineBlowup_of_disjoint_zeroLocus {U : (Spec (.of R)).Opens}
    (hU : Disjoint (α := Set (PrimeSpectrum R)) (U : Set (Spec (.of R)))
      (PrimeSpectrum.zeroLocus (I : Set R))) :
    IsIso ((Proj.toSpecZero (grade I) ≫
      Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom) ∣_ U) := by
  set f := Proj.toSpecZero (grade I) ≫ Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom
  -- `U` is covered by the opens `U ∩ D(b)` for `b ∈ I`, over each of which `f` is an isomorphism.
  let V (b : I) : U.toScheme.Opens := U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (b : R)
  have hV : ⨆ b, V b = ⊤ := by
    refine top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
    -- a point of `U` is a prime not containing `I`
    have hx : ¬(I : Set R) ⊆ (x.1 : PrimeSpectrum R).asIdeal := Set.disjoint_left.mp hU x.2
    obtain ⟨b, hb, hbx⟩ := Set.not_subset.mp hx
    exact ⟨⟨b, hb⟩, hbx⟩
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) V hV]
  intro b
  have himage : U.ι ''ᵁ V b = U ⊓ PrimeSpectrum.basicOpen (b : R) :=
    (U.ι.image_preimage_eq_opensRange_inf _).trans (by rw [Scheme.Opens.opensRange_ι])
  refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U (V b) ≪≫ morphismRestrictEq f himage)).mpr ?_
  exact (MorphismProperty.isomorphisms.iff _).mpr
    (isIso_morphismRestrict_of_le_basicOpen b.2 inf_le_right)

end TauCeti.AlgebraicGeometry
