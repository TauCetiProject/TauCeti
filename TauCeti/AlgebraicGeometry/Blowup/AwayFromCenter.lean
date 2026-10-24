/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.AffineCharts
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.Restrict

/-!
# The blowup of an affine scheme away from its center

Let `I` be an ideal of a commutative ring `R`. The blowup of `Spec R` along `V(I)` is
`Proj R[It] ⟶ Spec R`. This file proves that it changes nothing away from the center: over every
open subset of `Spec R` disjoint from `V(I)` it restricts to an isomorphism.

Locally this is explicit. For `a ∈ I`, the part of the blowup lying over the basic open `D(a)`
is the basic open `D(a)` of the chart `Spec R[I/a]`, and over it the chart is `Spec` of the
isomorphism `R_a ≅ R[I/a]_a`: the compatible tower `R → R[I/a] ↪ R_a` identifies the
localization of the intermediate algebra at `a` with `R_a`; the map from `R` need not be injective.

For instance, if `π ∈ I`, this applies to `U = D(π)`: blowing up a center contained in `V(π)`
changes nothing over `D(π)`. When `R` is an algebra over a discrete valuation ring with
uniformizer `π`, the open `D(π)` is the generic fibre. The isomorphism over this open preserves
the generic-fibre identification; no properness or flatness assertion is made here.

## Main results

All results are in the namespace `TauCeti.AlgebraicGeometry`.

* `toSpecZero_reesAlgebra_preimage_basicOpen`: the inverse image of `D(a)` in the blowup is the
  standard open `D₊(a)` of the degree-zero element `a`.
* `affineBlowupι_image_basicOpen`: for `a ∈ I`, the inverse image of `D(a)` in the blowup is the
  image of the basic open `D(a)` of the chart `Spec R[I/a]`.
* `isIso_morphismRestrict_toSpecZero_reesAlgebra_of_disjoint_zeroLocus`: the blowup
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

variable (I) in
/-- The inverse image of the basic open `D(a)` of `Spec R` in the blowup `Proj R[It]` is the
standard open `D₊(a)` of the degree-zero element `a`: the homogeneous primes not containing `a`. -/
theorem toSpecZero_reesAlgebra_preimage_basicOpen (a : R) :
    (Proj.toSpecZero (grade I) ≫ Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom) ⁻¹ᵁ
        PrimeSpectrum.basicOpen a =
      Proj.basicOpen (grade I) ((gradeZeroEquiv I a : grade I 0) : reesAlgebra I) := by
  have h := Scheme.Hom.comp_preimage (Proj.toSpecZero (grade I))
    (Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom) (PrimeSpectrum.basicOpen a)
  rwa [SpecMap_preimage_basicOpen, RingEquiv.toCommRingCatIso_hom, CommRingCat.ofHom_apply,
    Proj.toSpecZero_preimage_basicOpen] at h

/-- Over `D(a)`, the blowup lies inside the chart of `a`: the inverse image of `D(a)` in
`Proj R[It]` is contained in the standard open `D₊(a t)`. -/
private theorem preimage_basicOpen_le_basicOpen_monomialDegreeOne (ha : a ∈ I) :
    (Proj.toSpecZero (grade I) ≫ Spec.map (gradeZeroEquiv I).toCommRingCatIso.hom) ⁻¹ᵁ
        PrimeSpectrum.basicOpen a ≤
      Proj.basicOpen (grade I) (monomialDegreeOne ha) := by
  intro x hx
  -- A point over `D(a)` is a homogeneous prime not containing `a`.
  rw [toSpecZero_reesAlgebra_preimage_basicOpen] at hx
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
    hab ▸ (Proj.basicOpen_mul _ _ _).ge ⟨hx, hxb⟩
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
      PrimeSpectrum.basicOpen (algebraMap R (I.affineBlowup a S) a) := by
    have h' := Scheme.Hom.comp_preimage (affineBlowupι S ha) f (PrimeSpectrum.basicOpen a)
    rw [affineBlowupι_toSpecZero, SpecMap_preimage_basicOpen, CommRingCat.ofHom_apply] at h'
    exact h'.symm
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
  -- The tower `R → R[I/a] ↪ R_a` identifies the localization of the chart algebra at `a`
  -- with `R_a`, so the chart is an isomorphism over `D(a)`.
  have hga : IsIso (g ∣_ PrimeSpectrum.basicOpen a) :=
    isIso_SpecMap_morphismRestrict_basicOpen_of_injective (S := Localization.Away a) a
      Subtype.val_injective
  -- Hence also over `W ⊆ D(a)`.
  have hgW : IsIso (g ∣_ W) := (MorphismProperty.isomorphisms.iff _).mp
    (IsZariskiLocalAtTarget.restrict_of_le (MorphismProperty.isomorphisms Scheme)
      ((MorphismProperty.isomorphisms.iff _).mpr inferInstance) hW)
  -- Over `W`, the blowup lies in the chart of `a`, so `g ∣_ W` is `f ∣_ W` up to an isomorphism.
  have hle : f ⁻¹ᵁ W ≤ (affineBlowupι (Localization.Away a) ha).opensRange := by
    rw [opensRange_affineBlowupι]
    exact (f.preimage_mono hW).trans (preimage_basicOpen_le_basicOpen_monomialDegreeOne ha)
  have : IsIso (affineBlowupι (Localization.Away a) ha ∣_ f ⁻¹ᵁ W) :=
    (affineBlowupι (Localization.Away a) ha).isIso_morphismRestrict_of_le_opensRange hle
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
theorem isIso_morphismRestrict_toSpecZero_reesAlgebra_of_disjoint_zeroLocus
    {U : (Spec (.of R)).Opens} (hU : Disjoint (α := Set (PrimeSpectrum R)) (U : Set (Spec (.of R)))
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
  refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U (V b))).mpr ?_
  exact (MorphismProperty.isomorphisms.iff _).mpr
    (isIso_morphismRestrict_of_le_basicOpen b.2 (U.ι.image_preimage_le _))

end TauCeti.AlgebraicGeometry
