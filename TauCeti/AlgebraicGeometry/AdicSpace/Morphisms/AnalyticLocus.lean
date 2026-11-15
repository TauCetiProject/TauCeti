/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.Adic

/-!
# Restricting adic morphisms to analytic loci

An adic morphism restricts uniquely to the analytic loci of its source and target. The
resulting square with the two open inclusions is cartesian: the analytic locus of the source
is exactly the inverse image of the analytic locus of the target. This allows constructions on
analytic open subspaces to be compared with restriction along adic morphisms.

A map from a space all of whose points are analytic factors through the analytic locus of its
target if and only if it is adic. The factorization and restriction maps below are morphisms of
adic spaces, not just maps of their underlying topological spaces.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, §3,
  Proposition 3.2.
* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Remark 8.37 and Proposition 8.39.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.AdicSpace

universe u

variable {X Y Z T : AdicSpace.{u}}

/-- For an adic morphism the analytic points of the source are exactly the inverse image of
those of the target. -/
theorem IsAdic.preimage_analyticPoints {f : X ⟶ Y} (hf : IsAdic f) :
    f.hom.base ⁻¹' Y.obj.analyticPoints = X.obj.analyticPoints :=
  (PreAdicSpace.preimage_analyticPoints_eq_iff_mapsTo f.hom).mpr
    ((isAdic_iff_mapsTo_analyticPoints f).mp hf)

/-- Restriction of an adic morphism to the analytic loci of its source and target. -/
noncomputable def IsAdic.analyticLocusMap {f : X ⟶ Y} (hf : IsAdic f) :
    X.analyticLocus ⟶ Y.analyticLocus :=
  analyticLocus.lift (analyticLocus.ι X ≫ f) <| by
    rintro _ ⟨x, rfl⟩
    exact (isAdic_iff_mapsTo_analyticPoints f).mp hf
      (analyticLocus.range_ι X ▸ Set.mem_range_self x)

/-- Restriction commutes with the analytic-locus inclusions. -/
@[reassoc (attr := simp)]
theorem IsAdic.analyticLocusMap_ι {f : X ⟶ Y} (hf : IsAdic f) :
    hf.analyticLocusMap ≫ analyticLocus.ι Y = analyticLocus.ι X ≫ f :=
  analyticLocus.lift_ι _ _

/-- Restriction preserves identities. -/
@[simp]
theorem IsAdic.analyticLocusMap_id (h : IsAdic (𝟙 X)) :
    h.analyticLocusMap = 𝟙 X.analyticLocus := by
  rw [← cancel_mono (analyticLocus.ι X)]
  simp

/-- Restriction preserves composition. -/
theorem IsAdic.analyticLocusMap_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsAdic f) (hg : IsAdic g) :
    (IsAdic.comp_mem f g hf hg).analyticLocusMap = hf.analyticLocusMap ≫ hg.analyticLocusMap := by
  rw [← cancel_mono (analyticLocus.ι Z)]
  simp [Category.assoc]

/-- The analytic-locus restriction square of an adic morphism is a pullback. In particular,
this pullback exists without any finite-type or sheafiness hypotheses on charts. -/
theorem IsAdic.isPullback_analyticLocusMap {f : X ⟶ Y} (hf : IsAdic f) :
    IsPullback hf.analyticLocusMap (analyticLocus.ι X) (analyticLocus.ι Y) f := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ hf.analyticLocusMap_ι) ?_
  refine PullbackCone.isLimitAux'
    (PullbackCone.mk _ _ hf.analyticLocusMap_ι) fun s ↦ ?_
  have hs : Set.range s.snd.hom.base ⊆ X.obj.analyticPoints := by
    rintro _ ⟨t, rfl⟩
    rw [← hf.preimage_analyticPoints]
    have ht : (s.snd ≫ f).hom.base t ∈ Y.obj.analyticPoints := by
      rw [← s.condition]
      exact analyticLocus.range_ι Y ▸ Set.mem_range_self (s.fst.hom.base t)
    exact ht
  refine ⟨analyticLocus.lift s.snd hs, ?_, analyticLocus.lift_ι _ _, ?_⟩
  · rw [← cancel_mono (analyticLocus.ι Y)]
    simp only [PullbackCone.mk_fst, Category.assoc, IsAdic.analyticLocusMap_ι,
      analyticLocus.lift_ι_assoc, s.condition]
  · intro m _ hm
    exact analyticLocus.lift_uniq _ _ m hm

/-- A map from an analytic source factors through the analytic locus of the target exactly
when it is adic. Uniqueness is `analyticLocus.lift_uniq`. -/
theorem isAdic_iff_exists_comp_analyticLocus_ι_eq (g : T ⟶ X)
    (hT : T.obj.analyticPoints = Set.univ) :
    IsAdic g ↔ ∃ l : T ⟶ X.analyticLocus, l ≫ analyticLocus.ι X = g := by
  rw [isAdic_iff_mapsTo_analyticPoints, analyticLocus.exists_comp_ι_eq_iff, hT,
    Set.mapsTo_univ_iff, Set.range_subset_iff]

end TauCeti.AdicSpace
