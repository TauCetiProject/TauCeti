/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Common affine neighborhoods in projective spectra

Every finite set of relevant homogeneous primes misses one homogeneous element of positive
degree. Its basic open is affine. Pulling back that open along an affine morphism gives a
common affine neighborhood of a prescribed finite set in its source.

No field, finite generation, degree-one generation or nonempty-set hypothesis is required.
The homogeneous prime-avoidance argument raises two sections to a common degree before adding
them, so it applies over finite fields as well.

These neighborhoods supply affine charts around finite divisor supports and the finite
orbits used in descent of projective Picard charts.

## Main results

* `ProjectiveSpectrum.exists_homogeneous_notMem_of_finset`: one positive-degree homogeneous
  section avoiding every point in a finite set.
* `AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_superset_of_proj`: common affine
  neighborhoods under an affine morphism to a projective spectrum.

-/

public section

variable {coefficients gradedPiece : Type*} [CommRing coefficients]
  [SetLike gradedPiece coefficients] [AddSubgroupClass gradedPiece coefficients]
  {grading : ℕ → gradedPiece} [GradedRing grading]

namespace ProjectiveSpectrum

/-- A finite set of relevant homogeneous primes misses a common homogeneous element
of positive degree. -/
theorem exists_homogeneous_notMem_of_finset (points : Finset (ProjectiveSpectrum grading)) :
    ∃ degree > 0, ∃ homogeneousElement ∈ grading degree,
      ∀ point ∈ points, homogeneousElement ∉ point.asHomogeneousIdeal := by
  classical
  induction points using Finset.strongInduction with
  | H points inductionHypothesis =>
    rcases points.eq_empty_or_nonempty with rfl | nonemptyPoints
    · exact ⟨1, one_pos, 0, zero_mem _, by simp⟩
    obtain ⟨minimalPoint, minimality⟩ := points.exists_minimal nonemptyPoints
    obtain ⟨degree, positiveDegree, homogeneousElement, homogeneous, avoidsOthers⟩ :=
      inductionHypothesis (points.erase minimalPoint)
        (Finset.erase_ssubset minimality.prop)
    by_cases outsideMinimal : homogeneousElement ∉ minimalPoint.asHomogeneousIdeal
    · refine ⟨degree, positiveDegree, homogeneousElement, homogeneous, fun point membership ↦ ?_⟩
      by_cases equality : point = minimalPoint
      · exact equality ▸ outsideMinimal
      · exact avoidsOthers point (Finset.mem_erase.mpr ⟨equality, membership⟩)
    rw [not_not] at outsideMinimal
    have separatingSection (point : points.erase minimalPoint) :
        ∃ degree, ∃ homogeneousElement ∈ grading degree,
          homogeneousElement ∈ point.1.asHomogeneousIdeal ∧
            homogeneousElement ∉ minimalPoint.asHomogeneousIdeal := by
      have notBelow : ¬ point.1.asHomogeneousIdeal ≤ minimalPoint.asHomogeneousIdeal :=
        fun inclusion ↦ (Finset.mem_erase.mp point.2).1
          (le_antisymm inclusion (minimality.2 (Finset.mem_erase.mp point.2).2 inclusion))
      exact HomogeneousIdeal.exists_homogeneous_mem_notMem_of_not_le notBelow
    choose separatingDegree separatingElement separatingHomogeneous inOtherPrime
      outsideMinimalPrime using separatingSection
    let index := (AlgebraicGeometry.Proj.affineOpenCover grading).idx minimalPoint
    let initialDegree := index.1.val
    have positiveInitialDegree : 0 < initialDegree := index.1.property
    let initialElement : coefficients := index.2
    have initialHomogeneous : initialElement ∈ grading initialDegree := index.2.property
    have initialOutside : initialElement ∉ minimalPoint.asHomogeneousIdeal := by
      have membership := (AlgebraicGeometry.Proj.affineOpenCover grading).covers minimalPoint
      -- The chosen cover index is its away chart; exposing that chart identifies its
      -- range with the basic open via opensRange_awayι.
      change minimalPoint ∈ (AlgebraicGeometry.Proj.awayι grading initialElement
        initialHomogeneous positiveInitialDegree).opensRange at membership
      rwa [AlgebraicGeometry.Proj.opensRange_awayι] at membership
    -- Multiply the separating sections with a positive-degree section missing the minimum.
    let totalDegree := initialDegree +
      ∑ point ∈ (points.erase minimalPoint).attach, separatingDegree point
    let productSection := initialElement *
      ∏ point ∈ (points.erase minimalPoint).attach, separatingElement point
    have productHomogeneous : productSection ∈ grading totalDegree :=
      SetLike.mul_mem_graded initialHomogeneous
        (SetLike.prod_mem_graded _ _ _ (fun point _ ↦ separatingHomogeneous point))
    have productOutside : productSection ∉ minimalPoint.asHomogeneousIdeal := by
      refine minimalPoint.isPrime.mul_notMem initialOutside ?_
      rw [Ideal.IsPrime.prod_mem_iff (hp := minimalPoint.isPrime)]
      push Not
      exact fun point _ ↦ outsideMinimalPrime point
    have productInOther (point : points.erase minimalPoint) :
        productSection ∈ point.1.asHomogeneousIdeal :=
      Ideal.mul_mem_left _ _ (Ideal.mem_of_dvd _
        (Finset.dvd_prod_of_mem _ (Finset.mem_attach _ point)) (inOtherPrime point))
    have positiveTotalDegree : 0 < totalDegree :=
      lt_of_lt_of_le positiveInitialDegree (Nat.le_add_right _ _)
    -- Raise both sections to a common degree before adding, preserving every avoidance.
    refine ⟨degree * totalDegree, Nat.mul_pos positiveDegree positiveTotalDegree,
      homogeneousElement ^ totalDegree + productSection ^ degree, add_mem ?_ ?_,
      fun point membership ↦ ?_⟩
    · simpa [mul_comm] using SetLike.pow_mem_graded totalDegree homogeneous
    · simpa using SetLike.pow_mem_graded degree productHomogeneous
    · by_cases equality : point = minimalPoint
      · subst equality
        intro inPrime
        exact productOutside (point.isPrime.mem_of_pow_mem degree
          ((Ideal.add_mem_iff_right _
            (Ideal.pow_mem_of_mem _ outsideMinimal totalDegree positiveTotalDegree)).mp inPrime))
      · have inErased : point ∈ points.erase minimalPoint :=
          Finset.mem_erase.mpr ⟨equality, membership⟩
        intro inPrime
        exact avoidsOthers point inErased (point.isPrime.mem_of_pow_mem totalDegree
          ((Ideal.add_mem_iff_left _
            (Ideal.pow_mem_of_mem _ (productInOther ⟨point, inErased⟩)
              degree positiveDegree)).mp inPrime))

end ProjectiveSpectrum

open CategoryTheory
open scoped AlgebraicGeometry

/-- A finite set in the source of an affine morphism to a projective spectrum lies in a common
affine open, without any assumption on the coefficient ring or the grading. -/
theorem AlgebraicGeometry.Scheme.Hom.exists_isAffineOpen_superset_of_proj
    {X : AlgebraicGeometry.Scheme} (f : X ⟶ AlgebraicGeometry.Proj grading)
    [AlgebraicGeometry.IsAffineHom f] {s : Set X} (hs : s.Finite) :
    ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧ s ⊆ U := by
  classical
  obtain ⟨n, hn, a, ha, havoid⟩ :=
    ProjectiveSpectrum.exists_homogeneous_notMem_of_finset (grading := grading)
      (hs.image f.base).toFinset
  refine ⟨f ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen grading a,
    (AlgebraicGeometry.Proj.isAffineOpen_basicOpen grading a ha hn).preimage f, ?_⟩
  intro x hx
  exact havoid (f x) ((hs.image f.base).mem_toFinset.mpr (Set.mem_image_of_mem f.base hx))
