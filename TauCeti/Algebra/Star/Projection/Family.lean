/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.Orthogonal
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.RingTheory.Idempotents

/-!
# Orthogonal and complete orthogonal projection families

A complete orthogonal projection family is a complete family of orthogonal idempotents whose
members are self-adjoint. For endomorphisms of a Hilbert space, these families describe orthogonal
decompositions of the identity.

The matched overlap `∑ i, Q i * P i` has algebraic block formulas requiring only orthogonal
idempotents. These formulas support simultaneous intertwining of projection families, without
requiring the spectral or polar-decomposition API here.

For any finite pairwise star-orthogonal family of star projections in a non-unital star semiring,
each summand is absorbed by the sum (`p j * ∑ k ∈ s, p k = p j`) and star-orthogonality to the sum
is equivalent to star-orthogonality to every summand.
-/

public section

namespace TauCeti

section FinsetSum
open Function
open scoped StarRing
variable {R ι : Type*} [NonUnitalSemiring R] [StarRing R] {s : Finset ι} {p : ι → R}
/-- For pairwise star-orthogonal star projections on `s`, `p j * ∑ k ∈ s, p k = p j` (`j ∈ s`). -/
theorem mul_sum_of_isStarProjection_of_pairwise_isStarOrtho
    (hp : ∀ k ∈ s, IsStarProjection (p k)) (hortho : (s : Set ι).Pairwise (IsStarOrtho on p))
    {j : ι} (hj : j ∈ s) : p j * ∑ k ∈ s, p k = p j := by
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem j hj fun k hk hkj ↦
    (hortho hj hk hkj.symm).mul_eq_zero' (hp k hk).isSelfAdjoint, (hp j hj).isIdempotentElem.eq]
/-- For pairwise star-orthogonal star projections on `s`, `(∑ k ∈ s, p k) * p j = p j` (`j ∈ s`). -/
theorem sum_mul_of_isStarProjection_of_pairwise_isStarOrtho
    (hp : ∀ k ∈ s, IsStarProjection (p k)) (hortho : (s : Set ι).Pairwise (IsStarOrtho on p))
    {j : ι} (hj : j ∈ s) : (∑ k ∈ s, p k) * p j = p j := by
  rw [Finset.sum_mul, Finset.sum_eq_single_of_mem j hj fun k hk hkj ↦
    (hortho hk hj hkj).mul_eq_zero' (hp j hj).isSelfAdjoint, (hp j hj).isIdempotentElem.eq]
/-- A sum of pairwise star-orthogonal star projections is `⋆⟂ q` iff every summand is. -/
theorem isStarOrtho_sum_left_iff (hp : ∀ k ∈ s, IsStarProjection (p k))
    (hortho : (s : Set ι).Pairwise (IsStarOrtho on p)) {q : R} :
    (∑ k ∈ s, p k) ⋆⟂ q ↔ ∀ j ∈ s, p j ⋆⟂ q :=
  ⟨fun h j hj ↦ ⟨by rw [← mul_sum_of_isStarProjection_of_pairwise_isStarOrtho hp hortho hj,
      mul_assoc, h.mul_star_eq_zero, mul_zero],
    by rw [← sum_mul_of_isStarProjection_of_pairwise_isStarOrtho hp hortho hj,
      ← mul_assoc, h.star_mul_eq_zero, zero_mul]⟩, IsStarOrtho.sum_left⟩
end FinsetSum

variable {R ι : Type*} [Semiring R] [Fintype ι]

/-- A finite family of self-adjoint orthogonal idempotents with sum equal to the identity.
For Hilbert-space endomorphisms, its members are orthogonal projections. -/
structure IsCompleteOrthogonalProjectionFamily [Star R] (P : ι → R) : Prop
    extends CompleteOrthogonalIdempotents P where
  /-- Each member is self-adjoint. -/
  isSelfAdjoint : ∀ i, IsSelfAdjoint (P i)

/-- Every member of a complete orthogonal projection family is a star projection. -/
theorem IsCompleteOrthogonalProjectionFamily.isStarProjection [Star R] {P : ι → R}
    (hP : IsCompleteOrthogonalProjectionFamily P) (i : ι) : IsStarProjection (P i) :=
  ⟨hP.idem i, hP.isSelfAdjoint i⟩

/-- Complete orthogonal projection families are complete orthogonal idempotent families
whose members are star projections. -/
theorem isCompleteOrthogonalProjectionFamily_iff [Star R] (P : ι → R) :
    IsCompleteOrthogonalProjectionFamily P ↔
      CompleteOrthogonalIdempotents P ∧ ∀ i, IsStarProjection (P i) :=
  ⟨fun hP ↦ ⟨hP.toCompleteOrthogonalIdempotents, hP.isStarProjection⟩,
    fun ⟨hP, hPstar⟩ ↦ ⟨hP, fun i ↦ (hPstar i).isSelfAdjoint⟩⟩

/-- The overlap between two projection families, with each source block sent into the
corresponding target block in the endomorphism setting. -/
noncomputable def projectionFamilyOverlap (P Q : ι → R) : R := ∑ i, Q i * P i

/-- The overlap is the sum of the matched projection products. -/
theorem projectionFamilyOverlap_def (P Q : ι → R) :
    projectionFamilyOverlap P Q = ∑ i, Q i * P i := (rfl)

/-- Taking the star of the overlap reverses the two self-adjoint families. -/
@[simp]
theorem star_projectionFamilyOverlap [StarRing R] {P Q : ι → R}
    (hP : ∀ i, IsSelfAdjoint (P i)) (hQ : ∀ i, IsSelfAdjoint (Q i)) :
    star (projectionFamilyOverlap P Q) = projectionFamilyOverlap Q P := by
  simp only [projectionFamilyOverlap_def, star_sum, star_mul,
    fun i ↦ (hP i).star_eq, fun i ↦ (hQ i).star_eq]

end TauCeti

namespace OrthogonalIdempotents

open TauCeti

variable {R ι : Type*} [Semiring R] [Fintype ι] {P Q : ι → R}

/-- Restricting the overlap to a source block retains just its matched product. -/
@[simp]
theorem projectionFamilyOverlap_mul (hP : OrthogonalIdempotents P) (Q : ι → R) (i : ι) :
    projectionFamilyOverlap P Q * P i = Q i * P i := by
  classical
  simp [projectionFamilyOverlap_def, Finset.sum_mul, mul_assoc, hP.mul_eq, mul_ite]

/-- Projecting the overlap onto a target block retains just its matched product. -/
@[simp]
theorem mul_projectionFamilyOverlap (hQ : OrthogonalIdempotents Q) (P : ι → R) (i : ι) :
    Q i * projectionFamilyOverlap P Q = Q i * P i := by
  classical
  simp [projectionFamilyOverlap_def, Finset.mul_sum, ← mul_assoc, hQ.mul_eq, ite_mul]

end OrthogonalIdempotents
