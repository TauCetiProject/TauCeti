/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.RingTheory.Idempotents

/-!
# Complete orthogonal projection families

A complete orthogonal projection family is a complete family of orthogonal idempotents whose
members are self-adjoint. For endomorphisms of a Hilbert space, these families describe orthogonal
decompositions of the identity.

The matched overlap `∑ i, Q i * P i` has algebraic block formulas requiring only orthogonal
idempotents. These formulas support simultaneous intertwining of projection families, without
requiring the spectral or polar-decomposition API here.
-/

public section

namespace TauCeti

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

/-- The overlap intertwines each source idempotent with its matched target idempotent. -/
theorem projectionFamilyOverlap_mul_eq_mul_projectionFamilyOverlap
    (hP : OrthogonalIdempotents P) (hQ : OrthogonalIdempotents Q) (i : ι) :
    projectionFamilyOverlap P Q * P i = Q i * projectionFamilyOverlap P Q := by
  simp only [hP.projectionFamilyOverlap_mul, hQ.mul_projectionFamilyOverlap]

end OrthogonalIdempotents
