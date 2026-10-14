/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Module.LinearMap.End
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

/-- The overlap between two projection families, with each source block sent into the
corresponding target block in the endomorphism setting. -/
noncomputable def projectionFamilyOverlap (P Q : ι → R) : R := ∑ i, Q i * P i

/-- The overlap is the sum of the matched projection products. -/
theorem projectionFamilyOverlap_def (P Q : ι → R) :
    projectionFamilyOverlap P Q = ∑ i, Q i * P i := (rfl)

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

namespace CompleteOrthogonalIdempotents

variable {𝕜 E ι : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [Fintype ι]
  {P : ι → E →ₗ[𝕜] E}

/-- Summing the projected components reconstructs a vector. -/
@[simp]
theorem sum_apply_eq_self (hP : CompleteOrthogonalIdempotents P) (x : E) :
    ∑ i, P i x = x := by
  simpa using LinearMap.congr_fun hP.complete x

end CompleteOrthogonalIdempotents
