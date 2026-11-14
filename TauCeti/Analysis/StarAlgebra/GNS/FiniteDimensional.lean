/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.StarAlgebra.GNS.Bounded
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# C*-norms from finite-dimensional GNS representations

A finite-dimensional complex star algebra with a faithful positive functional is a C*-algebra
under the operator norm of left multiplication on its GNS space. Traciality is not required.
In particular, this construction applies to finite-dimensional quotients by positive trace
radicals, giving the C*-algebras underlying positive quotient towers.

`StarPositiveFunctional.cstarAlgebra` supplies this norm explicitly, rather than registering a
global instance: the algebra may already carry a different norm. Its faithfulness hypothesis is
`φ.nullSubmodule = ⊥`, equivalently that `φ (star a * a) = 0` implies `a = 0`.
The norm is characterized both by the bounded GNS representation and by the quadratic-form
inequality for left multiplication. The latter uses no preexisting topology on the algebra.

The construction reuses the algebraic GNS quotient and its bounded representation. In finite
dimension the quotient is already complete, and every left multiplication operator is bounded.

## References

* G. J. Murphy, *C*-Algebras and Operator Theory*, §3.3, for the GNS representation.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, for positive traces on
  finite-dimensional Temperley–Lieb quotients.
-/

public section

noncomputable section

open scoped ComplexOrder

namespace TauCeti.StarPositiveFunctional

section NonUnital

variable {A : Type*} [NonUnitalRing A] [Module ℂ A] [StarRing A] [StarModule ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [FiniteDimensional ℂ A]
  (φ : StarPositiveFunctional A)

/-- The algebraic GNS quotient of a finite-dimensional algebra is finite-dimensional. -/
instance : FiniteDimensional ℂ φ.GNS :=
  FiniteDimensional.of_surjective φ.classMap φ.classMap_surjective

end NonUnital

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [FiniteDimensional ℂ A] (φ : StarPositiveFunctional A)

/-- The C*-algebra structure obtained from the operator norm of left multiplication for a
faithful positive functional on a finite-dimensional complex star algebra.

This is not an instance: use `letI := φ.cstarAlgebra hφ` to choose this norm explicitly.
The ring, algebra and involution are the original ones. -/
@[implicit_reducible]
def cstarAlgebra (hφ : φ.nullSubmodule = ⊥) : CStarAlgebra A := by
  let π := φ.boundedRepresentation fun a ↦ (φ.leftMul a).continuous_of_finiteDimensional
  letI := NormedRing.induced A (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) π
    (φ.boundedRepresentation_injective_of_nullSubmodule_eq_bot _ hφ)
  letI := NormedAlgebra.induced ℂ A (φ.HilbertGNS →L[ℂ] φ.HilbertGNS) π
  letI : CompleteSpace A := FiniteDimensional.completeSpace ℂ A
  -- The induced norm is the operator norm, so the C*-identity pulls back along π.
  have hnorm (a : A) : ‖π a‖ * ‖π a‖ ≤ ‖π (star a * a)‖ := by
    rw [map_mul, StarHomClass.map_star]
    exact @CStarRing.norm_mul_self_le (φ.HilbertGNS →L[ℂ] φ.HilbertGNS)
      inferInstance inferInstance inferInstance (π a)
  exact { norm_mul_self_le := hnorm }

/-- The chosen C*-norm is precisely the operator norm of left multiplication on the algebraic
GNS space, which is already complete in finite dimension. -/
@[simp]
theorem norm_cstarAlgebra (hφ : φ.nullSubmodule = ⊥) (a : A) :
    letI := φ.cstarAlgebra hφ
    ‖a‖ = ‖φ.leftMulCLM (φ.leftMul a).continuous_of_finiteDimensional‖ := by
  calc
    _ = ‖φ.boundedRepresentation
        (fun b ↦ (φ.leftMul b).continuous_of_finiteDimensional) a‖ := (rfl)
    _ = _ := by rw [φ.boundedRepresentation_apply, φ.norm_hilbertLeftMul]

/-- A nonnegative number bounds the chosen C*-norm exactly when it bounds the quadratic form
of left multiplication on the GNS space. No trace hypothesis is needed. -/
theorem norm_cstarAlgebra_le_iff (hφ : φ.nullSubmodule = ⊥) (a : A) {R : ℝ} (hR : 0 ≤ R) :
    letI := φ.cstarAlgebra hφ
    ‖a‖ ≤ R ↔ ∀ b : A, φ (star b * star a * a * b) ≤ (R : ℂ) ^ 2 * φ (star b * b) := by
  rw [φ.norm_cstarAlgebra hφ]
  exact φ.norm_leftMulCLM_le_iff (φ.leftMul a).continuous_of_finiteDimensional hR

end TauCeti.StarPositiveFunctional
