/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Projection.ProjectiveModule
public import TauCeti.Analysis.Matrix.ProjectionKZero
public import Mathlib.Analysis.Complex.Basic

/-!
# Checks for the comparison of projections and idempotents

The idempotent `e = [[1, 1], [0, 0]]` in `M₂(ℂ)` satisfies `e² = e` but is not self-adjoint. Its
column range is `ℂ × 0`, whose orthogonal projection is `p = diag(1, 0)`, and indeed `e * p = p`
and `p * e = e`. So the inverse of the comparison `V(ℂ) ≃+ IdempotentMonoid ℂ` sends the class
of `e` to the class of `diag(1, 0)`, whose rank is `1`: a comparison defined only on self-adjoint
representatives must first replace `e` by `p`.
-/

public section

open Matrix

namespace TauCeti.ProjectiveModuleExample

/-- The non-self-adjoint idempotent `[[1, 1], [0, 0]]` in `M₂(ℂ)`. -/
def oblique : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 0, 0]

/-- `[[1, 1], [0, 0]]` is idempotent. -/
theorem isIdempotentElem_oblique : IsIdempotentElem oblique := by
  rw [IsIdempotentElem, oblique]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `[[1, 1], [0, 0]]` is not self-adjoint. -/
theorem not_isSelfAdjoint_oblique : ¬IsSelfAdjoint oblique := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [oblique] at this

/-- `diag(1, 0)`, the matrix unit `E₀₀`, is a projection. -/
theorem isStarProjection_single : IsStarProjection (single 0 0 1 : Matrix (Fin 2) (Fin 2) ℂ) :=
  (isMurrayVonNeumannEquivalent_single_one_one (n := Fin 1) 0).isStarProjection_left

/-- `diag(1, 0)` is the range projection of `[[1, 1], [0, 0]]`: `e * p = p` and `p * e = e`. -/
theorem oblique_mul_single : oblique * single 0 0 1 = single 0 0 1 ∧
    single 0 0 1 * oblique = oblique := by
  refine ⟨?_, ?_⟩ <;>
  · rw [oblique]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The class of `[[1, 1], [0, 0]]` is `1`.** The inverse of the comparison of projections with
idempotents sends it to the class of `diag(1, 0)`, of rank `1`. -/
theorem rankAddEquiv_idempotentMonoidEquiv_symm_mk_oblique :
    ProjectionMonoid.rankAddEquiv ℂ ((ProjectionMonoid.idempotentMonoidEquiv ℂ).symm
      (IdempotentMonoid.mk oblique isIdempotentElem_oblique)) = 1 := by
  rw [ProjectionMonoid.idempotentMonoidEquiv_symm_mk isIdempotentElem_oblique
    isStarProjection_single oblique_mul_single.1 oblique_mul_single.2,
    ProjectionMonoid.mk_eq_mk (isMurrayVonNeumannEquivalent_single_one_one (n := Fin 1) 0),
    ProjectionMonoid.rankAddEquiv_mk]
  simp

end TauCeti.ProjectiveModuleExample
