/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Matrix
public import TauCeti.LinearAlgebra.OrthogonalGroup
public import TauCeti.LinearAlgebra.QuadraticForm.Real

/-!
# Definite real orthogonal groups in Euclidean coordinates

Every positive definite real quadratic form admits Euclidean coordinates, by Mathlib's Sylvester
normal form `QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared`. The coordinate
comparison identifies its orthogonal group with the matrix orthogonal group as a topological
group, and intertwines its action with `TauCeti.orthogonalGroupToLinearIsometryEquiv`.

Negating a form does not change its orthogonal group, so negative definite forms have the same
matrix model. The statements include dimension zero and use the canonical forward-and-inverse
topology on linear automorphisms, not an independently chosen orthogonal-group topology.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §43.
-/

public section

namespace TauCeti

open Matrix

noncomputable section

variable {V n : Type*} [AddCommGroup V] [Module ℝ V] [Fintype n] [DecidableEq n]
  {Q : QuadraticForm ℝ V}

/-- In Euclidean coordinates the abstract orthogonal action is exactly the linear-isometry
action of the associated orthogonal matrix. -/
theorem orthogonalGroupToLinearIsometryEquiv_orthogonalGroupContinuousMulEquivMatrix_apply
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n ℝ)))
    (g : QuadraticMap.orthogonalGroup Q) (x : V) :
    orthogonalGroupToLinearIsometryEquiv
        (orthogonalGroupContinuousMulEquivMatrix
          ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e g)
        ((EuclideanSpace.equiv n ℝ).symm (e x)) =
      (EuclideanSpace.equiv n ℝ).symm (e ((g : V ≃ₗ[ℝ] V) x)) := by
  simp [orthogonalGroupToLinearIsometryEquiv_apply, LinearMap.toMatrix'_mulVec]

variable [FiniteDimensional ℝ V]

/-- The orthogonal group of any definite real quadratic form is topologically isomorphic to
the Euclidean matrix orthogonal group of the same dimension. -/
theorem nonempty_orthogonalGroupContinuousMulEquivMatrix_of_definite
    (hQ : Q.PosDef ∨ (-Q).PosDef) :
    Nonempty (QuadraticMap.orthogonalGroup Q ≃ₜ*
      Matrix.orthogonalGroup (Fin (Module.finrank ℝ V)) ℝ) := by
  rcases hQ with hQ | hQ
  · obtain ⟨e⟩ := nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef hQ
    exact ⟨orthogonalGroupContinuousMulEquivMatrix
      ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e⟩
  · obtain ⟨e⟩ := nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef hQ
    rw [← orthogonalGroup_neg Q]
    exact ⟨orthogonalGroupContinuousMulEquivMatrix
      ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e⟩

end

end TauCeti
