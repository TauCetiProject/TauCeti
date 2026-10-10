/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Matrix
public import TauCeti.LinearAlgebra.OrthogonalGroup
import Mathlib.LinearAlgebra.QuadraticForm.Real

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
theorem orthogonalGroupContinuousEquivMatrix_action
    (e : Q.IsometryEquiv (Matrix.toQuadraticForm' (1 : Matrix n n ℝ)))
    (g : QuadraticMap.orthogonalGroup Q) (x : V) :
    orthogonalGroupToLinearIsometryEquiv
        (orthogonalGroupContinuousEquivMatrix
          ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e g)
        ((EuclideanSpace.equiv n ℝ).symm (e x)) =
      (EuclideanSpace.equiv n ℝ).symm (e ((g : V ≃ₗ[ℝ] V) x)) := by
  simp [orthogonalGroupToLinearIsometryEquiv_apply, LinearMap.toMatrix'_mulVec]

variable [FiniteDimensional ℝ V]

/-- A positive definite real quadratic form admits Euclidean coordinates and the resulting
topological identification of its orthogonal group with the matrix orthogonal group. -/
theorem exists_orthogonalGroupContinuousEquivMatrix_of_posDef (hQ : Q.PosDef) :
    ∃ _e : Q.IsometryEquiv
        (Matrix.toQuadraticForm' (1 : Matrix (Fin (Module.finrank ℝ V))
          (Fin (Module.finrank ℝ V)) ℝ)),
      Nonempty (QuadraticMap.orthogonalGroup Q ≃ₜ*
        Matrix.orthogonalGroup (Fin (Module.finrank ℝ V)) ℝ) := by
  obtain ⟨w, hw, ⟨e⟩⟩ := Q.equivalent_one_zero_neg_one_weighted_sum_squared
  have hwpos (i : Fin (Module.finrank ℝ V)) : 0 < w i := by
    have h := hQ (e.symm (Pi.single i 1)) (by simp)
    rw [← e.map_app] at h
    simpa [QuadraticMap.weightedSumSquares_apply, Pi.single_apply,
      Finset.sum_ite_eq'] using h
  have hwone : w = 1 := funext fun i ↦ by
    rcases hw i with h | h | h <;> have := hwpos i <;> norm_num [h] at *
  have hstandard : QuadraticMap.weightedSumSquares ℝ w =
      Matrix.toQuadraticForm' (1 : Matrix (Fin (Module.finrank ℝ V))
        (Fin (Module.finrank ℝ V)) ℝ) := by
    rw [hwone]
    ext x
    simp [toQuadraticForm'_one_apply, QuadraticMap.weightedSumSquares_apply, dotProduct]
  rw [hstandard] at e
  exact ⟨e, ⟨orthogonalGroupContinuousEquivMatrix
    ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e⟩⟩

/-- The orthogonal group of any definite real quadratic form is topologically isomorphic to
the Euclidean matrix orthogonal group of the same dimension. -/
theorem nonempty_orthogonalGroupContinuousEquivMatrix_of_definite
    (hQ : Q.PosDef ∨ (-Q).PosDef) :
    Nonempty (QuadraticMap.orthogonalGroup Q ≃ₜ*
      Matrix.orthogonalGroup (Fin (Module.finrank ℝ V)) ℝ) := by
  rcases hQ with hQ | hQ
  · obtain ⟨_, h⟩ := exists_orthogonalGroupContinuousEquivMatrix_of_posDef hQ
    exact h
  · obtain ⟨_, ⟨E⟩⟩ := exists_orthogonalGroupContinuousEquivMatrix_of_posDef hQ
    have h : QuadraticMap.orthogonalGroup Q = QuadraticMap.orthogonalGroup (-Q) := by
      ext g
      simp
    rw [h]
    exact ⟨E⟩

end

end TauCeti
