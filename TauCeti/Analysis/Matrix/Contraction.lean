/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.Trace
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Contracting an endomorphism of `ℝⁿ` with a matrix

For a real `n × n` matrix `A`, the contraction `H ↦ ∑ᵢⱼ Aᵢⱼ ⟪H eᵢ, eⱼ⟫` of endomorphisms `H` of
`ℝⁿ` is a continuous linear functional. Applied to the Hessian of a function `u`, it is the
non-divergence-form operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` with constant coefficients `A`.

## Main declarations

* `TauCeti.matrixContraction`: the contraction with `A`, as a continuous linear functional.
* `TauCeti.matrixContraction_add`, `TauCeti.matrixContraction_sub`,
  `TauCeti.matrixContraction_smul`: the contraction is linear in the matrix.
* `TauCeti.matrixContraction_one`: contraction with the identity matrix is the trace.
* `TauCeti.abs_matrixContraction_le`: if every entry of `M` is at most `ε` in absolute value,
  then the contraction of `H` with `M` is at most `n² ε ‖H‖` in absolute value.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {n : ℕ}

/-- The contraction `H ↦ ∑ᵢⱼ Aᵢⱼ ⟪H eᵢ, eⱼ⟫` of an endomorphism of `ℝⁿ` with a matrix `A`, as a
continuous linear functional. -/
def matrixContraction (A : Matrix (Fin n) (Fin n) ℝ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace.single i 1))

/-- `TauCeti.matrixContraction A` evaluates to `∑ᵢⱼ Aᵢⱼ ⟪H eᵢ, eⱼ⟫`. -/
@[simp]
theorem matrixContraction_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    matrixContraction A H = ∑ i, ∑ j, A i j *
      ⟪H (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ := by
  simp [matrixContraction, real_inner_comm]

/-- The contraction is additive in the matrix. -/
@[simp]
theorem matrixContraction_add (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixContraction (A + B) = matrixContraction A + matrixContraction B := by
  ext H
  simp [add_mul, Finset.sum_add_distrib]

/-- The contraction commutes with subtraction of matrices. -/
@[simp]
theorem matrixContraction_sub (A B : Matrix (Fin n) (Fin n) ℝ) :
    matrixContraction (A - B) = matrixContraction A - matrixContraction B := by
  ext H
  simp [sub_mul, Finset.sum_sub_distrib]

/-- The contraction is homogeneous in the matrix. -/
@[simp]
theorem matrixContraction_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixContraction (c • A) = c • matrixContraction A := by
  ext H
  simp [mul_assoc, Finset.mul_sum]

/-- Contraction with the identity matrix is the trace. -/
theorem matrixContraction_one :
    matrixContraction (1 : Matrix (Fin n) (Fin n) ℝ) = traceCLM ℝ (EuclideanSpace ℝ (Fin n)) := by
  ext H
  rw [matrixContraction_apply, traceCLM_apply,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp [Matrix.one_apply, real_inner_comm]

/-- If every entry of `M` is at most `ε` in absolute value, then
`|∑ᵢⱼ Mᵢⱼ ⟪H eᵢ, eⱼ⟫| ≤ n² ε ‖H‖`. -/
theorem abs_matrixContraction_le {M : Matrix (Fin n) (Fin n) ℝ} {ε : ℝ}
    (hM : ∀ i j, |M i j| ≤ ε) (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    |matrixContraction M H| ≤ n ^ 2 * ε * ‖H‖ := by
  have h1 : ∀ k : Fin n, ‖EuclideanSpace.single k (1 : ℝ)‖ = 1 := fun k => by simp
  rw [matrixContraction_apply]
  calc |∑ i, ∑ j, M i j * ⟪H (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ|
      ≤ ∑ _i : Fin n, ∑ _j : Fin n, ε * ‖H‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        refine mul_le_mul (hM i j) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hM i j))
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [h1, mul_one]
        exact (H.le_opNorm_of_le (h1 i).le).trans_eq (mul_one _)
    _ = n ^ 2 * ε * ‖H‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end TauCeti
