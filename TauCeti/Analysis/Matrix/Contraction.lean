/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Topology.Algebra.Module.Trace
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Contracting an endomorphism of `ℝⁿ` with a matrix

For a real `n × n` matrix `A`, the contraction `H ↦ ∑ᵢⱼ Aᵢⱼ ⟪H eᵢ, eⱼ⟫` of endomorphisms `H` of
`ℝⁿ` is a continuous linear functional. Applied to the Hessian of a function `u`, it is the
non-divergence-form operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` with constant coefficients `A`.

## Main declarations

* `Matrix.contraction`: the contraction with `A`, as a continuous linear functional.
* `Matrix.contraction_add`, `Matrix.contraction_sub`, `Matrix.contraction_smul`: the
  contraction is linear in the matrix.
* `Matrix.contraction_one`: contraction with the identity matrix is the trace.
* `Matrix.abs_contraction_le`: if every entry of `M` is at most `ε` in absolute value,
  then the contraction of `H` with `M` is at most `n² ε ‖H‖` in absolute value.
* `Matrix.enorm_contraction_le`: the contraction of `H` with `M` is at most
  `n² (∑ᵢⱼ ‖Mᵢⱼ‖ₑ) ‖H‖ₑ` in extended norm.
* `Matrix.abs_sum_sum_mul_apply_single_single_le`: the same bound for the contraction
  `∑ᵢⱼ Mᵢⱼ B eᵢ eⱼ` of a continuous bilinear form `B`, such as a second derivative.
-/

public section

noncomputable section

namespace Matrix

open scoped InnerProductSpace

open TauCeti

variable {n : ℕ}

/-- The contraction `H ↦ ∑ᵢⱼ Aᵢⱼ ⟪H eᵢ, eⱼ⟫` of an endomorphism of `ℝⁿ` with a matrix `A`, as a
continuous linear functional. -/
def contraction (A : Matrix (Fin n) (Fin n) ℝ) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • (innerSL ℝ (EuclideanSpace.single j (1 : ℝ))).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace.single i 1))

/-- `Matrix.contraction A` evaluates to `∑ᵢⱼ Aᵢⱼ ⟪H eᵢ, eⱼ⟫`. -/
@[simp]
theorem contraction_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    contraction A H = ∑ i, ∑ j, A i j *
      ⟪H (EuclideanSpace.single i 1), EuclideanSpace.single j 1⟫_ℝ := by
  simp [contraction, real_inner_comm]

/-- The contraction is additive in the matrix. -/
@[simp]
theorem contraction_add (A B : Matrix (Fin n) (Fin n) ℝ) :
    contraction (A + B) = contraction A + contraction B := by
  ext H
  simp [add_mul, Finset.sum_add_distrib]

/-- The contraction commutes with subtraction of matrices. -/
@[simp]
theorem contraction_sub (A B : Matrix (Fin n) (Fin n) ℝ) :
    contraction (A - B) = contraction A - contraction B := by
  ext H
  simp [sub_mul, Finset.sum_sub_distrib]

/-- The contraction is homogeneous in the matrix. -/
@[simp]
theorem contraction_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    contraction (c • A) = c • contraction A := by
  ext H
  simp [mul_assoc, Finset.mul_sum]

/-- Contraction with the identity matrix is the trace. -/
theorem contraction_one :
    contraction (1 : Matrix (Fin n) (Fin n) ℝ) = traceCLM ℝ (EuclideanSpace ℝ (Fin n)) := by
  ext H
  rw [contraction_apply, TauCeti.traceCLM_apply,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp [Matrix.one_apply, real_inner_comm]

/-- If every entry of `M` is at most `ε` in absolute value, then
`|∑ᵢⱼ Mᵢⱼ ⟪H eᵢ, eⱼ⟫| ≤ n² ε ‖H‖`. -/
theorem abs_contraction_le {M : Matrix (Fin n) (Fin n) ℝ} {ε : ℝ}
    (hM : ∀ i j, |M i j| ≤ ε) (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    |contraction M H| ≤ n ^ 2 * ε * ‖H‖ := by
  have h1 : ∀ k : Fin n, ‖EuclideanSpace.single k (1 : ℝ)‖ = 1 := fun k => by simp
  rw [contraction_apply]
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

/-- The contraction of `H` with `M` is at most `n² (∑ᵢⱼ ‖Mᵢⱼ‖ₑ) ‖H‖ₑ` in extended norm: the bound
`Matrix.abs_contraction_le` with the sum of the absolute values of the entries as the entrywise
bound. -/
theorem enorm_contraction_le (M : Matrix (Fin n) (Fin n) ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖contraction M H‖ₑ ≤ ENNReal.ofReal (n ^ 2) * (∑ i, ∑ j, ‖M i j‖ₑ) * ‖H‖ₑ := by
  have h := abs_contraction_le (ε := ∑ i, ∑ j, |M i j|) (fun i j =>
    (Finset.single_le_sum (f := fun j => |M i j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))) H
  rw [Real.enorm_eq_ofReal_abs]
  refine (ENNReal.ofReal_le_ofReal h).trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ofReal_norm]
  congr 2
  rw [ENNReal.ofReal_sum_of_nonneg (f := fun i => ∑ j, |M i j|)
    fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (f := fun j => |M i j|) fun _ _ => abs_nonneg _]
  exact Finset.sum_congr rfl fun j _ => (Real.enorm_eq_ofReal_abs _).symm

/-- If every entry of `M` is at most `ε` in absolute value, then for a continuous bilinear form
`B` on `EuclideanSpace ℝ ι`, `|∑ᵢⱼ Mᵢⱼ B eᵢ eⱼ| ≤ (card ι)² ε ‖B‖`. Applied to the second
derivative of a function, this bounds the principal part `∑ᵢⱼ Mᵢⱼ ∂ᵢ∂ⱼh` of a
non-divergence-form operator by the operator norm of the Hessian. -/
theorem abs_sum_sum_mul_apply_single_single_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} {ε : ℝ} (hM : ∀ i j, |M i j| ≤ ε)
    (B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    |∑ i, ∑ j, M i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤
      Fintype.card ι ^ 2 * ε * ‖B‖ := by
  calc |∑ i, ∑ j, M i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)|
      ≤ ∑ _i : ι, ∑ _j : ι, ε * ‖B‖ := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        refine mul_le_mul (hM i j) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hM i j))
        simpa using B.le_opNorm₂ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    _ = Fintype.card ι ^ 2 * ε * ‖B‖ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Matrix
