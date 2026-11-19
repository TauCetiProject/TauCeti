/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Entrywise norms of complex eigenvectors of nonnegative real matrices

Let `A` be an entrywise nonnegative real square matrix, viewed as a complex matrix. If `A z = μ z`
for a complex vector `z`, then the triangle inequality in each row gives `‖μ‖ ‖z‖ ≤ A ‖z‖`
entrywise, where `‖z‖` is the real vector of moduli of the entries of `z`. Comparison theorems for
nonnegative real matrices, such as the Collatz–Wielandt bound of Perron–Frobenius theory, then
control the complex eigenvalues of `A` through this real inequality.

## Main results

* `Matrix.norm_smul_le_mulVec_norm`: `‖μ‖ ‖z‖ ≤ A ‖z‖` entrywise for a complex eigenvector `z` of
  an entrywise nonnegative real matrix `A`.
-/

public section

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] {A : Matrix n n ℝ}

/-- For an entrywise nonnegative real matrix `A` and a complex eigenvector `z` for `μ`, the moduli
of the entries of `z` satisfy `‖μ‖ ‖z‖ ≤ A ‖z‖`, by the triangle inequality. -/
theorem norm_smul_le_mulVec_norm (hA : ∀ i j, 0 ≤ A i j) {μ : ℂ} {z : n → ℂ}
    (hAz : A.map (↑) *ᵥ z = μ • z) : ‖μ‖ • (fun i => ‖z i‖) ≤ A *ᵥ fun i => ‖z i‖ := by
  intro i
  calc ‖μ‖ * ‖z i‖ = ‖(A.map (↑) *ᵥ z) i‖ := by simp [hAz]
    _ ≤ ∑ j, ‖((A i j : ℝ) : ℂ) * z j‖ := norm_sum_le _ _
    _ = (A *ᵥ fun i => ‖z i‖) i := by
      simp [mulVec, dotProduct, Complex.norm_real, abs_of_nonneg (hA i _)]

end Matrix
