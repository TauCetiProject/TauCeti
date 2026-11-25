/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Unit eigenvectors of complex matrices

`Matrix.exists_mulVec_eq_smul_and_star_dotProduct_self_eq_one`: as `ℂ` is algebraically closed,
every complex square matrix on a nonempty index type has an eigenvector `v` normalized for the
Hermitian dot product, `star v ⬝ᵥ v = 1`.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n]

open scoped ComplexOrder in
/-- Every complex square matrix on a nonempty index type has an eigenvector `v` of unit length,
`star v ⬝ᵥ v = 1`. -/
theorem exists_mulVec_eq_smul_and_star_dotProduct_self_eq_one [Nonempty n] (A : Matrix n n ℂ) :
    ∃ (μ : ℂ) (v : n → ℂ), A *ᵥ v = μ • v ∧ star v ⬝ᵥ v = 1 := by
  classical
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (toLin' A)
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hAw : A *ᵥ w = μ • w := by simpa using hw.apply_eq_smul
  obtain ⟨t, ht, htw⟩ := RCLike.nonneg_iff_exists_ofReal.mp (dotProduct_star_self_nonneg w)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hw.2 (dotProduct_star_self_eq_zero.mp (by simpa using htw.symm))
  refine ⟨μ, ((Real.sqrt t)⁻¹ : ℂ) • w, by rw [mulVec_smul, hAw, smul_comm], ?_⟩
  rw [star_smul, smul_dotProduct, dotProduct_smul, ← htw, smul_eq_mul, smul_eq_mul]
  have hsqrt : (Real.sqrt t : ℂ) ^ 2 = t := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht]
  have hsqrt0 : (Real.sqrt t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne ht (Ne.symm ht0)))
  rw [← Complex.ofReal_inv, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv]
  field_simp
  exact hsqrt.symm

end Matrix
