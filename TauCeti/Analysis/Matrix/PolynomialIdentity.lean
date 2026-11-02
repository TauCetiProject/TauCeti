/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
import TauCeti.Analysis.SpecialFunctions.Pow.PolynomialIdentity

/-!
# Polynomial equations on real powers of matrices

For a positive semidefinite real or complex matrix `A`, every polynomial equation in matrix
entries that holds on all natural powers of `A` also holds on all real powers, as defined by
the continuous functional calculus. Thus real powers preserve any set specified by polynomial
entry equations that contains every natural power. This is useful for constructing polar
deformations inside algebraic matrix groups.

Diagonalization expresses each entry of `A ^ t` as a fixed linear combination of powers of its
nonnegative eigenvalues. The scalar identity theorem in
`TauCeti.Analysis.SpecialFunctions.Pow.PolynomialIdentity` then extends the equation. No
invertibility, distinct-eigenvalue or nonempty-index hypothesis is needed; the natural powers
include `A ^ 0 = 1`.
-/

public section

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- A polynomial equation in the entries of a positive semidefinite matrix's powers extends
from all natural powers to all CFC real powers. In particular, it holds at negative exponents. -/
theorem PosSemidef.eval_rpow_eq_zero_of_forall_pow {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (p : MvPolynomial (n × n) 𝕜)
    (h : ∀ k : ℕ, MvPolynomial.eval (fun ij ↦ (A ^ k) ij.1 ij.2) p = 0) (t : ℝ) :
    MvPolynomial.eval (fun ij ↦ (A ^ t) ij.1 ij.2) p = 0 := by
  let U : Matrix n n 𝕜 := hA.isHermitian.eigenvectorUnitary
  have hentry (s : ℝ) (i j : n) :
      (A ^ s) i j = ∑ k, algebraMap ℝ 𝕜 (hA.isHermitian.eigenvalues k ^ s) *
        (U i k * star (U j k)) := by
    rw [CFC.rpow_eq_cfc_real hA.nonneg, hA.isHermitian.cfc_eq]
    rw [IsHermitian.cfc, Unitary.conjStarAlgAut_apply, mul_apply]
    simp [mul_diagonal, U, mul_comm, mul_left_comm, mul_assoc]
  have heval (s : ℝ) : MvPolynomial.eval (fun ij ↦ (A ^ s) ij.1 ij.2) p =
      MvPolynomial.eval (fun ij ↦ ∑ k,
        algebraMap ℝ 𝕜 (hA.isHermitian.eigenvalues k ^ s) *
          (U ij.1 k * star (U ij.2 k))) p := by
    simp_rw [hentry]
  rw [heval]
  apply MvPolynomial.eval_sum_rpow_eq_zero_of_forall_pow p _ hA.eigenvalues_nonneg
  intro k
  have hk := h k
  rw [← CFC.rpow_natCast A k hA.nonneg, heval] at hk
  simpa only [Real.rpow_natCast] using hk

end Matrix
