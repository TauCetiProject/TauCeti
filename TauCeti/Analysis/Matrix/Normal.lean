/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.JointDiagonalization

/-!
# Unitary diagonalization of normal matrices

A complex square matrix `A` is **normal** when it commutes with its conjugate transpose,
`IsStarNormal A`. The spectral theorem for normal matrices says that such a matrix is unitarily
diagonalizable: `star U * A * U` is diagonal for some unitary `U`. Mathlib proves this for Hermitian
matrices (`Matrix.IsHermitian.spectral_theorem`); this file extends it to normal ones as the
singleton case of `TauCeti.exists_mem_unitaryGroup_forall_star_mul_mul_eq_diagonal`.
The columns of `U` are an orthonormal basis of eigenvectors of `A`.

Unitary matrices are normal, so in particular every unitary matrix is conjugate within the unitary
group to a diagonal one. This is the statement that every element of `U(n)` lies in a conjugate of
the diagonal torus.

## Main results

* `Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal`: **the spectral theorem for normal
  matrices**, a normal complex matrix is diagonalized by a unitary matrix.

## References

* S. Axler, *Linear Algebra Done Right*, 3rd ed., Springer (2015), Theorem 7.24 (the complex
  spectral theorem).
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The spectral theorem for normal matrices.** A normal complex matrix is unitarily
diagonalizable: there is a unitary matrix `U` with `star U * A * U` diagonal. -/
theorem exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (A : Matrix n n ℂ) [IsStarNormal A] :
    ∃ U ∈ unitaryGroup n ℂ, ∃ d : n → ℂ, star U * A * U = diagonal d := by
  obtain ⟨U, hU, d, hd⟩ := TauCeti.exists_mem_unitaryGroup_forall_star_mul_mul_eq_diagonal
    (fun _ : Unit => A) (fun _ => inferInstance) (fun _ _ _ => Commute.refl _)
  exact ⟨U, hU, d (), hd ()⟩

end Matrix
