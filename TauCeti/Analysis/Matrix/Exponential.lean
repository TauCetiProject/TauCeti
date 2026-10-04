/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
-- Non-public: the skew-adjoint scalar criterion for self-adjointness of a scalar multiple is used
-- only inside a proof.
import Mathlib.Algebra.Star.SelfAdjoint

/-!
# The determinant of a matrix exponential

Mathlib records `det (exp A) = exp (trace A)` as an open task. The identity is elementary once `A`
is *diagonalizable*: conjugation leaves both the determinant of the exponential and the trace
alone, and for a diagonal matrix the exponential is diagonal
(`Matrix.exp_diagonal`), so both sides are `∏ i, exp (d i) = exp (∑ i, d i)`.

That special case already covers the matrices the real classical groups are built from. Over an
`RCLike` field a Hermitian matrix is unitarily diagonalizable (Mathlib's
`Matrix.IsHermitian.spectral_theorem`), and over `ℂ` a skew-Hermitian matrix is `-I` times a
Hermitian one, hence diagonalizable as well. So the identity holds on both the Hermitian and the
skew-Hermitian matrices, the second of which is what cuts the *special* unitary group out of the
unitary group; see
`TauCeti/Geometry/Lie/Exponential/Matrix/SpecialUnitary.lean`.

Nothing here proves the identity for a general matrix: over `ℝ` a matrix need not be
diagonalizable even after passing to the algebraic closure, and the general statement goes through
either a triangularization or a derivative of the determinant, neither of which is available.

## Main results

* `Matrix.det_exp_diagonal`: the identity for a diagonal matrix.
* `Matrix.det_exp_of_eq_conj_diagonal`: the identity for a matrix conjugate to a diagonal one.
* `Matrix.IsHermitian.eq_conj_diagonal`: a Hermitian matrix is the conjugate of the diagonal
  matrix of its eigenvalues, with the conjugating matrix inverted rather than starred.
* `Matrix.IsHermitian.det_exp`: **the identity for a Hermitian matrix.**
* `Matrix.det_exp_of_conjTranspose_eq_neg`: **the identity for a skew-Hermitian complex matrix.**

## References

* <https://en.wikipedia.org/wiki/Matrix_exponential>, "Determinant", for the identity and the
  classical proofs of it.
-/

public section

open NormedSpace
open scoped Matrix

noncomputable section

namespace Matrix

section Diagonalizable

variable {m 𝔸 : Type*} [Fintype m] [DecidableEq m]
  [NormedCommRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- The determinant of the exponential of a **diagonal** matrix is the exponential of its trace:
both sides are `∏ i, exp (d i)`. -/
theorem det_exp_diagonal (d : m → 𝔸) : (exp (diagonal d)).det = exp (diagonal d).trace := by
  rw [exp_diagonal, det_diagonal, trace_diagonal, NormedSpace.exp_sum]
  -- The exponential of the diagonal is the pointwise exponential of the entries.
  exact Finset.prod_congr rfl fun i _ => Pi.coe_exp d i

/-- The determinant of the exponential of a **diagonalizable** matrix is the exponential of its
trace. Conjugation commutes with the exponential and fixes both the determinant and the trace, so
the statement reduces to `Matrix.det_exp_diagonal`. -/
theorem det_exp_of_eq_conj_diagonal {A U : Matrix m m 𝔸} (hU : IsUnit U) (d : m → 𝔸)
    (hA : A = U * diagonal d * U⁻¹) : (exp A).det = exp A.trace := by
  rw [hA, exp_conj _ _ hU, det_conj hU, trace_conj hU, det_exp_diagonal]

end Diagonalizable

section Hermitian

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **A Hermitian matrix is conjugate to the diagonal matrix of its eigenvalues.** This is
Mathlib's `Matrix.IsHermitian.spectral_theorem` with the conjugation written multiplicatively and
the adjoint of the eigenvector unitary replaced by its matrix inverse, which is the shape the
determinant, trace and exponential conjugation lemmas consume. -/
theorem IsHermitian.eq_conj_diagonal {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
      (hA.eigenvectorUnitary : Matrix n n 𝕜)⁻¹ := by
  have hinv : (hA.eigenvectorUnitary : Matrix n n 𝕜)⁻¹ =
      ((star hA.eigenvectorUnitary : unitary (Matrix n n 𝕜)) : Matrix n n 𝕜) :=
    inv_eq_right_inv (Unitary.coe_mul_star_self hA.eigenvectorUnitary)
  rw [hinv]
  exact hA.spectral_theorem

/-- **The determinant of the exponential of a Hermitian matrix is the exponential of its trace.**
A Hermitian matrix is unitarily diagonalizable, so this is `Matrix.det_exp_of_eq_conj_diagonal`
applied to the spectral decomposition. -/
theorem IsHermitian.det_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (NormedSpace.exp A).det = NormedSpace.exp A.trace :=
  det_exp_of_eq_conj_diagonal Unitary.isUnit_coe _ hA.eq_conj_diagonal

end Hermitian

section Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A **skew-Hermitian** complex matrix is conjugate to a diagonal matrix: it is `-I` times the
Hermitian matrix `I • A`, whose eigenvector unitary therefore diagonalizes it as well. -/
theorem eq_conj_diagonal_of_conjTranspose_eq_neg {A : Matrix n n ℂ} (hA : Aᴴ = -A) :
    ∃ (U : Matrix n n ℂ) (_ : IsUnit U) (d : n → ℂ), A = U * diagonal d * U⁻¹ := by
  -- `I • A` is Hermitian, since both `I` and `A` are skew-adjoint.
  have hherm : (Complex.I • A).IsHermitian :=
    isHermitian_iff_isSelfAdjoint.mpr
      (isSelfAdjoint_smul_of_mem_skewAdjoint
        (skewAdjoint.mem_iff.mpr (by simp [Complex.conj_I]))
        (skewAdjoint.mem_iff.mpr (by rwa [star_eq_conjTranspose])))
  refine ⟨(hherm.eigenvectorUnitary : Matrix n n ℂ), Unitary.isUnit_coe,
    (-Complex.I) • (RCLike.ofReal ∘ hherm.eigenvalues), ?_⟩
  -- Scaling the diagonalization of `I • A` by `-I` returns `A`.
  rw [diagonal_smul, mul_smul_comm, smul_mul_assoc, ← hherm.eq_conj_diagonal, smul_smul]
  simp [Complex.I_mul_I]

/-- **The determinant of the exponential of a skew-Hermitian complex matrix is the exponential of
its trace.** This is the input that cuts the special unitary group out of the unitary group: the
exponential of a skew-Hermitian matrix is unitary, and it has determinant one as soon as the trace
of the matrix vanishes. The converse fails for a single exponential, since the trace of a
skew-Hermitian matrix is purely imaginary and the exponential is periodic along the imaginary
axis; it is determinant one along the *whole* real exponential line `t ↦ exp (t • A)` that forces
the trace to vanish. -/
theorem det_exp_of_conjTranspose_eq_neg {A : Matrix n n ℂ} (hA : Aᴴ = -A) :
    (exp A).det = exp A.trace := by
  obtain ⟨U, hU, d, hd⟩ := eq_conj_diagonal_of_conjTranspose_eq_neg hA
  exact det_exp_of_eq_conj_diagonal hU d hd

end Complex

end Matrix

end
