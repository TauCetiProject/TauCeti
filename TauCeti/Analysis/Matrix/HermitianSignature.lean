/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.LinearAlgebra.Matrix.Realify
public import TauCeti.LinearAlgebra.Matrix.Signature

/-!
# The signature of a Hermitian complex matrix

The *signature* of a Hermitian matrix over `ℂ` is the number of its positive eigenvalues minus
the number of its negative ones, the difference of the two indices of inertia of the Hermitian
form `x ↦ xᴴ A x`. Unlike the real case there is no ambient linearly ordered field, so this is
not an instance of `Matrix.signature`; the two are related instead through the realification
`Matrix.realify`, which turns the Hermitian form into a real quadratic form of twice the rank
(`Matrix.IsHermitian.signature_realify`).

That identity is what makes the real theory available here. In particular **Sylvester's law of
inertia** over `ℂ` (`Matrix.IsHermitian.signature_congr`: the signature is unchanged by
`A ↦ P * A * Pᴴ` for invertible `P`) follows from its real counterpart
`Matrix.signature_congr`, and the signature of a real symmetric matrix read as a Hermitian
complex matrix is its real signature (`Matrix.IsHermitian.signature_map_ofReal`).

## Main definitions

* `Matrix.IsHermitian.signature`: positive eigenvalues counted against negative ones.

## Main results

* `Matrix.IsHermitian.signature_realify`: the realification has twice the signature.
* `Matrix.IsHermitian.signature_congr`: Sylvester's law of inertia for Hermitian matrices.
* `Matrix.IsHermitian.signature_eq_of_congr_diagonal`: the signature read off an explicit
  diagonalising `*`-congruence.
* `Matrix.IsHermitian.signature_map_ofReal`: a real matrix keeps its real signature.
* `Matrix.IsHermitian.signature_neg` and `Matrix.IsHermitian.signature_map_starRingEnd`:
  negation negates the signature, entrywise conjugation preserves it.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1, for the real theory this reduces to.
-/

public section

namespace Matrix.IsHermitian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}

/-- The signature of a Hermitian complex matrix: its positive eigenvalues counted against its
negative ones. -/
noncomputable def signature (hA : A.IsHermitian) : ℤ :=
  ∑ i, if 0 < hA.eigenvalues i then (1 : ℤ) else if hA.eigenvalues i < 0 then -1 else 0

/-- **The realification of a Hermitian matrix has twice its signature.** Each eigenvalue of a
Hermitian matrix contributes a complex line, hence a real plane, to the realified form. -/
theorem signature_realify (hA : A.IsHermitian) :
    Matrix.signature A.realify = 2 * hA.signature := by
  have hAeq : A = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      (Matrix.diagonal hA.eigenvalues).map ((↑) : ℝ → ℂ) *
      ((hA.eigenvectorUnitary : Matrix ι ι ℂ))ᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_map (by simp)]
    simp [Function.comp_def]
  have hU : IsUnit ((hA.eigenvectorUnitary : Matrix ι ι ℂ)).det := by
    refine (Matrix.isUnit_iff_isUnit_det _).mp ⟨⟨_, ((hA.eigenvectorUnitary : Matrix ι ι ℂ))ᴴ,
      ?_, ?_⟩, rfl⟩
    · simpa [Matrix.star_eq_conjTranspose] using
        Unitary.coe_mul_star_self hA.eigenvectorUnitary
    · simpa [Matrix.star_eq_conjTranspose] using
        Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have key : Matrix.signature A.realify =
      Matrix.signature (Matrix.diagonal hA.eigenvalues) +
        Matrix.signature (Matrix.diagonal hA.eigenvalues) := by
    conv_lhs => rw [hAeq]
    rw [realify_mul, realify_mul, realify_conjTranspose,
      Matrix.signature_congr (Matrix.isUnit_det_realify hU), realify_map_ofReal,
      Matrix.signature_fromBlocks_zero]
  rw [key, Matrix.signature_diagonal, signature]
  ring

/-- **Sylvester's law of inertia for Hermitian matrices.** The signature is unchanged by
`*`-congruence `A ↦ P * A * Pᴴ` with `P` invertible. -/
theorem signature_congr {P : Matrix ι ι ℂ} (hP : IsUnit P.det) (hA : A.IsHermitian)
    (hPA : (P * A * Pᴴ).IsHermitian) : hPA.signature = hA.signature := by
  have h : Matrix.signature (P * A * Pᴴ).realify = Matrix.signature A.realify := by
    rw [realify_mul, realify_mul, realify_conjTranspose,
      Matrix.signature_congr (Matrix.isUnit_det_realify hP)]
  rw [hPA.signature_realify, hA.signature_realify] at h
  omega

/-- **The signature from an explicit diagonalising `*`-congruence.** -/
theorem signature_eq_of_congr_diagonal {P : Matrix ι ι ℂ} (hP : IsUnit P.det) (hA : A.IsHermitian)
    {d : ι → ℝ} (h : P * A * Pᴴ = (Matrix.diagonal d).map ((↑) : ℝ → ℂ)) :
    hA.signature = ∑ i, if 0 < d i then (1 : ℤ) else if d i < 0 then -1 else 0 := by
  have hcongr : Matrix.signature (P * A * Pᴴ).realify = Matrix.signature A.realify := by
    rw [realify_mul, realify_mul, realify_conjTranspose,
      Matrix.signature_congr (Matrix.isUnit_det_realify hP)]
  rw [h, realify_map_ofReal, Matrix.signature_fromBlocks_zero, Matrix.signature_diagonal,
    hA.signature_realify] at hcongr
  omega

/-- A real matrix, read as a Hermitian complex matrix, keeps its real signature. -/
theorem signature_map_ofReal {M : Matrix ι ι ℝ} (hM : (M.map ((↑) : ℝ → ℂ)).IsHermitian) :
    hM.signature = Matrix.signature M := by
  have h := hM.signature_realify
  rw [realify_map_ofReal, Matrix.signature_fromBlocks_zero] at h
  omega

/-- The zero matrix has signature zero. -/
@[simp]
theorem signature_zero (h : (0 : Matrix ι ι ℂ).IsHermitian) : h.signature = 0 := by
  have h' := h.signature_realify
  rw [realify_zero, Matrix.signature_zero] at h'
  omega

/-- Negating a Hermitian matrix negates its signature. -/
theorem signature_neg (hA : A.IsHermitian) (hnA : (-A).IsHermitian) :
    hnA.signature = -hA.signature := by
  have h := hnA.signature_realify
  rw [realify_neg, Matrix.signature_neg, hA.signature_realify] at h
  omega

/-- Conjugating every entry of a Hermitian matrix preserves its signature: it is the congruence
by the reflection negating the imaginary coordinates. -/
theorem signature_map_starRingEnd (hA : A.IsHermitian)
    (hcA : (A.map (starRingEnd ℂ)).IsHermitian) : hcA.signature = hA.signature := by
  have h : Matrix.signature (A.map (starRingEnd ℂ)).realify = Matrix.signature A.realify := by
    rw [realify_map_starRingEnd, Matrix.signature_congr isUnit_det_realifyReflection]
  rw [hcA.signature_realify, hA.signature_realify] at h
  omega

end Matrix.IsHermitian
