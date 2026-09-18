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
# The signature of a Hermitian matrix

The *signature* of a Hermitian matrix is the number of its positive eigenvalues minus the number
of its negative ones, the difference of the two indices of inertia of the Hermitian form
`x ↦ xᴴ A x`. Mathlib's eigenvalues of a Hermitian matrix are real over any `RCLike` field, so
`Matrix.IsHermitian.signature` is defined at that generality.

The theory is then developed over `ℂ`, where the Hermitian form is not a real quadratic form and
the signature is therefore not an instance of `Matrix.signature`. The two are related instead
through the realification `Matrix.realify`, which turns the Hermitian form into a real quadratic
form of twice the rank (`Matrix.IsHermitian.signature_realify`).

That identity is what makes the real theory available here. In particular **Sylvester's law of
inertia** over `ℂ` (`Matrix.IsHermitian.signature_congr`: the signature is unchanged by
`A ↦ P * A * Pᴴ` for invertible `P`) follows from its real counterpart
`Matrix.signature_congr`, and the signature of a real symmetric matrix read as a Hermitian
complex matrix is its real signature (`Matrix.IsHermitian.signature_map_ofReal`).

## Main definitions

* `Matrix.IsHermitian.signature`: positive eigenvalues counted against negative ones.

## Main results

* `Matrix.IsHermitian.signature_diagonal`: over any `RCLike` field, a real diagonal matrix counts
  its positive entries against its negative ones.
* `Matrix.IsHermitian.signature_realify`: the realification has twice the signature.
* `Matrix.IsHermitian.signature_congr`: Sylvester's law of inertia for Hermitian matrices.
* `Matrix.IsHermitian.signature_fromBlocks_zero`: additivity along a block diagonal.
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

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {A : Matrix ι ι 𝕜}

/-- The signature of a Hermitian matrix: its positive eigenvalues counted against its negative
ones.

The eigenvalues do not depend on the decidability of equality on the index type, so the local
decider here is invisible: `Matrix.IsHermitian.signature_def` identifies the definition with the
one read off any `DecidableEq ι` instance. -/
noncomputable def signature (hA : A.IsHermitian) : ℤ :=
  letI := Classical.decEq ι
  ∑ i, if 0 < hA.eigenvalues i then (1 : ℤ) else if hA.eigenvalues i < 0 then -1 else 0

/-- The signature read off the eigenvalues for any `DecidableEq ι` instance. -/
theorem signature_def [DecidableEq ι] (hA : A.IsHermitian) :
    hA.signature =
      ∑ i, if 0 < hA.eigenvalues i then (1 : ℤ) else if hA.eigenvalues i < 0 then -1 else 0 := by
  rw [signature, Subsingleton.elim (Classical.decEq ι) ‹DecidableEq ι›]

/-- The zero matrix has signature zero: all its eigenvalues vanish. -/
@[simp]
theorem signature_zero :
    (Matrix.isHermitian_zero : (0 : Matrix ι ι 𝕜).IsHermitian).signature = 0 := by
  classical
  rw [signature_def,
    (Matrix.isHermitian_zero : (0 : Matrix ι ι 𝕜).IsHermitian).eigenvalues_eq_zero_iff.mpr rfl]
  simp

/-- **The signature of a real diagonal matrix** counts its positive entries against its negative
ones: the diagonal entries are the eigenvalues, up to the order in which they are listed. -/
@[simp]
theorem signature_diagonal [DecidableEq ι] {d : ι → ℝ} :
    (Matrix.isHermitian_diagonal_of_self_adjoint (fun i => (d i : 𝕜))
      (by ext i; simp)).signature =
      ∑ i, if 0 < d i then (1 : ℤ) else if d i < 0 then -1 else 0 := by
  suffices ∀ hd : (Matrix.diagonal fun i => (d i : 𝕜)).IsHermitian,
      hd.signature = ∑ i, if 0 < d i then (1 : ℤ) else if d i < 0 then -1 else 0 from this _
  intro hd
  -- Both lists of reals are the real parts of the roots of the characteristic polynomial.
  have h : Multiset.map hd.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
    have hr := congrArg (Multiset.map RCLike.re) hd.roots_charpoly_eq_eigenvalues
    rw [charpoly_diagonal, Polynomial.roots_prod _ _
      (by simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at hr
    simpa [Multiset.map_map, Function.comp_def, Multiset.bind_singleton] using hr.symm
  have hsum (e : ι → ℝ) : (∑ i, if 0 < e i then (1 : ℤ) else if e i < 0 then -1 else 0) =
      (Multiset.map (fun x : ℝ => if 0 < x then (1 : ℤ) else if x < 0 then -1 else 0)
        (Multiset.map e Finset.univ.val)).sum := by
    rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
    rfl
  rw [signature_def, hsum, h, ← hsum]

/-- Reindexing both coordinates of a Hermitian matrix along an equivalence does not change its
signature. -/
@[simp]
theorem signature_submatrix_equiv_self (e : ι ≃ κ) (hA : A.IsHermitian) :
    (hA.submatrix e.symm).signature = hA.signature := by
  classical
  let hB : (A.submatrix e.symm e.symm).IsHermitian := hA.submatrix e.symm
  change hB.signature = hA.signature
  have hroots : Multiset.map hB.eigenvalues Finset.univ.val =
      Multiset.map hA.eigenvalues Finset.univ.val := by
    calc
      Multiset.map hB.eigenvalues Finset.univ.val =
          Multiset.map RCLike.re (A.submatrix e.symm e.symm).charpoly.roots := by
        rw [hB.roots_charpoly_eq_eigenvalues]
        simp [Multiset.map_map]
      _ = Multiset.map RCLike.re A.charpoly.roots := by
        rw [← Matrix.reindex_apply e e A, Matrix.charpoly_reindex]
      _ = Multiset.map hA.eigenvalues Finset.univ.val := by
        rw [hA.roots_charpoly_eq_eigenvalues]
        simp [Multiset.map_map]
  rw [signature_def, signature_def]
  calc
    (∑ i, if 0 < hB.eigenvalues i then (1 : ℤ) else if hB.eigenvalues i < 0 then -1 else 0) =
        (Multiset.map (fun x : ℝ => if 0 < x then (1 : ℤ) else if x < 0 then -1 else 0)
          (Multiset.map hB.eigenvalues Finset.univ.val)).sum := by
      rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
      rfl
    _ = (Multiset.map (fun x : ℝ => if 0 < x then (1 : ℤ) else if x < 0 then -1 else 0)
          (Multiset.map hA.eigenvalues Finset.univ.val)).sum := by rw [hroots]
    _ = ∑ i, if 0 < hA.eigenvalues i then (1 : ℤ) else if hA.eigenvalues i < 0 then -1 else 0 :=
      by
        rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
        simp

end RCLike

section Complex

variable {A : Matrix ι ι ℂ}

/-- **The realification of a Hermitian matrix has twice its signature.** Each eigenvalue of a
Hermitian matrix contributes a complex line, hence a real plane, to the realified form. -/
theorem signature_realify (hA : A.IsHermitian) :
    Matrix.signature A.realify = 2 * hA.signature := by
  classical
  have hAeq : A = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      (Matrix.diagonal hA.eigenvalues).map ((↑) : ℝ → ℂ) *
      ((hA.eigenvectorUnitary : Matrix ι ι ℂ))ᴴ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_map (by simp)]
    simp [Function.comp_def]
  have hU : IsUnit ((hA.eigenvectorUnitary : Matrix ι ι ℂ)).det := by
    exact (Matrix.isUnit_iff_isUnit_det
      (hA.eigenvectorUnitary : Matrix ι ι ℂ)).mp Unitary.isUnit_coe
  have key : Matrix.signature A.realify =
      Matrix.signature (Matrix.diagonal hA.eigenvalues) +
        Matrix.signature (Matrix.diagonal hA.eigenvalues) := by
    conv_lhs => rw [hAeq]
    rw [realify_mul, realify_mul, realify_conjTranspose,
      Matrix.signature_congr (Matrix.isUnit_det_realify hU), realify_map_ofReal,
      Matrix.signature_fromBlocks_zero]
  rw [key, Matrix.signature_diagonal, signature_def]
  ring

/-- **Sylvester's law of inertia for Hermitian matrices.** The signature is unchanged by
`*`-congruence `A ↦ P * A * Pᴴ` with `P` invertible. -/
theorem signature_congr [DecidableEq ι] {P : Matrix ι ι ℂ} (hP : IsUnit P.det)
    (hA : A.IsHermitian) :
    (Matrix.isHermitian_mul_mul_conjTranspose P hA).signature = hA.signature := by
  have h : Matrix.signature (P * A * Pᴴ).realify = Matrix.signature A.realify := by
    rw [realify_mul, realify_mul, realify_conjTranspose,
      Matrix.signature_congr (Matrix.isUnit_det_realify hP)]
  rw [(Matrix.isHermitian_mul_mul_conjTranspose P hA).signature_realify,
    hA.signature_realify] at h
  omega

/-- A real matrix, read as a Hermitian complex matrix, keeps its real signature. -/
@[simp]
theorem signature_map_ofReal {M : Matrix ι ι ℝ} (hM : (M.map ((↑) : ℝ → ℂ)).IsHermitian) :
    hM.signature = Matrix.signature M := by
  have h := hM.signature_realify
  rw [realify_map_ofReal, Matrix.signature_fromBlocks_zero] at h
  omega

/-- **The signature from an explicit diagonalising `*`-congruence.** -/
theorem signature_eq_of_congr_diagonal [DecidableEq ι] {P : Matrix ι ι ℂ} (hP : IsUnit P.det)
    (hA : A.IsHermitian) {d : ι → ℝ} (h : P * A * Pᴴ = (Matrix.diagonal d).map ((↑) : ℝ → ℂ)) :
    hA.signature = ∑ i, if 0 < d i then (1 : ℤ) else if d i < 0 then -1 else 0 := by
  -- `h` rewrites the matrix under a Hermiticity proof, so read it off a universally
  -- quantified matrix, where it becomes a substitution.
  have key : ∀ {B : Matrix ι ι ℂ} (hB : B.IsHermitian),
      B = (Matrix.diagonal d).map ((↑) : ℝ → ℂ) →
        hB.signature = ∑ i, if 0 < d i then (1 : ℤ) else if d i < 0 then -1 else 0 := by
    rintro B hB rfl
    rw [signature_map_ofReal, Matrix.signature_diagonal]
  rw [← hA.signature_congr hP]
  exact key _ h

/-- **Additivity of the signature along a block diagonal.** The realification of a
block-diagonal matrix is, after reindexing, the block diagonal of the two realifications. -/
@[simp]
theorem signature_fromBlocks_zero {B : Matrix κ κ ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (hA.fromBlocks Matrix.conjTranspose_zero hB).signature = hA.signature + hB.signature := by
  classical
  have hshuffle : (Matrix.fromBlocks A 0 0 B).realify.submatrix
      (Equiv.sumSumSumComm ι ι κ κ) (Equiv.sumSumSumComm ι ι κ κ) =
      Matrix.fromBlocks A.realify 0 0 B.realify := by
    ext p q
    rcases p with (i | i) | (k | k) <;> rcases q with (j | j) | (l | l) <;>
      simp [Equiv.sumSumSumComm]
  have key : Matrix.signature (Matrix.fromBlocks A 0 0 B).realify =
      Matrix.signature A.realify + Matrix.signature B.realify := by
    rw [← Matrix.signature_submatrix_equiv_self (Equiv.sumSumSumComm ι ι κ κ).symm,
      Equiv.symm_symm, hshuffle,
      Matrix.signature_fromBlocks_zero]
  rw [(hA.fromBlocks Matrix.conjTranspose_zero hB).signature_realify, hA.signature_realify,
    hB.signature_realify] at key
  omega

/-- Negating a Hermitian matrix negates its signature. -/
@[simp]
theorem signature_neg (hA : A.IsHermitian) : hA.neg.signature = -hA.signature := by
  have h := hA.neg.signature_realify
  rw [realify_neg, Matrix.signature_neg, hA.signature_realify] at h
  omega

/-- Conjugating every entry of a Hermitian matrix preserves its signature: it is the congruence
by the reflection negating the imaginary coordinates. -/
@[simp]
theorem signature_map_starRingEnd (hA : A.IsHermitian) :
    (hA.map (starRingEnd ℂ) (by simp [Function.Semiconj])).signature = hA.signature := by
  classical
  have h : Matrix.signature (A.map (starRingEnd ℂ)).realify = Matrix.signature A.realify := by
    rw [realify_map_starRingEnd, Matrix.signature_congr TauCeti.isUnit_det_realifyReflection]
  rw [(hA.map (starRingEnd ℂ) (by simp [Function.Semiconj])).signature_realify,
    hA.signature_realify] at h
  omega

end Complex

end Matrix.IsHermitian
