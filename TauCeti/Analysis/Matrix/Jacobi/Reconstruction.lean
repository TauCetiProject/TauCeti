/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Jacobi.Basic
import TauCeti.Analysis.InnerProductSpace.Lanczos
import TauCeti.Analysis.Matrix.OrthogonalRows
import TauCeti.LinearAlgebra.Matrix.MulVec

/-!
# Spectral reconstruction for real symmetric Jacobi matrices

Applying Lanczos tridiagonalization (`TauCeti.Analysis.InnerProductSpace.Lanczos`) to the diagonal
multiplication operator `T = (diagonal lam).toEuclideanLin` on `EuclideanSpace ℝ (Fin (n + 1))` and
the weighted Vandermonde vectors `w m k = √(q k) * lam k ^ m` realizes every strictly decreasing
sequence `lam : Fin (n + 1) → ℝ` and strictly positive probability vector `q : Fin (n + 1) → ℝ`
(`∑ k, q k = 1`) as the ordered eigenvalues and Lagrange spectral weights of a symmetric Jacobi
matrix with strictly positive subdiagonal entries.

## Main results

* `TauCeti.exists_jacobiEigenvalues_eq_and_jacobiSpectralWeight_eq`: surjectivity of
  `(a, b) ↦ (jacobiEigenvalues a b, jacobiSpectralWeight a b)` from positive-subdiagonal symmetric
  Jacobi matrices onto strictly decreasing spectra and strictly positive probability weights.

## References

* I. Dumitriu, A. Edelman, *Matrix models for beta ensembles*, J. Math. Phys. 43 (2002),
  5830–5847.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.5.1.
-/

public section

noncomputable section

open Matrix Finset InnerProductSpace
open scoped RealInnerProductSpace

namespace TauCeti

section Reconstruction

variable {n : ℕ}

/-- The weighted Vandermonde vectors `w m k = √(q k) * lam k ^ m`. -/
private def spectralVandermondeVec (lam q : Fin (n + 1) → ℝ) (m : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 fun k => Real.sqrt (q k) * lam k ^ m.val

private theorem linearIndependent_spectralVandermondeVec {lam q : Fin (n + 1) → ℝ}
    (hlam : StrictAnti lam) (hq : ∀ k, 0 < q k) :
    LinearIndependent ℝ (spectralVandermondeVec lam q) := by
  refine Fintype.linearIndependent_iff.mpr fun c hc => ?_
  have hsum : ∀ k, ∑ m : Fin (n + 1), c m * lam k ^ (m : ℕ) = 0 := fun k => by
    have hk := congrArg (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x k) hc
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      WithLp.ofLp_zero, Pi.zero_apply, spectralVandermondeVec] at hk
    have hfac : Real.sqrt (q k) * ∑ m : Fin (n + 1), c m * lam k ^ (m : ℕ) = 0 := by
      rw [Finset.mul_sum]
      refine (Finset.sum_congr rfl fun m _ => by ring).trans hk
    exact (mul_eq_zero.mp hfac).resolve_left (Real.sqrt_pos.mpr (hq k)).ne'
  exact fun m => congrFun (Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero hlam.injective hsum) m

private theorem diagMul_spectralVandermondeVec (lam q : Fin (n + 1) → ℝ) (k : Fin n) :
    (Matrix.diagonal lam).toEuclideanLin (spectralVandermondeVec lam q k.castSucc) =
      spectralVandermondeVec lam q k.succ := by
  ext r
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_diagonal, spectralVandermondeVec,
    WithLp.ofLp_toLp, Fin.val_castSucc, Fin.val_succ, pow_succ]
  ring

private theorem gramSchmidtNormed_spectralVandermondeVec_zero {lam q : Fin (n + 1) → ℝ}
    (hq : ∀ k, 0 < q k) (hsum : ∑ k, q k = 1) :
    gramSchmidtNormed ℝ (spectralVandermondeVec lam q) 0 = spectralVandermondeVec lam q 0 := by
  have hnorm0 : ‖spectralVandermondeVec lam q 0‖ = 1 := by
    have hsq : ‖spectralVandermondeVec lam q 0‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [spectralVandermondeVec, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs,
        Fin.val_zero, pow_zero, mul_one]
      simp_rw [Real.sq_sqrt (hq _).le]
      exact hsum
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hsq)
  exact gramSchmidtNormed_eq_self_of_inner_eq_zero (fun _ hj => (not_lt_bot hj).elim) hnorm0

private theorem symmJacobiMatrix_spectralVandermondeVec_eq_conj_diagonal {lam q : Fin (n + 1) → ℝ}
    {Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hQ : ∀ k i, Q k i = gramSchmidtNormed ℝ (spectralVandermondeVec lam q) i k) :
    symmJacobiMatrix
        (fun r => ⟪gramSchmidtNormed ℝ (spectralVandermondeVec lam q) r,
          (Matrix.diagonal lam).toEuclideanLin
            (gramSchmidtNormed ℝ (spectralVandermondeVec lam q) r)⟫)
        (fun k => ‖gramSchmidt ℝ (spectralVandermondeVec lam q) k.castSucc‖⁻¹ *
          ‖gramSchmidt ℝ (spectralVandermondeVec lam q) k.succ‖) =
      Qᵀ * Matrix.diagonal lam * Q := by
  ext i j
  have hT : (Matrix.diagonal lam).toEuclideanLin.IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_diagonal lam)
  have htrid := inner_gramSchmidtNormed_apply_eq_symmJacobiMatrix_map hT
    (diagMul_spectralVandermondeVec lam q) i j
  simp only [Matrix.map_apply, RCLike.re_to_real, Algebra.algebraMap_self,
    RingHom.id_apply] at htrid
  rw [← htrid, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, transpose_apply, hQ, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Matrix.toLpLin_apply, Matrix.mulVec_diagonal, star_trivial]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- **Spectral reconstruction for symmetric Jacobi matrices**: every strictly decreasing tuple of
eigenvalues `lam` and positive spectral weight vector `q` summing to `1` are realized by a symmetric
Jacobi matrix with strictly positive subdiagonal entries. -/
theorem exists_jacobiEigenvalues_eq_and_jacobiSpectralWeight_eq {lam q : Fin (n + 1) → ℝ}
    (hlam : StrictAnti lam) (hq : ∀ k, 0 < q k) (hsum : ∑ k, q k = 1) :
    ∃ (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ),
      (∀ k, 0 < b k) ∧
      jacobiEigenvalues a b = lam ∧
      jacobiSpectralWeight a b = q := by
  let w := spectralVandermondeVec lam q
  have hw_li : LinearIndependent ℝ w := linearIndependent_spectralVandermondeVec hlam hq
  let e := gramSchmidtNormed ℝ w
  let T := (Matrix.diagonal lam).toEuclideanLin
  let a : Fin (n + 1) → ℝ := fun r => ⟪e r, T (e r)⟫
  let b : Fin n → ℝ := fun k => ‖gramSchmidt ℝ w k.castSucc‖⁻¹ * ‖gramSchmidt ℝ w k.succ‖
  have hb_pos : ∀ k, 0 < b k := fun k =>
    mul_pos (inv_pos.mpr (norm_pos_iff.mpr (gramSchmidt_ne_zero k.castSucc hw_li)))
      (norm_pos_iff.mpr (gramSchmidt_ne_zero k.succ hw_li))
  let basisE := gramSchmidtOrthonormalBasis (ι := Fin (n + 1)) finrank_euclideanSpace w
  have hbasisE : ∀ i, basisE i = e i := fun i =>
    gramSchmidtOrthonormalBasis_apply finrank_euclideanSpace
      ((gramSchmidtNormed_orthonormal hw_li).ne_zero i)
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.toMatrix basisE.toBasis
  have hQ_apply : ∀ k i, Q k i = e i k := fun k i => by
    simp [Q, Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr, hbasisE]
  have hQJH : Q * Qᴴ = 1 :=
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toMatrix_orthonormalBasis_self_mul_conjTranspose
      basisE
  have hQQT : Q * Qᵀ = 1 := by rwa [conjTranspose_eq_transpose_of_trivial] at hQJH
  have hJeq : symmJacobiMatrix a b = Qᵀ * Matrix.diagonal lam * Q :=
    symmJacobiMatrix_spectralVandermondeVec_eq_conj_diagonal hQ_apply
  have hlam_eq : jacobiEigenvalues a b = lam := by
    refine jacobiEigenvalues_eq_of_charpoly_eq hlam.antitone ?_
    rw [hJeq, Matrix.charpoly_mul_comm, ← mul_assoc, hQQT, one_mul, Matrix.charpoly_diagonal]
  refine ⟨a, b, hb_pos, hlam_eq, funext fun k => ?_⟩
  have hvk_norm : ‖(WithLp.toLp 2 (Q k) : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
    Matrix.norm_toLp_apply_of_mul_conjTranspose_eq_one hQJH k
  have hvk_eig : symmJacobiMatrix a b *ᵥ ⇑(WithLp.toLp 2 (Q k) : EuclideanSpace ℝ (Fin (n + 1))) =
      jacobiEigenvalues a b k • ⇑(WithLp.toLp 2 (Q k) : EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [hJeq, hlam_eq, WithLp.ofLp_toLp]
    exact Matrix.mul_diagonal_mul_mulVec_col_of_mul_eq_one (P := Qᵀ) hQQT lam k
  rw [jacobiSpectralWeight_eq_sq_eigenvector
    (fun _ hj => by rw [hlam_eq]; exact hlam.injective.ne hj) hvk_norm hvk_eig, PiLp.toLp_apply,
    hQ_apply]
  simp only [e, w, gramSchmidtNormed_spectralVandermondeVec_zero hq hsum,
    spectralVandermondeVec, Fin.val_zero, pow_zero, mul_one, Real.sq_sqrt (hq k).le]

end Reconstruction

end TauCeti
