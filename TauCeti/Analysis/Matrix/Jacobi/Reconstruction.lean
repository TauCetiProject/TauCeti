/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import TauCeti.Analysis.Matrix.Jacobi.Basic
import Mathlib.LinearAlgebra.Vandermonde
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho
import TauCeti.Analysis.Matrix.OrthogonalRows
import TauCeti.LinearAlgebra.Matrix.MulVec

/-!
# Lanczos tridiagonalization and spectral reconstruction for real Jacobi matrices

For any inner product space `E` over `𝕜` (`ℝ` or `ℂ`), any symmetric linear endomorphism
`T : E →ₗ[𝕜] E`, and any chain of vectors `w : Fin (n + 1) → E` satisfying
`T (w k.castSucc) = w k.succ`, the matrix elements `⟪e i, T (e j)⟫` along the normalized
Gram–Schmidt family `e = gramSchmidtNormed 𝕜 w` form a real symmetric tridiagonal Jacobi matrix
with diagonal `r ↦ re ⟪e r, T (e r)⟫` and nonnegative subdiagonal
`k ↦ ‖gramSchmidt 𝕜 w k.castSucc‖⁻¹ * ‖gramSchmidt 𝕜 w k.succ‖`, without any linear-independence
assumption on `w`. When `w` is linearly independent, every subdiagonal entry is strictly positive.

Applying this Lanczos tridiagonalization to `T = (diagonal lam).toEuclideanLin` on
`EuclideanSpace ℝ (Fin (n + 1))` and the weighted Vandermonde vectors `w m k = √(q k) * lam k ^ m`
realizes every strictly decreasing sequence `lam : Fin (n + 1) → ℝ` and strictly positive
probability vector `q : Fin (n + 1) → ℝ` (`∑ k, q k = 1`) as the ordered eigenvalues and spectral
weights of a positive-subdiagonal Jacobi matrix.

## Main results

* `TauCeti.inner_gramSchmidtNormed_succ_apply_castSucc`: unconditional Lanczos subdiagonal formula
  `⟪e (k + 1), T (e k)⟫ = ‖gramSchmidt 𝕜 w k‖⁻¹ * ‖gramSchmidt 𝕜 w (k + 1)‖`.
* `TauCeti.inner_gramSchmidtNormed_apply_eq_jacobiMatrix_map`: unconditional Lanczos
  tridiagonalization of a symmetric operator along `gramSchmidtNormed 𝕜 w`.
* `TauCeti.exists_jacobiEigenvalues_eq_and_jacobiSpectralWeight_eq`: surjectivity of
  `(a, b) ↦ (jacobiEigenvalues a b, jacobiSpectralWeight a b)` from positive-subdiagonal Jacobi
  matrices onto strictly decreasing spectra and strictly positive probability weights.

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

/-! ### Lanczos tridiagonalization along normalized Gram–Schmidt chains -/

section Lanczos

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

private theorem map_mem_span_Iic_of_apply_castSucc {T : E →ₗ[𝕜] E} {w : Fin (n + 1) → E}
    (hw : ∀ k : Fin n, T (w k.castSucc) = w k.succ) (m : Fin n) {u : E}
    (hu : u ∈ Submodule.span 𝕜 (w '' Set.Iic m.castSucc)) :
    T u ∈ Submodule.span 𝕜 (w '' Set.Iic m.succ) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨j, hj, rfl⟩
      let j' : Fin n := ⟨j.val, lt_of_le_of_lt hj m.isLt⟩
      have hjcast : j'.castSucc = j := Fin.ext rfl
      rw [← hjcast, hw j']
      exact Submodule.subset_span ⟨j'.succ, Nat.succ_le_succ hj, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

private theorem map_gramSchmidt_sub_mem_span_Iio {T : E →ₗ[𝕜] E} {w : Fin (n + 1) → E}
    (hw : ∀ k : Fin n, T (w k.castSucc) = w k.succ) (k : Fin n) :
    T (gramSchmidt 𝕜 w k.castSucc - w k.castSucc) ∈
      Submodule.span 𝕜 (w '' Set.Iio k.succ) := by
  have hrem := gramSchmidt_sub_mem_span_Iio (𝕜 := 𝕜) w k.castSucc
  rcases k with ⟨kv, hkv⟩
  cases kv with
  | zero =>
      have hemp : Set.Iio (⟨0, hkv⟩ : Fin n).castSucc = ∅ := by ext x; simp
      rw [hemp, Set.image_empty, Submodule.span_empty, Submodule.mem_bot] at hrem
      rw [hrem, map_zero]
      exact Submodule.zero_mem _
  | succ kv' =>
      have hsub : Set.Iio (⟨kv' + 1, hkv⟩ : Fin n).castSucc =
          Set.Iic (⟨kv', by omega⟩ : Fin n).castSucc := by
        ext x
        simp only [Set.mem_Iio, Set.mem_Iic, Fin.lt_def, Fin.le_def, Fin.val_castSucc]
        omega
      have hsub2 : Set.Iic (⟨kv', by omega⟩ : Fin n).succ ⊆
          Set.Iio (⟨kv' + 1, hkv⟩ : Fin n).succ := fun x hx => by
        simp only [Set.mem_Iic, Set.mem_Iio, Fin.le_def, Fin.lt_def, Fin.val_succ] at hx ⊢
        omega
      rw [hsub] at hrem
      exact Submodule.span_mono (Set.image_mono hsub2)
        (map_mem_span_Iic_of_apply_castSucc hw ⟨kv', by omega⟩ hrem)

/-- **Lanczos subdiagonal formula**: if `T (w k.castSucc) = w k.succ` for every `k : Fin n`, then
pairing the `(k + 1)`-st normalized Gram–Schmidt vector of `w` against the image of the `k`-th
under `T` gives `‖gramSchmidt 𝕜 w k.castSucc‖⁻¹ * ‖gramSchmidt 𝕜 w k.succ‖` unconditionally
(vanishing automatically if either Gram–Schmidt residual vanishes). -/
theorem inner_gramSchmidtNormed_succ_apply_castSucc {T : E →ₗ[𝕜] E} {w : Fin (n + 1) → E}
    (hw : ∀ k : Fin n, T (w k.castSucc) = w k.succ) (k : Fin n) :
    inner 𝕜 (gramSchmidtNormed 𝕜 w k.succ) (T (gramSchmidtNormed 𝕜 w k.castSucc)) =
      ((‖gramSchmidt 𝕜 w k.castSucc‖⁻¹ * ‖gramSchmidt 𝕜 w k.succ‖ : ℝ) : 𝕜) := by
  have hdiff : T (gramSchmidt 𝕜 w k.castSucc) - w k.succ =
      T (gramSchmidt 𝕜 w k.castSucc - w k.castSucc) := by
    rw [map_sub, hw k]
  have h0 : inner 𝕜 (gramSchmidtNormed 𝕜 w k.succ)
      (T (gramSchmidt 𝕜 w k.castSucc) - w k.succ) = 0 := by
    rw [hdiff]
    exact inner_gramSchmidtNormed_eq_zero_of_mem_span_Iio w k.succ
      (map_gramSchmidt_sub_mem_span_Iio hw k)
  have hstep1 : inner 𝕜 (gramSchmidtNormed 𝕜 w k.succ) (T (gramSchmidt 𝕜 w k.castSucc)) =
      inner 𝕜 (gramSchmidtNormed 𝕜 w k.succ) (w k.succ) :=
    sub_eq_zero.mp (by rw [← inner_sub_right, h0])
  have he_cast : gramSchmidtNormed 𝕜 w k.castSucc =
      (‖gramSchmidt 𝕜 w k.castSucc‖ : 𝕜)⁻¹ • gramSchmidt 𝕜 w k.castSucc := by
    rw [gramSchmidtNormed]
  rw [he_cast, map_smul, inner_smul_right, hstep1, inner_gramSchmidtNormed_eq_norm,
    ← RCLike.ofReal_inv, ← RCLike.ofReal_mul]

private theorem inner_gramSchmidtNormed_apply_eq_zero_of_add_one_lt {T : E →ₗ[𝕜] E}
    {w : Fin (n + 1) → E} (hw : ∀ k : Fin n, T (w k.castSucc) = w k.succ)
    {i j : Fin (n + 1)} (h : j.val + 1 < i.val) :
    inner 𝕜 (gramSchmidtNormed 𝕜 w i) (T (gramSchmidtNormed 𝕜 w j)) = 0 := by
  let j' : Fin n := ⟨j.val, by omega⟩
  have hj_eq : j = j'.castSucc := Fin.ext rfl
  have hej : gramSchmidtNormed 𝕜 w j ∈ Submodule.span 𝕜 (w '' Set.Iic j'.castSucc) := by
    rw [← span_gramSchmidt_Iic 𝕜 w j'.castSucc, ← span_gramSchmidtNormed w, hj_eq]
    exact Submodule.subset_span ⟨j'.castSucc, Set.mem_Iic.mpr le_rfl, rfl⟩
  have hsub : Set.Iic j'.succ ⊆ Set.Iio i := fun x hx => by
    simp only [Set.mem_Iic, Set.mem_Iio, Fin.le_def, Fin.lt_def, Fin.val_succ, j'] at hx ⊢
    omega
  exact inner_gramSchmidtNormed_eq_zero_of_mem_span_Iio w i
    (Submodule.span_mono (Set.image_mono hsub) (map_mem_span_Iic_of_apply_castSucc hw j' hej))

/-- **Lanczos tridiagonalization**: for a symmetric operator `T` and any chain `w` satisfying
`T (w k.castSucc) = w k.succ`, the matrix elements of `T` along `gramSchmidtNormed 𝕜 w` form the
real symmetric Jacobi matrix with diagonal `r ↦ re ⟪e r, T (e r)⟫` and subdiagonal
`k ↦ ‖gramSchmidt 𝕜 w k.castSucc‖⁻¹ * ‖gramSchmidt 𝕜 w k.succ‖`. -/
theorem inner_gramSchmidtNormed_apply_eq_jacobiMatrix_map {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {w : Fin (n + 1) → E} (hw : ∀ k : Fin n, T (w k.castSucc) = w k.succ) (i j : Fin (n + 1)) :
    inner 𝕜 (gramSchmidtNormed 𝕜 w i) (T (gramSchmidtNormed 𝕜 w j)) =
      (jacobiMatrix
        (fun r => RCLike.re (inner 𝕜 (gramSchmidtNormed 𝕜 w r) (T (gramSchmidtNormed 𝕜 w r))))
        (fun k => ‖gramSchmidt 𝕜 w k.castSucc‖⁻¹ * ‖gramSchmidt 𝕜 w k.succ‖)).map
        (algebraMap ℝ 𝕜) i j := by
  let e := gramSchmidtNormed 𝕜 w
  have hT_conj : ∀ x y, inner 𝕜 x (T y) = starRingEnd 𝕜 (inner 𝕜 y (T x)) := fun x y => by
    rw [← hT x y, inner_conj_symm]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.map_apply, jacobiMatrix_apply_self, RCLike.algebraMap_eq_ofReal]
    exact (RCLike.conj_eq_iff_re.mp (hT_conj (e i) (e i)).symm).symm
  · by_cases h1 : j.val = i.val + 1
    · let k : Fin n := ⟨i.val, by omega⟩
      have hi' : i = k.castSucc := Fin.ext rfl
      have hj' : j = k.succ := Fin.ext (by simp [k, h1])
      rw [hi', hj', Matrix.map_apply, jacobiMatrix_apply_castSucc_succ,
        RCLike.algebraMap_eq_ofReal, hT_conj, inner_gramSchmidtNormed_succ_apply_castSucc hw k,
        RCLike.conj_ofReal]
    · by_cases h2 : i.val = j.val + 1
      · let k : Fin n := ⟨j.val, by omega⟩
        have hj' : j = k.castSucc := Fin.ext rfl
        have hi' : i = k.succ := Fin.ext (by simp [k, h2])
        rw [hi', hj', Matrix.map_apply, jacobiMatrix_apply_succ_castSucc,
          RCLike.algebraMap_eq_ofReal, inner_gramSchmidtNormed_succ_apply_castSucc hw k]
      · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
        · rw [Matrix.map_apply, jacobiMatrix_apply_of_add_one_lt_right _ _ (i := i) (j := j)
            (by omega), map_zero, hT_conj,
            inner_gramSchmidtNormed_apply_eq_zero_of_add_one_lt hw (by omega), map_zero]
        · rw [Matrix.map_apply, jacobiMatrix_apply_of_add_one_lt_left _ _ (i := i) (j := j)
            (by omega), map_zero]
          exact inner_gramSchmidtNormed_apply_eq_zero_of_add_one_lt hw (by omega)

end Lanczos

/-! ### Spectral reconstruction from eigenvalues and weights -/

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

private theorem jacobiMatrix_spectralVandermondeVec_eq_conj_diagonal {lam q : Fin (n + 1) → ℝ}
    {Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hQ : ∀ k i, Q k i = gramSchmidtNormed ℝ (spectralVandermondeVec lam q) i k) :
    jacobiMatrix
        (fun r => ⟪gramSchmidtNormed ℝ (spectralVandermondeVec lam q) r,
          (Matrix.diagonal lam).toEuclideanLin
            (gramSchmidtNormed ℝ (spectralVandermondeVec lam q) r)⟫)
        (fun k => ‖gramSchmidt ℝ (spectralVandermondeVec lam q) k.castSucc‖⁻¹ *
          ‖gramSchmidt ℝ (spectralVandermondeVec lam q) k.succ‖) =
      Qᵀ * Matrix.diagonal lam * Q := by
  ext i j
  have hT : (Matrix.diagonal lam).toEuclideanLin.IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_diagonal lam)
  have htrid := inner_gramSchmidtNormed_apply_eq_jacobiMatrix_map hT
    (diagMul_spectralVandermondeVec lam q) i j
  simp only [Matrix.map_apply, RCLike.re_to_real, Algebra.algebraMap_self,
    RingHom.id_apply] at htrid
  rw [← htrid, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, transpose_apply, hQ, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Matrix.toLpLin_apply, Matrix.mulVec_diagonal, star_trivial]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- **Spectral reconstruction for Jacobi matrices**: every strictly decreasing tuple of eigenvalues
`lam` and positive spectral weight vector `q` summing to `1` are realized by a Jacobi matrix with
strictly positive subdiagonal entries. -/
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
  have hJeq : jacobiMatrix a b = Qᵀ * Matrix.diagonal lam * Q :=
    jacobiMatrix_spectralVandermondeVec_eq_conj_diagonal hQ_apply
  have hlam_eq : jacobiEigenvalues a b = lam := by
    refine jacobiEigenvalues_eq_of_charpoly_eq hlam.antitone ?_
    rw [hJeq, Matrix.charpoly_mul_comm, ← mul_assoc, hQQT, one_mul, Matrix.charpoly_diagonal]
  refine ⟨a, b, hb_pos, hlam_eq, funext fun k => ?_⟩
  have hvk_norm : ‖(WithLp.toLp 2 (Q k) : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
    Matrix.norm_toLp_apply_of_mul_conjTranspose_eq_one hQJH k
  have hvk_eig : jacobiMatrix a b *ᵥ ⇑(WithLp.toLp 2 (Q k) : EuclideanSpace ℝ (Fin (n + 1))) =
      jacobiEigenvalues a b k • ⇑(WithLp.toLp 2 (Q k) : EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa [hJeq, hlam_eq] using
      Matrix.transpose_mul_diagonal_mul_mulVec_apply_of_mul_transpose_eq_one hQQT lam k
  rw [jacobiSpectralWeight_eq_sq_eigenvector
    (fun _ hj => by rw [hlam_eq]; exact hlam.injective.ne hj) hvk_norm hvk_eig, PiLp.toLp_apply,
    hQ_apply]
  simp only [e, w, gramSchmidtNormed_spectralVandermondeVec_zero hq hsum,
    spectralVandermondeVec, Fin.val_zero, pow_zero, mul_one, Real.sq_sqrt (hq k).le]

end Reconstruction

end TauCeti
