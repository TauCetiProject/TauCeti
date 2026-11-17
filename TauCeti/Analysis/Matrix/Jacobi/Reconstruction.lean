/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Jacobi.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Spectral reconstruction for real Jacobi matrices

Every strictly decreasing sequence of real numbers `lam : Fin (n + 1) → ℝ` and every strictly
positive probability vector `q : Fin (n + 1) → ℝ` (`∑ k, q k = 1`) arise as the ordered
eigenvalues and spectral weights of a symmetric tridiagonal Jacobi matrix with strictly positive
subdiagonal entries.

The construction applies Gram–Schmidt orthonormalization to the weighted Vandermonde vectors
`w m k = √(q k) * lam k ^ m` in `EuclideanSpace ℝ (Fin (n + 1))`. In the resulting orthonormal
basis `e`, multiplication by `diagonal lam` is tridiagonal with strictly positive subdiagonal
entries `b k = ‖gramSchmidt ℝ w (k + 1)‖ / ‖gramSchmidt ℝ w k‖`, and the first basis vector is
`e 0 = w 0 = (√(q k))_k`, which recovers the spectral weights.

## Main results

* `TauCeti.exists_jacobiMatrix_of_strictAnti_weights`: surjectivity of the spectral-data map
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

variable {n : ℕ}

/-- The weighted Vandermonde vectors `w m k = √(q k) * lam k ^ m`. -/
private def spectralVandermondeVec (lam q : Fin (n + 1) → ℝ) (m : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 fun k => Real.sqrt (q k) * lam k ^ m.val

private theorem linearIndependent_spectralVandermondeVec {lam q : Fin (n + 1) → ℝ}
    (hlam : StrictAnti lam) (hq : ∀ k, 0 < q k) :
    LinearIndependent ℝ (spectralVandermondeVec lam q) := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.diagonal (fun k => Real.sqrt (q k)) * Matrix.vandermonde lam
  have hMdet : M.det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => (Real.sqrt_pos.mpr (hq k)).ne') ?_
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact sub_ne_zero.mpr (hlam (Finset.mem_Ioi.mp hj)).ne
  refine Fintype.linearIndependent_iff.mpr fun c hc => ?_
  have hMc : M *ᵥ c = 0 := by
    ext k
    have hk := congrArg (fun x : EuclideanSpace ℝ (Fin (n + 1)) => x k) hc
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      WithLp.ofLp_zero, Pi.zero_apply, spectralVandermondeVec] at hk
    simpa only [M, Matrix.mulVec, dotProduct, Matrix.diagonal_mul, Matrix.vandermonde_apply,
      Pi.zero_apply, mul_assoc, mul_comm, mul_left_comm] using hk
  have hc0 : c = 0 := by
    calc c = (M⁻¹ * M) *ᵥ c := by
          rw [Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hMdet), one_mulVec]
      _ = 0 := by rw [← mulVec_mulVec, hMc, mulVec_zero]
  exact fun i => congrFun hc0 i

private theorem diagMul_spectralVandermondeVec (lam q : Fin (n + 1) → ℝ) (k : Fin n) :
    (Matrix.diagonal lam).toEuclideanLin (spectralVandermondeVec lam q k.castSucc) =
      spectralVandermondeVec lam q k.succ := by
  ext r
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_diagonal, spectralVandermondeVec,
    WithLp.ofLp_toLp, Fin.val_castSucc, Fin.val_succ, pow_succ]
  ring

private theorem diagMul_mem_span_Iic (lam q : Fin (n + 1) → ℝ) (m : Fin n)
    {u : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : u ∈ Submodule.span ℝ (spectralVandermondeVec lam q '' Set.Iic m.castSucc)) :
    (Matrix.diagonal lam).toEuclideanLin u ∈
      Submodule.span ℝ (spectralVandermondeVec lam q '' Set.Iic m.succ) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨j, hj, rfl⟩
      let j' : Fin n := ⟨j.val, lt_of_le_of_lt hj m.isLt⟩
      have hjcast : j'.castSucc = j := Fin.ext rfl
      rw [← hjcast, diagMul_spectralVandermondeVec]
      exact Submodule.subset_span ⟨j'.succ, Nat.succ_le_succ hj, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

private theorem gramSchmidtNormed_ortho_span_Iio {lam q : Fin (n + 1) → ℝ}
    (hw_li : LinearIndependent ℝ (spectralVandermondeVec lam q)) (i : Fin (n + 1))
    {u : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : u ∈ Submodule.span ℝ (spectralVandermondeVec lam q '' Set.Iio i)) :
    ⟪gramSchmidtNormed ℝ (spectralVandermondeVec lam q) i, u⟫ = 0 := by
  have he_ortho := gramSchmidtNormed_orthonormal hw_li
  rw [← span_gramSchmidt_Iio ℝ (spectralVandermondeVec lam q) i,
    ← span_gramSchmidtNormed (spectralVandermondeVec lam q)] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨j, hj, rfl⟩
      exact he_ortho.2 (ne_of_gt hj)
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]

private theorem gramSchmidt_sub_mem_span_Iio {lam q : Fin (n + 1) → ℝ} (i : Fin (n + 1)) :
    gramSchmidt ℝ (spectralVandermondeVec lam q) i - spectralVandermondeVec lam q i ∈
      Submodule.span ℝ (spectralVandermondeVec lam q '' Set.Iio i) := by
  let w := spectralVandermondeVec lam q
  rw [← span_gramSchmidt_Iio ℝ w i, gramSchmidt_def ℝ w i, sub_sub_cancel_left]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
  rw [Submodule.starProjection_singleton]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, Finset.mem_Iio.mp hj, rfl⟩)

private theorem subdiagonal_pos_gramSchmidt {lam q : Fin (n + 1) → ℝ}
    (hw_li : LinearIndependent ℝ (spectralVandermondeVec lam q)) (k : Fin n) :
    0 < ⟪gramSchmidtNormed ℝ (spectralVandermondeVec lam q) k.succ,
          (Matrix.diagonal lam).toEuclideanLin
            (gramSchmidtNormed ℝ (spectralVandermondeVec lam q) k.castSucc)⟫ := by
  let w := spectralVandermondeVec lam q
  let e := gramSchmidtNormed ℝ w
  let T := (Matrix.diagonal lam).toEuclideanLin
  have hgne : gramSchmidt ℝ w k.castSucc ≠ 0 := gramSchmidt_ne_zero k.castSucc hw_li
  have hgne' : gramSchmidt ℝ w k.succ ≠ 0 := gramSchmidt_ne_zero k.succ hw_li
  have hrem := gramSchmidt_sub_mem_span_Iio (lam := lam) (q := q) k.castSucc
  have hTrem : T (gramSchmidt ℝ w k.castSucc - w k.castSucc) ∈
      Submodule.span ℝ (w '' Set.Iio k.succ) := by
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
          (diagMul_mem_span_Iic lam q ⟨kv', by omega⟩ hrem)
  have hstep1 : ⟪e k.succ, T (gramSchmidt ℝ w k.castSucc)⟫ = ⟪e k.succ, w k.succ⟫ := by
    have hdiff : T (gramSchmidt ℝ w k.castSucc) - w k.succ =
        T (gramSchmidt ℝ w k.castSucc - w k.castSucc) := by
      rw [map_sub, diagMul_spectralVandermondeVec]
    have h0 : ⟪e k.succ, T (gramSchmidt ℝ w k.castSucc) - w k.succ⟫ = 0 := by
      rw [hdiff]; exact gramSchmidtNormed_ortho_span_Iio hw_li k.succ hTrem
    linarith [inner_sub_right (𝕜 := ℝ) (e k.succ) (T (gramSchmidt ℝ w k.castSucc)) (w k.succ)]
  have hstep2 : ⟪e k.succ, w k.succ⟫ = ‖gramSchmidt ℝ w k.succ‖ := by
    have hwsucc : w k.succ - gramSchmidt ℝ w k.succ ∈ Submodule.span ℝ (w '' Set.Iio k.succ) := by
      simpa using Submodule.neg_mem _ (gramSchmidt_sub_mem_span_Iio (lam := lam) (q := q) k.succ)
    have h0 := gramSchmidtNormed_ortho_span_Iio hw_li k.succ hwsucc
    have hself : ⟪e k.succ, gramSchmidt ℝ w k.succ⟫ = ‖gramSchmidt ℝ w k.succ‖ := by
      simp only [e, gramSchmidtNormed, inner_smul_left, RCLike.conj_to_real,
        RCLike.ofReal_real_eq_id, id_eq, real_inner_self_eq_norm_sq, sq]
      field_simp [norm_ne_zero_iff.mpr hgne']
    linarith [inner_sub_right (𝕜 := ℝ) (e k.succ) (w k.succ) (gramSchmidt ℝ w k.succ)]
  have hval : ⟪e k.succ, T (e k.castSucc)⟫ =
      ‖gramSchmidt ℝ w k.castSucc‖⁻¹ * ‖gramSchmidt ℝ w k.succ‖ := by
    change ⟪e k.succ, T (‖gramSchmidt ℝ w k.castSucc‖⁻¹ • gramSchmidt ℝ w k.castSucc)⟫ = _
    rw [map_smul, inner_smul_right, hstep1, hstep2]
  rw [hval]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hgne)) (norm_pos_iff.mpr hgne')

private theorem gramSchmidt_tridiagonal {lam q : Fin (n + 1) → ℝ}
    (hw_li : LinearIndependent ℝ (spectralVandermondeVec lam q)) (i j : Fin (n + 1)) :
    ⟪gramSchmidtNormed ℝ (spectralVandermondeVec lam q) i,
      (Matrix.diagonal lam).toEuclideanLin
        (gramSchmidtNormed ℝ (spectralVandermondeVec lam q) j)⟫ =
      jacobiMatrix
        (fun r => ⟪gramSchmidtNormed ℝ (spectralVandermondeVec lam q) r,
          (Matrix.diagonal lam).toEuclideanLin
            (gramSchmidtNormed ℝ (spectralVandermondeVec lam q) r)⟫)
        (fun k => ⟪gramSchmidtNormed ℝ (spectralVandermondeVec lam q) k.succ,
          (Matrix.diagonal lam).toEuclideanLin
            (gramSchmidtNormed ℝ (spectralVandermondeVec lam q) k.castSucc)⟫)
        i j := by
  let w := spectralVandermondeVec lam q
  let e := gramSchmidtNormed ℝ w
  let T := (Matrix.diagonal lam).toEuclideanLin
  have hT_symm : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫ :=
    isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_diagonal lam)
  by_cases hij : i = j
  · subst hij; simp
  · by_cases h1 : j.val = i.val + 1
    · let k : Fin n := ⟨i.val, by omega⟩
      have hi' : i = k.castSucc := Fin.ext rfl
      have hj' : j = k.succ := Fin.ext (by simp [k, h1])
      rw [hi', hj', jacobiMatrix_apply_castSucc_succ]
      exact (hT_symm (e k.castSucc) (e k.succ)).symm.trans (real_inner_comm _ _)
    · by_cases h2 : i.val = j.val + 1
      · let k : Fin n := ⟨j.val, by omega⟩
        have hj' : j = k.castSucc := Fin.ext rfl
        have hi' : i = k.succ := Fin.ext (by simp [k, h2])
        rw [hi', hj', jacobiMatrix_apply_succ_castSucc]
      · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
        · rw [jacobiMatrix_apply_of_add_one_lt_right _ _ (by omega)]
          rw [show ⟪e i, T (e j)⟫ = ⟪e j, T (e i)⟫ from
            (hT_symm (e i) (e j)).symm.trans (real_inner_comm _ _)]
          let i' : Fin n := ⟨i.val, by omega⟩
          have hi_eq : i = i'.castSucc := Fin.ext rfl
          have hei : e i ∈ Submodule.span ℝ (w '' Set.Iic i'.castSucc) := by
            rw [← span_gramSchmidt_Iic ℝ w i'.castSucc, ← span_gramSchmidtNormed w, hi_eq]
            exact Submodule.subset_span ⟨i'.castSucc, Set.mem_Iic.mpr le_rfl, rfl⟩
          have hsub : Set.Iic i'.succ ⊆ Set.Iio j := fun x hx => by
            simp only [Set.mem_Iic, Set.mem_Iio, Fin.le_def, Fin.lt_def, Fin.val_succ, i'] at hx ⊢
            omega
          exact gramSchmidtNormed_ortho_span_Iio hw_li j
            (Submodule.span_mono (Set.image_mono hsub) (diagMul_mem_span_Iic lam q i' hei))
        · rw [jacobiMatrix_apply_of_add_one_lt_left _ _ (by omega)]
          let j' : Fin n := ⟨j.val, by omega⟩
          have hj_eq : j = j'.castSucc := Fin.ext rfl
          have hej : e j ∈ Submodule.span ℝ (w '' Set.Iic j'.castSucc) := by
            rw [← span_gramSchmidt_Iic ℝ w j'.castSucc, ← span_gramSchmidtNormed w, hj_eq]
            exact Submodule.subset_span ⟨j'.castSucc, Set.mem_Iic.mpr le_rfl, rfl⟩
          have hsub : Set.Iic j'.succ ⊆ Set.Iio i := fun x hx => by
            simp only [Set.mem_Iic, Set.mem_Iio, Fin.le_def, Fin.lt_def, Fin.val_succ, j'] at hx ⊢
            omega
          exact gramSchmidtNormed_ortho_span_Iio hw_li i
            (Submodule.span_mono (Set.image_mono hsub) (diagMul_mem_span_Iic lam q j' hej))

private theorem gramSchmidtNormed_zero_eq_self {lam q : Fin (n + 1) → ℝ}
    (hq : ∀ k, 0 < q k) (hsum : ∑ k, q k = 1) :
    gramSchmidtNormed ℝ (spectralVandermondeVec lam q) 0 = spectralVandermondeVec lam q 0 := by
  let w := spectralVandermondeVec lam q
  have hg0 : gramSchmidt ℝ w 0 = w 0 := by
    rw [gramSchmidt_def]
    have hemp : Finset.Iio (0 : Fin (n + 1)) = ∅ := by ext x; simp
    simp [hemp]
  have hnorm0 : ‖w 0‖ = 1 := by
    have hsq : ‖w 0‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [w, spectralVandermondeVec, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs,
        Fin.val_zero, pow_zero, mul_one]
      simp_rw [Real.sq_sqrt (hq _).le]
      exact hsum
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hsq)
  rw [gramSchmidtNormed]
  change ‖gramSchmidt ℝ w 0‖⁻¹ • gramSchmidt ℝ w 0 = w 0
  rw [hg0, hnorm0, inv_one, one_smul]

/-- **Spectral reconstruction for Jacobi matrices**: every strictly decreasing tuple of eigenvalues
`lam` and positive spectral weight vector `q` summing to `1` are realized by a Jacobi matrix with
strictly positive subdiagonal entries. -/
theorem exists_jacobiMatrix_of_strictAnti_weights {lam q : Fin (n + 1) → ℝ}
    (hlam : StrictAnti lam) (hq : ∀ k, 0 < q k) (hsum : ∑ k, q k = 1) :
    ∃ (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ),
      (∀ k, 0 < b k) ∧
      jacobiEigenvalues a b = lam ∧
      jacobiSpectralWeight a b = q := by
  let w := spectralVandermondeVec lam q
  have hw_li : LinearIndependent ℝ w := linearIndependent_spectralVandermondeVec hlam hq
  let e := gramSchmidtNormed ℝ w
  let T := (Matrix.diagonal lam).toEuclideanLin
  let a : Fin (n + 1) → ℝ := fun i => ⟪e i, T (e i)⟫
  let b : Fin n → ℝ := fun k => ⟪e k.succ, T (e k.castSucc)⟫
  have hb_pos : ∀ k, 0 < b k := subdiagonal_pos_gramSchmidt hw_li
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun k i => e i k
  have hQTQ : Qᵀ * Q = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hinner : ∑ k, e i k * e j k = ⟪e i, e j⟫ := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
    simpa [Q, hinner] using orthonormal_iff_ite.mp (gramSchmidtNormed_orthonormal hw_li) i j
  have hQQT : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQTQ
  have hJeq : jacobiMatrix a b = Qᵀ * Matrix.diagonal lam * Q := by
    ext i j
    rw [← gramSchmidt_tridiagonal hw_li i j, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Q, transpose_apply, of_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.toLpLin_apply,
      Matrix.mulVec_diagonal, star_trivial]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hlam_eq : jacobiEigenvalues a b = lam := by
    refine jacobiEigenvalues_eq_of_charpoly_eq hlam.antitone ?_
    rw [hJeq, Matrix.charpoly_mul_comm, ← mul_assoc, hQQT, one_mul, Matrix.charpoly_diagonal]
  refine ⟨a, b, hb_pos, hlam_eq, funext fun k => ?_⟩
  let vk : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 fun i => e i k
  have hvk_norm : ‖vk‖ = 1 := by
    have hsq : ‖vk‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      have hdiag := congrFun (congrFun hQQT k) k
      simpa [vk, Q, Matrix.mul_apply, sq] using hdiag
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hsq)
  have hvk_eig : jacobiMatrix a b *ᵥ ⇑vk = jacobiEigenvalues a b k • ⇑vk := by
    rw [hlam_eq, hJeq]
    have hQvk : Q *ᵥ ⇑vk = Pi.single k 1 := by
      ext r
      have hr := congrFun (congrFun hQQT r) k
      simpa [Q, vk, mulVec, dotProduct, Matrix.mul_apply, Matrix.one_apply, Pi.single_apply,
        eq_comm] using hr
    rw [← mulVec_mulVec, hQvk, ← mulVec_mulVec, Matrix.diagonal_mulVec_single, mul_one]
    ext i
    simp [Q, vk, mulVec, dotProduct, Pi.single_apply, mul_comm]
  rw [jacobiSpectralWeight_eq_sq_eigenvector (fun j => (hb_pos j).ne') k hvk_norm hvk_eig]
  have hv0 : vk 0 = Real.sqrt (q k) := by
    change (gramSchmidtNormed ℝ (spectralVandermondeVec lam q) 0).ofLp k = _
    rw [gramSchmidtNormed_zero_eq_self hq hsum]
    simp [spectralVandermondeVec]
  rw [hv0, Real.sq_sqrt (hq k).le]

end TauCeti
