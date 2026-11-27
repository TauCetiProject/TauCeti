/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.SesquilinearForm
public import TauCeti.Analysis.InnerProductSpace.Spectrum
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary

/-!
# Eigenvalues of a Hermitian form relative to an inner product

Let `E` be a finite-dimensional inner product space over `𝕜 ∈ {ℝ, ℂ}` of dimension `n`, and let
`a : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜` be a Hermitian form (`LinearMap.IsSymm`). Its operator
`A_a = (LinearMap.toSesqForm 𝕜 E E).symm a`, characterized by `a u v = ⟪u, A_a v⟫`, is symmetric,
and the *relative eigenvalue vector* `λ[a] ∈ ℝⁿ` of `a` is the decreasingly sorted eigenvalue
vector of `A_a`. Equivalently, `λ[a]` is the antitone list of diagonal entries of `a` in an
orthonormal basis that diagonalizes it. In a basis with Gram matrix `g` and coefficient matrix
`(a_ij)` it is the spectrum of `g⁻¹a`.

## Main definitions

* `LinearMap.IsSymm.relEigenvalues`: the relative eigenvalue vector `λ[a]`.
* `LinearMap.IsSymm.relEigenvectorBasis`: an orthonormal basis diagonalizing `a`, ordered as
  `λ[a]`.

## Main results

* `LinearMap.IsSymm.apply_relEigenvectorBasis` and
  `LinearMap.IsSymm.relEigenvalues_eq_of_orthonormalBasis`: `λ[a]` is the unique antitone list of
  diagonal entries of `a` in an orthonormal basis diagonalizing it.
* `LinearMap.IsSymm.relEigenvalues_innerₛₗ`, `LinearMap.IsSymm.relEigenvalues_add_smul_innerₛₗ`,
  `LinearMap.IsSymm.relEigenvalues_smul`: `λ[⟪·,·⟫] = e`, `λ[a + t⟪·,·⟫] = λ[a] + t·e` and
  `λ[s·a] = s·λ[a]` for `s ≥ 0`.
* `LinearMap.IsSymm.sum_relEigenvalues`, `LinearMap.IsSymm.prod_relEigenvalues` and
  `LinearMap.IsSymm.det_id_add_smul`: `Σ λ_i[a] = tr A_a`, `∏ λ_i[a] = det A_a` and
  `det(Id + t·A_a) = Σ_k σ_k(λ[a])·t^k`.
* `LinearMap.IsSymm.sum_relEigenvalues_eq_sum_re_apply`: `Σ λ_i[a] = Σ_j Re a(b_j, b_j)` in any
  orthonormal basis `b`.
* `LinearMap.IsSymm.relEigenvalues_compl₂`: invariance under linear isometries,
  `λ[a(U·, U·)] = λ[a]`.
* `LinearMap.IsSymm.det_toMatrix₂_sub_smul_gram`: in a basis with Gram matrix `g`,
  `det([a] − μ·g) = det g · ∏_i (λ_i[a] − μ)`, so `λ[a]` lists the roots of
  `det([a] − μ·g) = 0`. It rests on `g·[A_a] = [a]`
  (`LinearMap.gram_mul_toMatrix_toSesqForm_symm`).
* `LinearMap.IsSymm.relEigenvalues_mono` and
  `LinearMap.IsSymm.abs_relEigenvalues_sub_le_opNorm`: monotonicity in the order of Hermitian
  forms and the Lipschitz bound `|λ_i[a] − λ_i[b]| ≤ ‖A_a − A_b‖`, from the Courant–Fischer
  theory.

## References

* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), Section 2.
* B. Guo, D. H. Phong and F. Tong, *On L∞ estimates for complex Monge–Ampère equations*,
  Ann. of Math. 198 (2023), Section 2.
-/

public section

open Module (finrank)
open scoped InnerProductSpace
open LinearMap (toSesqForm)

namespace LinearMap.IsSymm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {a b : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜}

/-- The **relative eigenvalue vector** `λ[a] ∈ ℝⁿ` of a Hermitian form `a` on a finite-dimensional
inner product space of dimension `n`: the decreasingly sorted eigenvalues of the symmetric
operator `A_a` with `a u v = ⟪u, A_a v⟫`. -/
noncomputable def relEigenvalues (ha : a.IsSymm) (hn : finrank 𝕜 E = n) : Fin n → ℝ :=
  ha.isSymmetric_toSesqForm_symm.eigenvalues hn

/-- Unfolding lemma for `relEigenvalues`. -/
theorem relEigenvalues_def (ha : a.IsSymm) (hn : finrank 𝕜 E = n) :
    ha.relEigenvalues hn = ha.isSymmetric_toSesqForm_symm.eigenvalues hn :=
  (rfl)

/-- An orthonormal basis of eigenvectors of the operator `A_a` of a Hermitian form `a`, ordered as
the relative eigenvalue vector `λ[a]`. It diagonalizes `a` (`apply_relEigenvectorBasis`). -/
noncomputable def relEigenvectorBasis (ha : a.IsSymm) (hn : finrank 𝕜 E = n) :
    OrthonormalBasis (Fin n) 𝕜 E :=
  ha.isSymmetric_toSesqForm_symm.eigenvectorBasis hn

/-- Unfolding lemma for `relEigenvectorBasis`. -/
theorem relEigenvectorBasis_def (ha : a.IsSymm) (hn : finrank 𝕜 E = n) :
    ha.relEigenvectorBasis hn = ha.isSymmetric_toSesqForm_symm.eigenvectorBasis hn :=
  (rfl)

/-- The relative eigenvalues are sorted decreasingly. -/
theorem relEigenvalues_antitone (ha : a.IsSymm) (hn : finrank 𝕜 E = n) :
    Antitone (ha.relEigenvalues hn) :=
  ha.isSymmetric_toSesqForm_symm.eigenvalues_antitone hn

/-- The basis `relEigenvectorBasis` diagonalizes the Hermitian form, with diagonal `λ[a]`. -/
theorem apply_relEigenvectorBasis (ha : a.IsSymm) (hn : finrank 𝕜 E = n) (i j : Fin n) :
    a (ha.relEigenvectorBasis hn i) (ha.relEigenvectorBasis hn j) =
      if i = j then (ha.relEigenvalues hn i : 𝕜) else 0 := by
  rw [← LinearMap.inner_toSesqForm_symm_apply, relEigenvectorBasis_def,
    ha.isSymmetric_toSesqForm_symm.apply_eigenvectorBasis, inner_smul_right,
    (ha.isSymmetric_toSesqForm_symm.eigenvectorBasis hn).inner_eq_ite, relEigenvalues_def]
  split_ifs with h
  · subst h; simp
  · simp

/-- **Uniqueness of the relative eigenvalue vector.** If an orthonormal basis `w` diagonalizes the
Hermitian form `a` with an antitone list of diagonal entries `μ`, then `μ = λ[a]`. -/
theorem relEigenvalues_eq_of_orthonormalBasis (ha : a.IsSymm) (hn : finrank 𝕜 E = n)
    (w : OrthonormalBasis (Fin n) 𝕜 E) {μ : Fin n → ℝ} (hμ : Antitone μ)
    (hw : ∀ i j, a (w i) (w j) = if i = j then (μ i : 𝕜) else 0) :
    ha.relEigenvalues hn = μ := by
  refine ha.isSymmetric_toSesqForm_symm.eigenvalues_eq_of_eigenbasis hn w.toBasis hμ fun j ↦ ?_
  rw [OrthonormalBasis.coe_toBasis]
  rw [← w.sum_repr' ((toSesqForm 𝕜 E E).symm a (w j))]
  simp_rw [LinearMap.inner_toSesqForm_symm_apply, hw, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The inner product has relative eigenvalue vector `e = (1, …, 1)`. -/
theorem relEigenvalues_innerₛₗ (h : (innerₛₗ 𝕜 : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜).IsSymm)
    (hn : finrank 𝕜 E = n) : h.relEigenvalues hn = 1 := by
  refine h.relEigenvalues_eq_of_orthonormalBasis hn
    ((stdOrthonormalBasis 𝕜 E).reindex (finCongr hn)) antitone_const fun i j ↦ ?_
  simp [OrthonormalBasis.inner_eq_ite]

/-- Adding a real multiple of the inner product shifts the relative eigenvalues:
`λ[a + t⟪·,·⟫] = λ[a] + t·e`. -/
theorem relEigenvalues_add_smul_innerₛₗ (ha : a.IsSymm) (t : ℝ)
    (h : (a + (t : 𝕜) • innerₛₗ 𝕜).IsSymm) (hn : finrank 𝕜 E = n) :
    h.relEigenvalues hn = ha.relEigenvalues hn + fun _ ↦ t := by
  refine h.relEigenvalues_eq_of_orthonormalBasis hn (ha.relEigenvectorBasis hn)
    ((ha.relEigenvalues_antitone hn).add antitone_const) fun i j ↦ ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, innerₛₗ_apply_apply,
    ha.apply_relEigenvectorBasis, (ha.relEigenvectorBasis hn).inner_eq_ite, Pi.add_apply]
  split_ifs <;> simp

/-- Scaling by `s ≥ 0` scales the relative eigenvalues: `λ[s·a] = s·λ[a]`. -/
theorem relEigenvalues_smul (ha : a.IsSymm) {s : ℝ} (hs : 0 ≤ s) (h : ((s : 𝕜) • a).IsSymm)
    (hn : finrank 𝕜 E = n) : h.relEigenvalues hn = s • ha.relEigenvalues hn := by
  refine h.relEigenvalues_eq_of_orthonormalBasis hn (ha.relEigenvectorBasis hn)
    ((ha.relEigenvalues_antitone hn).const_smul hs) fun i j ↦ ?_
  simp only [LinearMap.smul_apply, ha.apply_relEigenvectorBasis, Pi.smul_apply]
  split_ifs <;> simp

/-- The relative eigenvalues sum to the trace of the operator of the form. -/
theorem sum_relEigenvalues (ha : a.IsSymm) (hn : finrank 𝕜 E = n) :
    ∑ i, (ha.relEigenvalues hn i : 𝕜) = LinearMap.trace 𝕜 E ((toSesqForm 𝕜 E E).symm a) :=
  by simp [relEigenvalues_def,
    LinearMap.IsSymmetric.trace_eq_sum_eigenvalues hn ha.isSymmetric_toSesqForm_symm]

/-- The relative eigenvalues of a Hermitian form sum to the sum of the real parts of its diagonal
entries in any orthonormal basis. -/
theorem sum_relEigenvalues_eq_sum_re_apply {ι : Type*} [Fintype ι] (ha : a.IsSymm)
    (hn : finrank 𝕜 E = n) (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, ha.relEigenvalues hn i = ∑ j, RCLike.re (a (b j) (b j)) := by
  have hsum := congrArg RCLike.re (ha.sum_relEigenvalues hn)
  rw [LinearMap.trace_eq_sum_inner _ b, map_sum, map_sum] at hsum
  simpa only [RCLike.ofReal_re, LinearMap.inner_toSesqForm_symm_apply] using hsum

/-- The relative eigenvalues multiply to the determinant of the operator of the form. -/
theorem prod_relEigenvalues (ha : a.IsSymm) (hn : finrank 𝕜 E = n) :
    ∏ i, (ha.relEigenvalues hn i : 𝕜) = LinearMap.det ((toSesqForm 𝕜 E E).symm a) :=
  (ha.isSymmetric_toSesqForm_symm.det_eq_prod_eigenvalues hn).symm

/-- `det(Id + t·A_a) = Σ_k σ_k(λ[a])·t^k`, where `σ_k` is the `k`-th elementary symmetric
polynomial. -/
theorem det_id_add_smul (ha : a.IsSymm) (hn : finrank 𝕜 E = n) (t : 𝕜) :
    LinearMap.det (LinearMap.id + t • (toSesqForm 𝕜 E E).symm a) =
      ∑ k ∈ Finset.range (n + 1),
        (MvPolynomial.eval (ha.relEigenvalues hn) (MvPolynomial.esymm (Fin n) ℝ k) : 𝕜) *
          t ^ k := by
  rw [← one_smul 𝕜 LinearMap.id, ha.isSymmetric_toSesqForm_symm.det_smul_id_add_smul hn]
  have h := TauCeti.prod_one_add_mul_eq_sum_esymm (fun i ↦ (ha.relEigenvalues hn i : 𝕜)) t
  rw [Fintype.card_fin] at h
  refine h.trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  simp [MvPolynomial.esymm, map_sum, map_prod]

/-- **Invariance under linear isometries.** For a linear isometry equivalence `U`, the form
`a(U·, U·)` has the same relative eigenvalues as `a`; in particular `λ[a(U·, U·)] = λ[a]` for every
unitary `U`. -/
theorem relEigenvalues_compl₂ {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    [FiniteDimensional 𝕜 E'] (ha : a.IsSymm) (U : E' ≃ₗᵢ[𝕜] E)
    (h : ((a.comp U.toLinearMap).compl₂ U.toLinearMap).IsSymm) (hn : finrank 𝕜 E = n)
    (hn' : finrank 𝕜 E' = n) : h.relEigenvalues hn' = ha.relEigenvalues hn := by
  refine h.relEigenvalues_eq_of_orthonormalBasis hn' ((ha.relEigenvectorBasis hn).map U.symm)
    (ha.relEigenvalues_antitone hn) fun i j ↦ ?_
  simp [ha.apply_relEigenvectorBasis]

/-- **The relative eigenvalues in a basis.** In a basis `b` with Gram matrix `g` and coefficient
matrix `[a]`, `det([a] − μ·g) = det g · ∏_i (λ_i[a] − μ)`. Since `det g ≠ 0`, the relative
eigenvalues are the roots of `det([a] − μ·g) = 0`, the spectrum of `g⁻¹[a]`. -/
theorem det_toMatrix₂_sub_smul_gram (ha : a.IsSymm) (hn : finrank 𝕜 E = n) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι 𝕜 E) (μ : 𝕜) :
    (LinearMap.toMatrix₂ b b a - μ • Matrix.gram 𝕜 b).det =
      (Matrix.gram 𝕜 b).det * ∏ i, ((ha.relEigenvalues hn i : 𝕜) - μ) := by
  have hg : μ • Matrix.gram 𝕜 b = Matrix.gram 𝕜 b * LinearMap.toMatrix b b (μ • LinearMap.id) := by
    rw [map_smul, LinearMap.toMatrix_id, Matrix.mul_smul, Matrix.mul_one]
  have hA : (toSesqForm 𝕜 E E).symm a - μ • LinearMap.id =
      (-μ) • LinearMap.id + (1 : 𝕜) • (toSesqForm 𝕜 E E).symm a := by
    rw [one_smul, neg_smul]; abel
  rw [← LinearMap.gram_mul_toMatrix_toSesqForm_symm, hg, ← Matrix.mul_sub, Matrix.det_mul,
    ← map_sub, LinearMap.det_toMatrix, hA,
    ha.isSymmetric_toSesqForm_symm.det_smul_id_add_smul hn]
  simp [relEigenvalues_def, neg_add_eq_sub]

/-- **Monotonicity.** If `b − a` is positive semidefinite, then `λ_i[a] ≤ λ_i[b]` for every `i`. -/
theorem relEigenvalues_mono (ha : a.IsSymm) (hb : b.IsSymm) (hn : finrank 𝕜 E = n)
    (h : ∀ x, RCLike.re (a x x) ≤ RCLike.re (b x x)) (i : Fin n) :
    ha.relEigenvalues hn i ≤ hb.relEigenvalues hn i := by
  refine ha.isSymmetric_toSesqForm_symm.eigenvalue_mono hb.isSymmetric_toSesqForm_symm hn
    (fun x ↦ ?_) i
  rw [← inner_conj_symm, RCLike.conj_re, LinearMap.inner_toSesqForm_symm_apply, ← inner_conj_symm,
    RCLike.conj_re, LinearMap.inner_toSesqForm_symm_apply]
  exact h x

/-- **Lipschitz bound.** `|λ_i[a] − λ_i[b]| ≤ ‖A_a − A_b‖` for the operator norm. -/
theorem abs_relEigenvalues_sub_le_opNorm (ha : a.IsSymm) (hb : b.IsSymm)
    (hn : finrank 𝕜 E = n) (i : Fin n) :
    |ha.relEigenvalues hn i - hb.relEigenvalues hn i| ≤
      ‖LinearMap.toContinuousLinearMap
        ((toSesqForm 𝕜 E E).symm a - (toSesqForm 𝕜 E E).symm b)‖ :=
  LinearMap.IsSymmetric.abs_eigenvalues_sub_le_opNorm ha.isSymmetric_toSesqForm_symm
    hb.isSymmetric_toSesqForm_symm hn i

end LinearMap.IsSymm
