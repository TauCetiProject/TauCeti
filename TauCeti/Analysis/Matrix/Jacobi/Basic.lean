/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.LinearAlgebra.Matrix.Jacobi
import Mathlib.LinearAlgebra.Vandermonde
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.LinearAlgebra.Matrix.MulVec

/-!
# Spectral theory of real symmetric tridiagonal Jacobi matrices

For a real symmetric tridiagonal matrix `TauCeti.jacobiMatrix a b` of size `(n + 1) × (n + 1)`
(defined over arbitrary types with zero in `TauCeti.LinearAlgebra.Matrix.Jacobi`), all `n + 1`
eigenvalues are real, and when every subdiagonal entry `b k` is nonzero they are simple, so the
decreasingly ordered spectrum `TauCeti.jacobiEigenvalues a b` is strictly antitone and every
eigenvector has nonzero first coordinate.

The spectral weights `q k = (v k 0) ^ 2` — the squared first coordinates of unit eigenvectors for
the ordered eigenvalues `λ k` — are independent of eigenvector sign choices and sum to `1` whenever
the spectrum is simple. We define `TauCeti.jacobiSpectralWeight` directly by the Lagrange
interpolation formula in the matrix and its ordered eigenvalues, which makes it canonically defined,
globally measurable, bounded in `[0, 1]`, vanishing at repeated eigenvalues, and continuous at any
matrix where the `k`-th eigenvalue is simple, while agreeing with `(v k 0) ^ 2` there.

## Main definitions

* `TauCeti.jacobiEigenvalues`: the decreasingly ordered eigenvalues of a real Jacobi matrix,
  indexed directly by `Fin (n + 1)`.
* `TauCeti.jacobiSpectralWeight`: the canonical Lagrange spectral weights of a real Jacobi matrix.

## Main results

* `TauCeti.jacobiEigenvalues_strictAnti`: a real Jacobi matrix with nonzero subdiagonal entries
  has strictly decreasing eigenvalues.
* `TauCeti.charpoly_jacobiMatrix` and `TauCeti.jacobiEigenvalues_eq_of_charpoly_eq`:
  characterization of `jacobiEigenvalues` via the split characteristic polynomial.
* `TauCeti.sum_jacobiEigenvalues_sq`:
  `∑ k, jacobiEigenvalues a b k ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2`.
* `TauCeti.jacobiSpectralWeight_eq_sq_eigenvector` and
  `TauCeti.jacobiSpectralWeight_eq_zero_of_jacobiEigenvalues_eq`: `jacobiSpectralWeight a b k`
  equals `(v 0) ^ 2` when the `k`-th eigenvalue is simple and `0` when it is repeated.
* `TauCeti.jacobiSpectralWeight_nonneg` and `TauCeti.jacobiSpectralWeight_le_one`: unconditional
  bounds `0 ≤ jacobiSpectralWeight a b k ≤ 1`.
* `TauCeti.aeval_jacobiMatrix_apply_zero_zero` and `TauCeti.jacobiMatrix_pow_apply_zero_zero`:
  polynomial and moment identities for the `(0, 0)` entry under simple spectrum.
* `TauCeti.continuousAt_jacobiSpectralWeight_apply`, `TauCeti.continuousAt_jacobiSpectralWeight`,
  and `TauCeti.continuousOn_jacobiSpectralWeight`: pointwise and simple-spectrum continuity of
  spectral weights.
* `TauCeti.abs_prod_pow_eq_prod_sqrt_jacobiSpectralWeight_mul_prod_sub_jacobiEigenvalues` and
  `TauCeti.prod_pow_eq_prod_sqrt_jacobiSpectralWeight_mul_prod_sub_jacobiEigenvalues`: the
  Dumitriu–Edelman identity linking `|∏ j, b j ^ (n - j)|` (or `∏ j, b j ^ (n - j)` for
  nonnegative `b`) to the spectral weights and the ordered eigenvalue differences.

## References

* I. Dumitriu, A. Edelman, *Matrix models for beta ensembles*, J. Math. Phys. 43 (2002),
  5830–5847.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.5.1.
-/

public section

noncomputable section

open Matrix Finset Polynomial
open scoped RealInnerProductSpace

namespace TauCeti

/-! ### Continuity and measurability of Jacobi matrices -/

section Regularity

variable {R : Type*} [Zero R] {n : ℕ}

/-- The Jacobi matrix depends continuously on its diagonal and subdiagonal entries. -/
@[fun_prop]
theorem continuous_jacobiMatrix [TopologicalSpace R] :
    Continuous fun p : (Fin (n + 1) → R) × (Fin n → R) => jacobiMatrix p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [jacobiMatrix_apply]
  split_ifs
  · exact (continuous_apply i).comp continuous_fst
  · exact (continuous_apply _).comp continuous_snd
  · exact (continuous_apply _).comp continuous_snd
  · exact continuous_const

/-- The Jacobi matrix depends measurably on its diagonal and subdiagonal entries. -/
@[fun_prop]
theorem measurable_jacobiMatrix [MeasurableSpace R] :
    Measurable fun p : (Fin (n + 1) → R) × (Fin n → R) => jacobiMatrix p.1 p.2 := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [jacobiMatrix_apply]
  split_ifs
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply _).comp measurable_snd
  · exact (measurable_pi_apply _).comp measurable_snd
  · exact measurable_const

end Regularity

/-! ### Ordered eigenvalues and simplicity -/

section Spectral

variable {n : ℕ}

/-- The decreasingly ordered eigenvalues of `jacobiMatrix a b`, indexed directly by `Fin (n + 1)`.
-/
def jacobiEigenvalues (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun k => (isHermitian_jacobiMatrix a b).eigenvalues₀ (k.cast (Fintype.card_fin (n + 1)).symm)

/-- Defining bridge between `jacobiEigenvalues` and `Matrix.IsHermitian.eigenvalues₀`. -/
theorem jacobiEigenvalues_apply (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (k : Fin (n + 1)) :
    jacobiEigenvalues a b k =
      (isHermitian_jacobiMatrix a b).eigenvalues₀ (k.cast (Fintype.card_fin (n + 1)).symm) :=
  (rfl)

/-- The ordered eigenvalues of `jacobiMatrix a b` are antitone. -/
theorem jacobiEigenvalues_antitone (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    Antitone (jacobiEigenvalues a b) := fun _ _ hij =>
  (isHermitian_jacobiMatrix a b).eigenvalues₀_antitone (Fin.le_def.mpr hij)

/-- The ordered eigenvalues of `jacobiMatrix a b` depend continuously on `(a, b)`. -/
@[fun_prop]
theorem continuous_jacobiEigenvalues :
    Continuous fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => jacobiEigenvalues p.1 p.2 := by
  refine continuous_pi fun k => (continuous_apply _).comp ?_
  exact Matrix.continuous_eigenvalues₀.comp
    (continuous_jacobiMatrix.subtype_mk fun p => isHermitian_jacobiMatrix p.1 p.2)

/-- The ordered eigenvalues of `jacobiMatrix a b` depend measurably on `(a, b)`. -/
@[fun_prop]
theorem measurable_jacobiEigenvalues :
    Measurable fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => jacobiEigenvalues p.1 p.2 :=
  continuous_jacobiEigenvalues.measurable

/-- The canonical index equivalence aligning `Matrix.IsHermitian.eigenvalues` with
`jacobiEigenvalues`. -/
private def jacobiEigenvaluesEquiv (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) :=
  (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin (n + 1))))).symm.trans
    (finCongr (Fintype.card_fin (n + 1)))

private theorem eigenvalues_eq_jacobiEigenvalues_equiv (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (i : Fin (n + 1)) :
    (isHermitian_jacobiMatrix a b).eigenvalues i =
      jacobiEigenvalues a b (jacobiEigenvaluesEquiv n i) := by
  simp [Matrix.IsHermitian.eigenvalues, jacobiEigenvalues, jacobiEigenvaluesEquiv]

/-- The orthonormal basis of eigenvectors of `jacobiMatrix a b` aligned with `jacobiEigenvalues`. -/
private def jacobiEigenvectorBasis (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    OrthonormalBasis (Fin (n + 1)) ℝ (EuclideanSpace ℝ (Fin (n + 1))) :=
  ((isSymmetric_toEuclideanLin_iff.mpr (isHermitian_jacobiMatrix a b)).eigenvectorBasis
    finrank_euclideanSpace).reindex (finCongr (Fintype.card_fin (n + 1)))

private theorem eigenvectorBasis_eq_jacobiEigenvectorBasis_equiv (a : Fin (n + 1) → ℝ)
    (b : Fin n → ℝ) (i : Fin (n + 1)) :
    (isHermitian_jacobiMatrix a b).eigenvectorBasis i =
      jacobiEigenvectorBasis a b (jacobiEigenvaluesEquiv n i) := by
  simp [Matrix.IsHermitian.eigenvectorBasis, jacobiEigenvectorBasis, jacobiEigenvaluesEquiv]

private theorem mulVec_jacobiEigenvectorBasis (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (k : Fin (n + 1)) :
    jacobiMatrix a b *ᵥ ⇑(jacobiEigenvectorBasis a b k) =
      jacobiEigenvalues a b k • ⇑(jacobiEigenvectorBasis a b k) := by
  have h := (isSymmetric_toEuclideanLin_iff.mpr
    (isHermitian_jacobiMatrix a b)).apply_eigenvectorBasis finrank_euclideanSpace
      (k.cast (Fintype.card_fin (n + 1)).symm)
  simpa only [jacobiEigenvectorBasis, OrthonormalBasis.reindex_apply, finCongr_symm,
    finCongr_apply, jacobiEigenvalues, Matrix.IsHermitian.eigenvalues₀, Matrix.toLpLin_apply,
    RCLike.ofReal_real_eq_id, id_eq, WithLp.ofLp_smul] using congrArg WithLp.ofLp h

/-- A real Jacobi matrix with nonzero subdiagonal entries has strictly decreasing eigenvalues. -/
theorem jacobiEigenvalues_strictAnti {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (hb : ∀ k, b k ≠ 0) : StrictAnti (jacobiEigenvalues a b) := by
  refine (jacobiEigenvalues_antitone a b).strictAnti_of_injective fun i j hij => ?_
  by_contra hne
  let vi := jacobiEigenvectorBasis a b i
  let vj := jacobiEigenvectorBasis a b j
  have hvi : jacobiMatrix a b *ᵥ ⇑vi = jacobiEigenvalues a b i • ⇑vi :=
    mulVec_jacobiEigenvectorBasis a b i
  have hvj : jacobiMatrix a b *ᵥ ⇑vj = jacobiEigenvalues a b i • ⇑vj := by
    rw [hij]; exact mulVec_jacobiEigenvectorBasis a b j
  have hcomb : jacobiMatrix a b *ᵥ (vj 0 • ⇑vi - vi 0 • ⇑vj) =
      jacobiEigenvalues a b i • (vj 0 • ⇑vi - vi 0 • ⇑vj) := by
    rw [mulVec_sub, mulVec_smul, mulVec_smul, hvi, hvj, smul_sub, smul_comm (vj 0),
      smul_comm (vi 0)]
  have hlin : vj 0 • ⇑vi - vi 0 • ⇑vj = 0 :=
    eq_zero_of_mulVec_jacobiMatrix_eq_smul_of_apply_zero_eq_zero hb hcomb (by simp [mul_comm])
  have hlinE : vj 0 • vi = vi 0 • vj := by
    ext r
    have hr := congrFun hlin r
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at hr
    simpa [PiLp.smul_apply, smul_eq_mul] using hr
  have hortho : ⟪vi, vj⟫ = 0 := (jacobiEigenvectorBasis a b).orthonormal.2 hne
  have hnorm : ⟪vi, vi⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, (jacobiEigenvectorBasis a b).orthonormal.1 i, one_pow]
  have hvj0 : vj 0 = 0 := by
    have := congrArg (fun x => ⟪vi, x⟫) hlinE
    simp only [inner_smul_right, hnorm, hortho, mul_one, mul_zero] at this
    exact this
  exact apply_zero_ne_zero_of_mulVec_jacobiMatrix_eq_smul hb hvj
    (fun h => (jacobiEigenvectorBasis a b).orthonormal.ne_zero j (PiLp.ext (congrFun h))) hvj0

/-- The characteristic polynomial of `jacobiMatrix a b` factors over `ℝ` along
`jacobiEigenvalues a b`. -/
theorem charpoly_jacobiMatrix (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    (jacobiMatrix a b).charpoly =
      ∏ k, (Polynomial.X - Polynomial.C (jacobiEigenvalues a b k)) := by
  rw [(isHermitian_jacobiMatrix a b).charpoly_eq]
  exact Fintype.prod_equiv (jacobiEigenvaluesEquiv n) _ _ fun i => by
    rw [RCLike.ofReal_real_eq_id, id_eq, eigenvalues_eq_jacobiEigenvalues_equiv]

/-- If the characteristic polynomial of `jacobiMatrix a b` splits over `ℝ` with decreasing roots
`lam`, then `jacobiEigenvalues a b = lam`. -/
theorem jacobiEigenvalues_eq_of_charpoly_eq {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    {lam : Fin (n + 1) → ℝ} (hlam : Antitone lam)
    (hchar : (jacobiMatrix a b).charpoly =
      ∏ k, (Polynomial.X - Polynomial.C (lam k))) :
    jacobiEigenvalues a b = lam := by
  let e := finCongr (Fintype.card_fin (n + 1))
  have hchar' : (jacobiMatrix a b).charpoly =
      ∏ k : Fin (Fintype.card (Fin (n + 1))), (Polynomial.X - Polynomial.C ((lam ∘ e) k)) := by
    rw [hchar]
    exact Fintype.prod_equiv e.symm _ _ fun k => by simp [e]
  have heq := (isHermitian_jacobiMatrix a b).eigenvalues₀_eq_of_charpoly_eq
    (fun _ _ hij => hlam (by simpa [e] using hij)) hchar'
  funext k
  simpa [jacobiEigenvalues, e] using congrFun heq (e.symm k)

/-- Scaling a Jacobi matrix by a nonnegative scalar `s` scales its ordered eigenvalues by `s`. -/
theorem jacobiEigenvalues_smul {s : ℝ} (hs : 0 ≤ s) (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    jacobiEigenvalues (s • a) (s • b) = s • jacobiEigenvalues a b := by
  have hirrel : ∀ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hM : M.IsHermitian),
      M = s • jacobiMatrix a b →
      hM.eigenvalues₀ = ((isHermitian_jacobiMatrix a b).smul (IsSelfAdjoint.all s)).eigenvalues₀ :=
    by rintro _ _ rfl; rfl
  funext k
  rw [jacobiEigenvalues_apply, hirrel _ _ (jacobiMatrix_smul s a b),
    (isHermitian_jacobiMatrix a b).eigenvalues₀_smul hs, Pi.smul_apply, Pi.smul_apply,
    jacobiEigenvalues_apply]

/-- The sum of squares of the ordered eigenvalues of `jacobiMatrix a b` equals
`∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2`. -/
theorem sum_jacobiEigenvalues_sq (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    ∑ k : Fin (n + 1), jacobiEigenvalues a b k ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ k, b k ^ 2 := by
  rw [← trace_jacobiMatrix_sq a b,
    (isHermitian_jacobiMatrix a b).trace_pow_eq_sum_eigenvalues_pow 2]
  exact (Fintype.sum_equiv (jacobiEigenvaluesEquiv n) _ _ fun i => by
    simp [eigenvalues_eq_jacobiEigenvalues_equiv]).symm

/-! ### Lagrange spectral weights -/

/-- For any polynomial `p` and real Jacobi matrix `J`, `(aeval J p) 0 0` is the weighted sum of
`p (λ k)` against the squared first entries of the orthonormal eigenvector basis. -/
private theorem aeval_jacobiMatrix_apply_zero_zero_eq_sum_basis (a : Fin (n + 1) → ℝ)
    (b : Fin n → ℝ) (p : ℝ[X]) :
    (Polynomial.aeval (jacobiMatrix a b) p) 0 0 =
      ∑ k : Fin (n + 1), (jacobiEigenvectorBasis a b k 0) ^ 2 *
        p.eval (jacobiEigenvalues a b k) := by
  rw [(isHermitian_jacobiMatrix a b).aeval_apply_eq_sum_eigenvalues p 0 0]
  refine Fintype.sum_equiv (jacobiEigenvaluesEquiv n) _ _ fun i => ?_
  rw [Matrix.IsHermitian.eigenvectorUnitary_apply, star_trivial,
    eigenvalues_eq_jacobiEigenvalues_equiv, eigenvectorBasis_eq_jacobiEigenvectorBasis_equiv,
    RCLike.ofReal_real_eq_id, id_eq]
  ring

private theorem nodup_filter_finRange_ne (k : Fin (n + 1)) :
    ((List.finRange (n + 1)).filter (· ≠ k)).Nodup :=
  (List.nodup_finRange (n + 1)).filter _

private theorem toFinset_filter_finRange_ne (k : Fin (n + 1)) :
    ((List.finRange (n + 1)).filter (· ≠ k)).toFinset = Finset.univ.erase k := by
  ext j
  simp [Finset.mem_erase]

/-- The canonical spectral weight associated to the `k`-th decreasing eigenvalue of
`jacobiMatrix a b`, defined by the Lagrange interpolation ratio in the matrix and its ordered
eigenvalues. Whenever the `k`-th eigenvalue is simple, it equals `(v k 0) ^ 2` for every unit
eigenvector `v k` of the `k`-th eigenvalue; when the eigenvalue is repeated, it vanishes. -/
def jacobiSpectralWeight (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (k : Fin (n + 1)) : ℝ :=
  let J := jacobiMatrix a b
  let lam := jacobiEigenvalues a b
  ((((List.finRange (n + 1)).filter (· ≠ k)).map
      fun j => J - lam j • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).prod) 0 0 /
    ∏ j ∈ Finset.univ.erase k, (lam k - lam j)

private theorem list_prod_sub_smul_eq_aeval (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (k : Fin (n + 1)) :
    (((List.finRange (n + 1)).filter (· ≠ k)).map
      fun j => jacobiMatrix a b - jacobiEigenvalues a b j •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).prod =
      Polynomial.aeval (jacobiMatrix a b)
        (∏ j ∈ Finset.univ.erase k,
          (Polynomial.X - Polynomial.C (jacobiEigenvalues a b j))) := by
  have hcomp : (fun j => jacobiMatrix a b - jacobiEigenvalues a b j •
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) =
      (Polynomial.aeval (jacobiMatrix a b)) ∘
        (fun j => Polynomial.X - Polynomial.C (jacobiEigenvalues a b j)) := by
    funext j
    simp [Algebra.algebraMap_eq_smul_one]
  rw [hcomp, ← List.map_map, ← map_list_prod]
  congr 1
  rw [← toFinset_filter_finRange_ne k, List.prod_toFinset _ (nodup_filter_finRange_ne k)]

/-- Lagrange polynomial representation of `jacobiSpectralWeight a b k`. -/
theorem jacobiSpectralWeight_eq_aeval_div (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (k : Fin (n + 1)) :
    jacobiSpectralWeight a b k =
      (Polynomial.aeval (jacobiMatrix a b)
        (∏ j ∈ Finset.univ.erase k,
          (Polynomial.X - Polynomial.C (jacobiEigenvalues a b j)))) 0 0 /
        ∏ j ∈ Finset.univ.erase k, (jacobiEigenvalues a b k - jacobiEigenvalues a b j) := by
  unfold jacobiSpectralWeight
  dsimp only
  rw [list_prod_sub_smul_eq_aeval]

private theorem jacobiSpectralWeight_eq_sq_basis {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    {k : Fin (n + 1)} (hsimple : ∀ j ≠ k, jacobiEigenvalues a b j ≠ jacobiEigenvalues a b k) :
    jacobiSpectralWeight a b k = (jacobiEigenvectorBasis a b k 0) ^ 2 := by
  let lam := jacobiEigenvalues a b
  have hden : ∏ j ∈ Finset.univ.erase k, (lam k - lam j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj =>
      sub_ne_zero.mpr (hsimple j (Finset.ne_of_mem_erase hj)).symm
  rw [jacobiSpectralWeight_eq_aeval_div, aeval_jacobiMatrix_apply_zero_zero_eq_sum_basis,
    Finset.sum_eq_single k]
  · simp [Polynomial.eval_prod, lam, mul_div_cancel_right₀ _ hden]
  · intro m _ hmk
    have hzero : (∏ j ∈ Finset.univ.erase k, (Polynomial.X - Polynomial.C (lam j))).eval
        (lam m) = 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hmk, Finset.mem_univ m⟩) (by simp)
    rw [hzero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Whenever the `k`-th eigenvalue of `jacobiMatrix a b` is simple, `jacobiSpectralWeight a b k`
equals `(v 0) ^ 2` for every unit eigenvector `v` of `jacobiMatrix a b` with eigenvalue
`jacobiEigenvalues a b k`. -/
theorem jacobiSpectralWeight_eq_sq_eigenvector {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    {k : Fin (n + 1)} (hsimple : ∀ j ≠ k, jacobiEigenvalues a b j ≠ jacobiEigenvalues a b k)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv_norm : ‖v‖ = 1)
    (hv_eig : jacobiMatrix a b *ᵥ ⇑v = jacobiEigenvalues a b k • ⇑v) :
    jacobiSpectralWeight a b k = (v 0) ^ 2 := by
  rw [jacobiSpectralWeight_eq_sq_basis hsimple]
  let u := jacobiEigenvectorBasis a b
  have hsymm := isSymmetric_toEuclideanLin_iff.mpr (isHermitian_jacobiMatrix a b)
  have hv_toLin : (jacobiMatrix a b).toEuclideanLin v = jacobiEigenvalues a b k • v :=
    PiLp.ext fun r => by simpa [Matrix.toLpLin_apply] using congrFun hv_eig r
  have hortho : ∀ j ≠ k, ⟪u j, v⟫ = 0 := fun j hjk => by
    have hu_toLin : (jacobiMatrix a b).toEuclideanLin (u j) = jacobiEigenvalues a b j • u j :=
      PiLp.ext fun r => by
        simpa [Matrix.toLpLin_apply] using congrFun (mulVec_jacobiEigenvectorBasis a b j) r
    exact hsymm.orthogonalFamily_eigenspaces (hsimple j hjk)
      ⟨u j, Module.End.mem_eigenspace_iff.mpr hu_toLin⟩
      ⟨v, Module.End.mem_eigenspace_iff.mpr hv_toLin⟩
  have hv_eq : v = ⟪u k, v⟫ • u k := by
    conv_lhs => rw [← u.sum_repr' v]
    rw [Finset.sum_eq_single k]
    · intro j _ hjk; rw [hortho j hjk, zero_smul]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hc_sq : ⟪u k, v⟫ ^ 2 = 1 := by
    have h := congrArg (fun x => ‖x‖ ^ 2) hv_eq
    simp only [hv_norm, one_pow, norm_smul, Real.norm_eq_abs, u.orthonormal.1 k, mul_one,
      sq_abs] at h
    exact h.symm
  have h0 : v 0 = ⟪u k, v⟫ * u k 0 := by
    simpa [PiLp.smul_apply, smul_eq_mul] using congrArg (fun x : EuclideanSpace ℝ _ => x 0) hv_eq
  rw [h0, mul_pow, hc_sq, one_mul]

/-- If the `k`-th ordered eigenvalue coincides with another ordered eigenvalue, its Lagrange
spectral weight vanishes. -/
theorem jacobiSpectralWeight_eq_zero_of_jacobiEigenvalues_eq {a : Fin (n + 1) → ℝ}
    {b : Fin n → ℝ} {j k : Fin (n + 1)} (hjk : j ≠ k)
    (heq : jacobiEigenvalues a b j = jacobiEigenvalues a b k) :
    jacobiSpectralWeight a b k = 0 := by
  have hden : ∏ i ∈ Finset.univ.erase k,
      (jacobiEigenvalues a b k - jacobiEigenvalues a b i) = 0 :=
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩) (by rw [heq, sub_self])
  simp [jacobiSpectralWeight, hden]

/-- Every spectral weight is nonnegative. -/
theorem jacobiSpectralWeight_nonneg (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (k : Fin (n + 1)) :
    0 ≤ jacobiSpectralWeight a b k := by
  by_cases hsimple : ∀ j ≠ k, jacobiEigenvalues a b j ≠ jacobiEigenvalues a b k
  · rw [jacobiSpectralWeight_eq_sq_basis hsimple]
    exact sq_nonneg _
  · push Not at hsimple
    obtain ⟨j, hjk, heq⟩ := hsimple
    rw [jacobiSpectralWeight_eq_zero_of_jacobiEigenvalues_eq hjk heq]

/-- Every spectral weight is at most `1`. -/
theorem jacobiSpectralWeight_le_one (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (k : Fin (n + 1)) :
    jacobiSpectralWeight a b k ≤ 1 := by
  by_cases hsimple : ∀ j ≠ k, jacobiEigenvalues a b j ≠ jacobiEigenvalues a b k
  · rw [jacobiSpectralWeight_eq_sq_basis hsimple]
    have hnorm : ∑ i : Fin (n + 1), (jacobiEigenvectorBasis a b k i) ^ 2 = 1 := by
      have h := EuclideanSpace.norm_sq_eq (jacobiEigenvectorBasis a b k)
      simp only [(jacobiEigenvectorBasis a b).orthonormal.1 k, one_pow, Real.norm_eq_abs,
        sq_abs] at h
      exact h.symm
    rw [← hnorm]
    exact Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ 0)
  · push Not at hsimple
    obtain ⟨j, hjk, heq⟩ := hsimple
    rw [jacobiSpectralWeight_eq_zero_of_jacobiEigenvalues_eq hjk heq]
    exact zero_le_one

/-- Every spectral weight of a Jacobi matrix with nonzero subdiagonals is strictly positive. -/
theorem jacobiSpectralWeight_pos {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ} (hb : ∀ j, b j ≠ 0)
    (k : Fin (n + 1)) : 0 < jacobiSpectralWeight a b k := by
  rw [jacobiSpectralWeight_eq_sq_basis
    (fun _ hj => (jacobiEigenvalues_strictAnti hb).injective.ne hj)]
  have hne : jacobiEigenvectorBasis a b k 0 ≠ 0 :=
    apply_zero_ne_zero_of_mulVec_jacobiMatrix_eq_smul hb (mulVec_jacobiEigenvectorBasis a b k)
      (fun h => (jacobiEigenvectorBasis a b).orthonormal.ne_zero k (PiLp.ext (congrFun h)))
  exact sq_pos_of_ne_zero hne

/-- Polynomial functional identity: when the eigenvalues of `jacobiMatrix a b` are distinct,
`(aeval (jacobiMatrix a b) p) 0 0` equals the integral of `p` against the discrete spectral
measure `∑ k, q k δ_{λ k}`. -/
theorem aeval_jacobiMatrix_apply_zero_zero {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (hlam : Function.Injective (jacobiEigenvalues a b)) (p : ℝ[X]) :
    (Polynomial.aeval (jacobiMatrix a b) p) 0 0 =
      ∑ k : Fin (n + 1), jacobiSpectralWeight a b k * p.eval (jacobiEigenvalues a b k) := by
  simp_rw [jacobiSpectralWeight_eq_sq_basis (fun _ hj => hlam.ne hj)]
  exact aeval_jacobiMatrix_apply_zero_zero_eq_sum_basis a b p

/-- Moment identity: when the eigenvalues of `jacobiMatrix a b` are distinct,
`((jacobiMatrix a b) ^ r) 0 0` is the `r`-th moment of the discrete spectral measure
`∑ k, q k δ_{λ k}`. -/
theorem jacobiMatrix_pow_apply_zero_zero {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (hlam : Function.Injective (jacobiEigenvalues a b)) (r : ℕ) :
    (jacobiMatrix a b ^ r) 0 0 =
      ∑ k : Fin (n + 1), jacobiSpectralWeight a b k * jacobiEigenvalues a b k ^ r := by
  simpa using aeval_jacobiMatrix_apply_zero_zero hlam (Polynomial.X ^ r)

/-- The spectral weights of a Jacobi matrix with simple eigenvalues sum to `1`. -/
theorem sum_jacobiSpectralWeight {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (hlam : Function.Injective (jacobiEigenvalues a b)) :
    ∑ k : Fin (n + 1), jacobiSpectralWeight a b k = 1 := by
  simpa using (jacobiMatrix_pow_apply_zero_zero hlam 0).symm

/-- Positive scaling of a Jacobi matrix leaves its spectral weights unchanged. -/
theorem jacobiSpectralWeight_smul {s : ℝ} (hs : 0 < s) (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    jacobiSpectralWeight (s • a) (s • b) = jacobiSpectralWeight a b := by
  funext k
  unfold jacobiSpectralWeight
  dsimp only
  rw [jacobiMatrix_smul, jacobiEigenvalues_smul hs.le]
  have hmap : (fun j => s • jacobiMatrix a b - (s • jacobiEigenvalues a b) j •
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) =
      (s • ·) ∘ (fun j => jacobiMatrix a b - jacobiEigenvalues a b j •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) := by
    funext j
    rw [Function.comp_apply, Pi.smul_apply, smul_eq_mul, smul_sub, smul_smul]
  rw [hmap, ← List.map_map, ← List.smul_prod, List.length_map]
  have hlen : ((List.finRange (n + 1)).filter (· ≠ k)).length = (Finset.univ.erase k).card := by
    rw [← toFinset_filter_finRange_ne k, List.toFinset_card_of_nodup (nodup_filter_finRange_ne k)]
  have hden : ∏ j ∈ Finset.univ.erase k,
      ((s • jacobiEigenvalues a b) k - (s • jacobiEigenvalues a b) j) =
      s ^ (Finset.univ.erase k).card *
        ∏ j ∈ Finset.univ.erase k, (jacobiEigenvalues a b k - jacobiEigenvalues a b j) := by
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, Finset.prod_mul_distrib, Finset.prod_const]
  rw [hlen, Matrix.smul_apply, smul_eq_mul, hden]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hs.ne')

private theorem continuous_jacobiSpectralWeight_num (k : Fin (n + 1)) :
    Continuous fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      ((((List.finRange (n + 1)).filter (· ≠ k)).map
        fun j => jacobiMatrix p.1 p.2 -
          jacobiEigenvalues p.1 p.2 j •
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).prod) 0 0 := by
  have hlam : ∀ j, Continuous fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      jacobiEigenvalues p.1 p.2 j := fun j =>
    (continuous_apply j).comp continuous_jacobiEigenvalues
  have hprod : Continuous fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      ((((List.finRange (n + 1)).filter (· ≠ k)).map
        fun j => jacobiMatrix p.1 p.2 -
          jacobiEigenvalues p.1 p.2 j •
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).prod) :=
    continuous_list_prod ((List.finRange (n + 1)).filter (· ≠ k)) fun j _ =>
      continuous_jacobiMatrix.sub ((hlam j).smul continuous_const)
  exact (continuous_apply 0).comp ((continuous_apply 0).comp hprod)

private theorem continuous_jacobiSpectralWeight_den (k : Fin (n + 1)) :
    Continuous fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      ∏ j ∈ Finset.univ.erase k,
        (jacobiEigenvalues p.1 p.2 k - jacobiEigenvalues p.1 p.2 j) := by
  fun_prop

/-- The spectral weight vector is globally measurable. -/
@[fun_prop]
theorem measurable_jacobiSpectralWeight :
    Measurable fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => jacobiSpectralWeight p.1 p.2 := by
  refine measurable_pi_iff.mpr fun k => ?_
  exact (continuous_jacobiSpectralWeight_num k).measurable.div
    (continuous_jacobiSpectralWeight_den k).measurable

/-- The `k`-th spectral weight is continuous at every parameter where the `k`-th ordered
eigenvalue is simple. -/
theorem continuousAt_jacobiSpectralWeight_apply
    {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)} {k : Fin (n + 1)}
    (hsimple : ∀ j ≠ k, jacobiEigenvalues p.1 p.2 j ≠ jacobiEigenvalues p.1 p.2 k) :
    ContinuousAt (fun q : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => jacobiSpectralWeight q.1 q.2 k) p :=
  (continuous_jacobiSpectralWeight_num k).continuousAt.div
    (continuous_jacobiSpectralWeight_den k).continuousAt <|
    Finset.prod_ne_zero_iff.mpr fun j hj =>
      sub_ne_zero.mpr (hsimple j (Finset.ne_of_mem_erase hj)).symm

/-- The spectral weight vector is continuous at every parameter with distinct eigenvalues. -/
theorem continuousAt_jacobiSpectralWeight {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ)}
    (hlam : Function.Injective (jacobiEigenvalues p.1 p.2)) :
    ContinuousAt (fun q : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => jacobiSpectralWeight q.1 q.2) p :=
  continuousAt_pi.mpr fun _ => continuousAt_jacobiSpectralWeight_apply fun _ hj => hlam.ne hj

/-- The spectral weight vector is continuous on the locus of simple spectra. -/
theorem continuousOn_jacobiSpectralWeight :
    ContinuousOn (fun p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) => jacobiSpectralWeight p.1 p.2)
      {p | Function.Injective (jacobiEigenvalues p.1 p.2)} :=
  fun _ hp => (continuousAt_jacobiSpectralWeight hp).continuousWithinAt

/-! ### The Dumitriu–Edelman Vandermonde–weight identity -/

private theorem eigenvectorMatrix_transpose_mul_jacobiKrylovMatrix (a : Fin (n + 1) → ℝ)
    (b : Fin n → ℝ) :
    (Matrix.of fun i k => jacobiEigenvectorBasis a b k i)ᵀ * jacobiKrylovMatrix a b =
      Matrix.diagonal (fun k => jacobiEigenvectorBasis a b k 0) *
        Matrix.vandermonde (jacobiEigenvalues a b) := by
  let v := jacobiEigenvectorBasis a b
  ext k m
  rw [Matrix.mul_apply, Matrix.diagonal_mul, Matrix.vandermonde_apply]
  have hsym : ∑ i, (Matrix.of fun i k => v k i)ᵀ k i * jacobiKrylovMatrix a b i m =
      ((jacobiMatrix a b ^ m.val) *ᵥ ⇑(v k)) 0 := by
    simp only [transpose_apply, of_apply, jacobiKrylovMatrix_apply, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [((isSymm_jacobiMatrix a b).pow m.val).apply 0 i, mul_comm]
  rw [hsym, Matrix.pow_mulVec_eq_pow_smul (mulVec_jacobiEigenvectorBasis a b k) m.val,
    Pi.smul_apply, smul_eq_mul, mul_comm]

private theorem abs_det_eigenvectorMatrix_transpose (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    |(Matrix.of fun i k => jacobiEigenvectorBasis a b k i)ᵀ.det| = 1 := by
  let v := jacobiEigenvectorBasis a b
  let e := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  -- The matrix with columns `v k` is definitionally `e.toBasis.toMatrix v.toBasis`.
  have hU : (Matrix.of fun i k => v k i) = e.toBasis.toMatrix v.toBasis := by
    ext i k
    simp [e, Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr]
  rw [hU, Matrix.det_transpose, ← Real.norm_eq_abs, ← Module.Basis.det_apply]
  exact e.det_to_matrix_orthonormalBasis v

/-- **Vandermonde–weight identity (unsigned)**: for any real Jacobi matrix,
`|∏ j, b j ^ (n - j)|` equals the product of the square roots of its spectral weights times the
product of pairwise differences of its decreasingly ordered eigenvalues. Both sides vanish if an
eigenvalue is repeated. -/
theorem abs_prod_pow_eq_prod_sqrt_jacobiSpectralWeight_mul_prod_sub_jacobiEigenvalues
    (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) :
    |∏ j : Fin n, b j ^ (n - j.val)| =
      (∏ k : Fin (n + 1), Real.sqrt (jacobiSpectralWeight a b k)) *
        ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
          (jacobiEigenvalues a b i - jacobiEigenvalues a b j) := by
  have hvand : |(Matrix.vandermonde (jacobiEigenvalues a b)).det| =
      ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
        (jacobiEigenvalues a b i - jacobiEigenvalues a b j) := by
    rw [Matrix.det_vandermonde, Finset.abs_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.abs_prod]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hle := jacobiEigenvalues_antitone a b (Finset.mem_Ioi.mp hj).le
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
  by_cases hlam : Function.Injective (jacobiEigenvalues a b)
  · let v := jacobiEigenvectorBasis a b
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i k => v k i
    have hdetU : |Uᵀ.det| = 1 := abs_det_eigenvectorMatrix_transpose a b
    have hdet : |(Uᵀ * jacobiKrylovMatrix a b).det| =
        |(Matrix.diagonal (fun k => v k 0) * Matrix.vandermonde (jacobiEigenvalues a b)).det| :=
      congrArg (fun M : Matrix _ _ ℝ => |M.det|)
        (eigenvectorMatrix_transpose_mul_jacobiKrylovMatrix a b)
    simp only [Matrix.det_mul, abs_mul, hdetU, one_mul, Matrix.det_diagonal,
      det_jacobiKrylovMatrix] at hdet
    rw [hdet, hvand]
    congr 1
    rw [Finset.abs_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [jacobiSpectralWeight_eq_sq_basis (fun _ hj => hlam.ne hj), Real.sqrt_sq_eq_abs]
  · have hb0 : ∃ j : Fin n, b j = 0 := by
      by_contra hne
      push Not at hne
      exact hlam (jacobiEigenvalues_strictAnti hne).injective
    obtain ⟨j₀, hj₀⟩ := hb0
    have hlhs : ∏ j : Fin n, b j ^ (n - j.val) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [hj₀, zero_pow (by omega)])
    rw [hlhs, abs_zero, ← hvand, not_ne_iff.mp (Matrix.det_vandermonde_ne_zero_iff.not.mpr hlam),
      abs_zero, mul_zero]

/-- **Vandermonde–weight identity**: for a Jacobi matrix with nonnegative subdiagonal entries,
`∏ j, b j ^ (n - j)` equals the product of the square roots of its spectral weights times the
product of pairwise differences of its ordered eigenvalues. -/
theorem prod_pow_eq_prod_sqrt_jacobiSpectralWeight_mul_prod_sub_jacobiEigenvalues
    {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ} (hb : ∀ j, 0 ≤ b j) :
    ∏ j : Fin n, b j ^ (n - j.val) =
      (∏ k : Fin (n + 1), Real.sqrt (jacobiSpectralWeight a b k)) *
        ∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i,
          (jacobiEigenvalues a b i - jacobiEigenvalues a b j) := by
  rw [← abs_prod_pow_eq_prod_sqrt_jacobiSpectralWeight_mul_prod_sub_jacobiEigenvalues a b,
    abs_of_nonneg (Finset.prod_nonneg fun j _ => pow_nonneg (hb j) _)]

end Spectral

end TauCeti
