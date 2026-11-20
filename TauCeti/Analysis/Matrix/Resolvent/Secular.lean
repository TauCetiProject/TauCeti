/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.DotProduct
public import TauCeti.Analysis.Matrix.Resolvent.Basic
public import TauCeti.LinearAlgebra.Matrix.SecularEquation

/-!
# Outliers of rank-one perturbations of Hermitian matrices

Let `A` be a Hermitian matrix with eigenvalues `λ j` and eigenvector unitary `U`, let `c` be real
and `u` a vector, and write `b = Uᴴ *ᵥ u` for the coordinates of `u` in the eigenbasis of `A`.
This file puts the secular equation of `Matrix.mem_spectrum_add_vecMulVec_iff` for the Hermitian
rank-one perturbation `A + c • u uᴴ` into its classical spectral form: a real `μ` that is not an
eigenvalue of `A` is an eigenvalue of `A + c • u uᴴ` exactly when

`1 + c * ∑ j, ‖b j‖ ^ 2 / (λ j - μ) = 0`.

For a unit eigenvector `x` of `A + c • u uᴴ` at such a `μ`, the squared overlap with `u` is

`‖uᴴ x‖ ^ 2 = (c ^ 2 * ∑ j, ‖b j‖ ^ 2 / (λ j - μ) ^ 2)⁻¹`.

Above the spectrum of `A` the secular sum is strictly increasing, so `A + c • u uᴴ` has at most
one eigenvalue exceeding every eigenvalue of `A`.

These are the finite-dimensional identities behind the location of the outlier eigenvalues of
spiked random matrices and the limit of the overlap of their eigenvectors with the spike: the
sums are the Stieltjes transform of the spectral measure of `A` in the state `u` and the
derivative of that transform.

## Main results

* `Matrix.IsHermitian.star_dotProduct_inv_sub_smul_one_mulVec` — the spectral expansion
  `uᴴ (A - z • 1)⁻¹ u = ∑ j, ‖b j‖ ^ 2 / (λ j - z)`;
* `Matrix.IsHermitian.star_inv_sub_smul_one_mulVec_dotProduct` — the spectral expansion
  `‖(A - z • 1)⁻¹ u‖ ^ 2 = ∑ j, ‖b j‖ ^ 2 / ‖λ j - z‖ ^ 2`;
* `Matrix.IsHermitian.mem_spectrum_add_smul_vecMulVec_iff` — the secular equation in spectral
  form;
* `Matrix.IsHermitian.norm_star_dotProduct_sq_eq_inv` — the squared overlap of a unit eigenvector
  with the perturbation direction;
* `Matrix.IsHermitian.eq_of_mem_spectrum_add_smul_vecMulVec` — at most one eigenvalue of
  `A + c • u uᴴ` lies above the spectrum of `A`.

## References

* F. Benaych-Georges, R. R. Nadakuditi, *The eigenvalues and eigenvectors of finite, low rank
  perturbations of large random matrices*, Adv. Math. 227 (2011), 494–521, Lemmas 4.1 and 5.1.
* G. H. Golub, *Some modified matrix eigenvalue problems*, SIAM Review 15 (1973), 318–334, §5.
-/

public section

noncomputable section

open Unitary

namespace Matrix.IsHermitian

/-- Above every pole, a secular sum `∑ j, w j / (f j - t)` with nonnegative weights is strictly
increasing in `t` once some weight is positive. -/
private theorem sum_div_sub_lt_sum_div_sub {n : Type*} [Fintype n] {f w : n → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hw₀ : ∃ j, 0 < w j) {s t : ℝ} (hs : ∀ j, f j < s) (hst : s < t) :
    ∑ j, w j / (f j - s) < ∑ j, w j / (f j - t) := by
  have key {a : ℝ} (ha : 0 < a) (j : n) : a / (f j - s) < a / (f j - t) := by
    rw [← neg_sub s, ← neg_sub t, div_neg, div_neg, neg_lt_neg_iff]
    exact div_lt_div_of_pos_left ha (sub_pos.2 (hs j)) (by linarith)
  obtain ⟨j₀, hj₀⟩ := hw₀
  refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨j₀, Finset.mem_univ _, key hj₀ j₀⟩
  rcases (hw j).lt_or_eq with hj | hj
  · exact (key hj j).le
  · simp [← hj]

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
  (hA : A.IsHermitian)

include hA

/-- The quadratic form of the resolvent of a Hermitian matrix, expanded over the eigenbasis:
`uᴴ (A - z • 1)⁻¹ u = ∑ j, ‖(Uᴴ u) j‖ ^ 2 / (λ j - z)`. -/
theorem star_dotProduct_inv_sub_smul_one_mulVec {z : 𝕜} (hz : z ∉ spectrum 𝕜 A) (u : n → 𝕜) :
    star u ⬝ᵥ (A - z • 1)⁻¹ *ᵥ u =
      ∑ j, ((‖((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ *ᵥ u) j‖ ^ 2 : ℝ) : 𝕜) /
        ((hA.eigenvalues j : 𝕜) - z) := by
  rw [hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal hz, conjStarAlgAut_apply,
    star_eq_conjTranspose, star_dotProduct_mul_diagonal_mul_conjTranspose_mulVec]
  simp_rw [inv_mul_eq_div]

/-- The squared norm of the resolvent of a Hermitian matrix applied to `u`, expanded over the
eigenbasis: `‖(A - z • 1)⁻¹ u‖ ^ 2 = ∑ j, ‖(Uᴴ u) j‖ ^ 2 / ‖λ j - z‖ ^ 2`. -/
theorem star_inv_sub_smul_one_mulVec_dotProduct {z : 𝕜} (hz : z ∉ spectrum 𝕜 A) (u : n → 𝕜) :
    star ((A - z • 1)⁻¹ *ᵥ u) ⬝ᵥ (A - z • 1)⁻¹ *ᵥ u =
      ∑ j, ((‖((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ *ᵥ u) j‖ ^ 2 /
        ‖(hA.eigenvalues j : 𝕜) - z‖ ^ 2 : ℝ) : 𝕜) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose,
    hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal hz, ← map_star, ← map_mul, star_eq_conjTranspose,
    diagonal_conjTranspose, diagonal_mul_diagonal, conjStarAlgAut_apply, star_eq_conjTranspose,
    star_dotProduct_mul_diagonal_mul_conjTranspose_mulVec]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul, norm_inv]
  push_cast
  ring

/-- **The secular equation in spectral form.** For a Hermitian `A`, real `c`, and a real `μ`
that is not an eigenvalue of `A`, `μ` is an eigenvalue of `A + c • u uᴴ` exactly when
`1 + c * ∑ j, ‖(Uᴴ u) j‖ ^ 2 / (λ j - μ) = 0`. -/
theorem mem_spectrum_add_smul_vecMulVec_iff (c : ℝ) (u : n → 𝕜) {μ : ℝ}
    (hμ : μ ∉ spectrum ℝ A) :
    μ ∈ spectrum ℝ (A + (c : 𝕜) • vecMulVec u (star u)) ↔
      1 + c * ∑ j, ‖((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ *ᵥ u) j‖ ^ 2 /
        (hA.eigenvalues j - μ) = 0 := by
  rw [← spectrum.algebraMap_mem_iff 𝕜] at hμ ⊢
  rw [← vecMulVec_smul, mem_spectrum_add_vecMulVec_iff hμ, smul_dotProduct,
    hA.star_dotProduct_inv_sub_smul_one_mulVec hμ, ← RCLike.ofReal_eq_zero (K := 𝕜)]
  simp [RCLike.algebraMap_eq_ofReal]

/-- **Overlap of an outlier eigenvector.** Let `A` be Hermitian, `c` real, and `μ` a real number
that is not an eigenvalue of `A`. A unit eigenvector `x` of `A + c • u uᴴ` for `μ` has squared
overlap `‖uᴴ x‖ ^ 2 = (c ^ 2 * ∑ j, ‖(Uᴴ u) j‖ ^ 2 / (λ j - μ) ^ 2)⁻¹` with `u`. -/
theorem norm_star_dotProduct_sq_eq_inv (c : ℝ) {u x : n → 𝕜} {μ : ℝ} (hμ : μ ∉ spectrum ℝ A)
    (hx : (A + (c : 𝕜) • vecMulVec u (star u)) *ᵥ x = (μ : 𝕜) • x) (hx₁ : star x ⬝ᵥ x = 1) :
    ‖star u ⬝ᵥ x‖ ^ 2 =
      (c ^ 2 * ∑ j, ‖((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ *ᵥ u) j‖ ^ 2 /
        (hA.eigenvalues j - μ) ^ 2)⁻¹ := by
  rw [← spectrum.algebraMap_mem_iff 𝕜, RCLike.algebraMap_eq_ofReal] at hμ
  rw [← vecMulVec_smul] at hx
  have hxw := eq_neg_dotProduct_smul_inv_sub_smul_one_mulVec hμ hx
  rw [smul_dotProduct, smul_eq_mul] at hxw
  have hnorm : star x ⬝ᵥ x = ((‖star u ⬝ᵥ x‖ ^ 2 * (c ^ 2 *
      ∑ j, ‖((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ *ᵥ u) j‖ ^ 2 /
        (hA.eigenvalues j - μ) ^ 2) : ℝ) : 𝕜) := by
    conv_lhs => rw [hxw]
    rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      RCLike.star_def, RCLike.conj_mul, hA.star_inv_sub_smul_one_mulVec_dotProduct hμ]
    have hsub (j : n) : ‖(hA.eigenvalues j : 𝕜) - μ‖ ^ 2 = (hA.eigenvalues j - μ) ^ 2 := by
      rw [← RCLike.ofReal_sub, RCLike.norm_ofReal, sq_abs]
    simp only [hsub, norm_neg, norm_mul, RCLike.norm_ofReal, ← RCLike.ofReal_pow, mul_pow, sq_abs]
    push_cast
    ring
  rw [hx₁, eq_comm, ← RCLike.ofReal_one, RCLike.ofReal_inj] at hnorm
  exact eq_inv_of_mul_eq_one_left hnorm

/-- **At most one outlier above the spectrum.** A real rank-one perturbation `A + c • u uᴴ` of a
Hermitian matrix `A` has at most one eigenvalue that exceeds every eigenvalue of `A`. For
`c ≤ 0` it has none. -/
theorem eq_of_mem_spectrum_add_smul_vecMulVec (c : ℝ) (u : n → 𝕜) {μ ν : ℝ}
    (hμ : μ ∈ spectrum ℝ (A + (c : 𝕜) • vecMulVec u (star u)))
    (hν : ν ∈ spectrum ℝ (A + (c : 𝕜) • vecMulVec u (star u)))
    (hμA : ∀ j, hA.eigenvalues j < μ) (hνA : ∀ j, hA.eigenvalues j < ν) : μ = ν := by
  have hnot {t : ℝ} (ht : ∀ j, hA.eigenvalues j < t) : t ∉ spectrum ℝ A := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    rintro ⟨j, rfl⟩
    exact lt_irrefl _ (ht j)
  rw [hA.mem_spectrum_add_smul_vecMulVec_iff c u (hnot hμA)] at hμ
  rw [hA.mem_spectrum_add_smul_vecMulVec_iff c u (hnot hνA)] at hν
  have hw (j : n) : 0 ≤ ‖((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ *ᵥ u) j‖ ^ 2 := by positivity
  -- Above the spectrum every term of the secular sum is nonpositive, so for `c ≤ 0` the secular
  -- equation has no root there.
  rcases le_or_gt c 0 with hc | hc
  · have hsum : ∑ j, ‖((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ *ᵥ u) j‖ ^ 2 /
        (hA.eigenvalues j - μ) ≤ 0 :=
      Finset.sum_nonpos fun j _ ↦ div_nonpos_of_nonneg_of_nonpos (hw j) (by linarith [hμA j])
    nlinarith
  -- Some weight is positive, since otherwise the secular equation reads `1 = 0`.
  have hw₀ : ∃ j, 0 < ‖((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ *ᵥ u) j‖ ^ 2 := by
    by_contra! h
    have h0 (j : n) : ‖((hA.eigenvectorUnitary : Matrix n n 𝕜)ᴴ *ᵥ u) j‖ ^ 2 = 0 :=
      le_antisymm (h j) (hw j)
    simp [h0] at hμ
  rcases lt_trichotomy μ ν with h | h | h
  · have := sum_div_sub_lt_sum_div_sub hw hw₀ hμA h
    nlinarith
  · exact h
  · have := sum_div_sub_lt_sum_div_sub hw hw₀ hνA h
    nlinarith

end Matrix.IsHermitian
