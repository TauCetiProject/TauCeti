/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Basic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
public import TauCeti.RingTheory.PowerSeries.Geometric

/-!
# The `h`--`e` convolution and the Toeplitz inverse

The complete homogeneous symmetric polynomials `h_n` and the elementary symmetric polynomials
`e_n` are related by the generating-function identity

`(∑ₙ hₙ tⁿ) · (∑ₙ (-1)ⁿ eₙ tⁿ) = 1`,

whose coefficient form is the convolution

`∑_{r + s = m} h_r · (-1)ˢ e_s = δ_{m0}`.

This is the Toeplitz-inverse identity behind the dual (transpose) Jacobi--Trudi formula: the
matrix `(h_{j - i})` and the matrix `((-1)^{j - i} e_{j - i})` are inverse to each other, so the
`s_μ` minor of the first is complementary to the `s_{μᵀ}` minor of the second.  Both matrices
are upper unitriangular, hence have determinant `1`, so the Schur-complement inversion is exact.

Determinantal formulas index `h` and `e` by integers, with `h_m = e_m = 0` for `m < 0`;
`TauCeti.hsymmInt` and `TauCeti.esymmInt` are these integer-indexed polynomials.

## Main results

* `TauCeti.mk_hsymm_mul_mk_neg_one_pow_mul_esymm_eq_one`: the generating functions of `h` and
  signed `e` are inverse.
* `TauCeti.sum_antidiagonal_hsymm_mul_neg_one_pow_mul_esymm`: the convolution
  `∑_{r + s = m} h_r · (-1)ˢ e_s = δ_{m0}`.
* `TauCeti.sum_Icc_hsymmInt_mul_neg_one_pow_mul_esymmInt`: its integer-indexed form, summed
  over `[i, j]`.
* `TauCeti.hsymmToeplitz`, `TauCeti.esymmToeplitz`: the Toeplitz matrices `(h_{j - i})` and
  `((-1)^{j - i} e_{j - i})`.
* `TauCeti.hsymmToeplitz_mul_esymmToeplitz`: they are inverse to each other.
* `TauCeti.det_hsymmToeplitz`, `TauCeti.det_esymmToeplitz`: both matrices are upper
  unitriangular, so both have determinant `1`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  (2.6'), (2.9), and (3.5).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, §7.6.
-/

public section

open Finset

namespace TauCeti

/-- **The `h`--`e` generating functions are inverse**:
`(∑ₙ hₙ tⁿ) · (∑ₙ (-1)ⁿ eₙ tⁿ) = 1`. -/
theorem mk_hsymm_mul_mk_neg_one_pow_mul_esymm_eq_one {σ : Type*} [Fintype σ] [DecidableEq σ]
    (R : Type*) [CommRing R] :
    PowerSeries.mk (fun n => MvPolynomial.hsymm σ R n) *
        PowerSeries.mk (fun n => (-1 : MvPolynomial σ R) ^ n * MvPolynomial.esymm σ R n) = 1 := by
  rw [mk_hsymm_eq_prod_mk_pow, mk_neg_one_pow_mul_esymm_eq_prod_one_sub_X,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ =>
    powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (MvPolynomial.X i)

/-- **The `h`--`e` convolution**: `∑_{r + s = m} hᵣ · (-1)ˢ eₛ = δ_{m0}`, the coefficient form
of `TauCeti.mk_hsymm_mul_mk_neg_one_pow_mul_esymm_eq_one`. -/
theorem sum_antidiagonal_hsymm_mul_neg_one_pow_mul_esymm {σ : Type*} [Fintype σ] [DecidableEq σ]
    (R : Type*) [CommRing R] (m : ℕ) :
    ∑ p ∈ Finset.antidiagonal m,
        MvPolynomial.hsymm σ R p.1 *
          ((-1 : MvPolynomial σ R) ^ p.2 * MvPolynomial.esymm σ R p.2) =
      if m = 0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff m)
    (mk_hsymm_mul_mk_neg_one_pow_mul_esymm_eq_one (σ := σ) R)
  simpa only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_one] using h

/-- The `h`--`e` convolution summed over `range (m + 1)` rather than over an antidiagonal. -/
theorem sum_range_hsymm_mul_neg_one_pow_mul_esymm {σ : Type*} [Fintype σ] [DecidableEq σ]
    (R : Type*) [CommRing R] (m : ℕ) :
    ∑ r ∈ Finset.range (m + 1),
        MvPolynomial.hsymm σ R r *
          ((-1 : MvPolynomial σ R) ^ (m - r) * MvPolynomial.esymm σ R (m - r)) =
      if m = 0 then 1 else 0 := by
  rw [← sum_antidiagonal_hsymm_mul_neg_one_pow_mul_esymm (σ := σ) R m,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- **The integer-indexed `h`--`e` convolution**:
`∑_{k = i}^{j} h_{k - i} · (-1)^{j - k} e_{j - k} = δ_{ij}`, the sum being empty for `j < i`. -/
theorem sum_Icc_hsymmInt_mul_neg_one_pow_mul_esymmInt {σ : Type*} [Fintype σ] [DecidableEq σ]
    (R : Type*) [CommRing R] {i j : ℕ} :
    ∑ k ∈ Finset.Icc i j,
        hsymmInt σ R ((k : ℤ) - i) *
          ((-1 : MvPolynomial σ R) ^ ((j : ℤ) - k).toNat *
            esymmInt σ R ((j : ℤ) - k)) = if i = j then 1 else 0 := by
  by_cases hij : i ≤ j
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have hIcc : Finset.Icc i (i + d) = Finset.Ico i (i + d + 1) := by
      ext k
      simp
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    have hlen : i + d + 1 - i = d + 1 := by omega
    rw [hlen]
    have hif : (if i = i + d then (1 : MvPolynomial σ R) else 0) = if d = 0 then 1 else 0 := by
      by_cases hd : d = 0 <;> simp [hd]
    rw [hif, ← sum_range_hsymm_mul_neg_one_pow_mul_esymm (σ := σ) R d]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r ≤ d := by
      have := Finset.mem_range.mp hr
      omega
    have h1 : (((i + r : ℕ) : ℤ) - (i : ℕ)) = (r : ℤ) := by omega
    have h2 : (((i + d : ℕ) : ℤ) - ((i + r : ℕ) : ℤ)) = (d : ℤ) - r := by omega
    have h3 : ((d : ℤ) - (r : ℤ)).toNat = d - r := by omega
    rw [h1, h2, h3, ← Nat.cast_sub hr', hsymmInt_natCast, esymmInt_natCast]
  · have hne : i ≠ j := by omega
    rw [Finset.Icc_eq_empty hij, Finset.sum_empty, ite_eq_right hne]

/-- The `h`--`e` summand vanishes when `k` lies outside the interval `[i, j]`: either
`k < i`, so `h_{k - i} = 0`, or `j < k`, so `e_{j - k} = 0`. -/
theorem hsymmInt_sub_mul_neg_one_pow_mul_esymmInt_sub_eq_zero {σ : Type*} [Fintype σ]
    [DecidableEq σ] (R : Type*) [CommRing R] {i j k : ℕ} (hk : k < i ∨ j < k) :
    hsymmInt σ R ((k : ℤ) - i) *
      ((-1 : MvPolynomial σ R) ^ ((j : ℤ) - k).toNat * esymmInt σ R ((j : ℤ) - k)) = 0 := by
  rcases hk with hki | hkj
  · have hneg : ((k : ℤ) - (i : ℤ)) < 0 := by omega
    rw [hsymmInt_of_neg hneg, zero_mul]
  · have hneg : (((j : ℕ) : ℤ) - (k : ℤ)) < 0 := by omega
    rw [esymmInt_of_neg hneg, mul_zero, mul_zero]

section ToeplitzSemiring

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommSemiring R]

/-- The **Toeplitz matrix of complete homogeneous symmetric polynomials**
`(h_{j - i})_{0 ≤ i, j < n}`, with negative indices read as `0`. -/
noncomputable def hsymmToeplitz (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial σ R) :=
  Matrix.of fun i j => hsymmInt σ R ((j : ℤ) - i)

@[simp]
theorem hsymmToeplitz_apply (n : ℕ) (i j : Fin n) :
    hsymmToeplitz σ R n i j = hsymmInt σ R ((j : ℤ) - i) := by
  simp [hsymmToeplitz]

end ToeplitzSemiring

section Toeplitz

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R]

omit [DecidableEq σ] in
/-- The **signed Toeplitz matrix of elementary symmetric polynomials**
`((-1)^{j - i} e_{j - i})_{0 ≤ i, j < n}`, with negative indices read as `0`. -/
noncomputable def esymmToeplitz (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial σ R) :=
  Matrix.of fun i j =>
    (-1 : MvPolynomial σ R) ^ ((j : ℤ) - i).toNat * esymmInt σ R ((j : ℤ) - i)

omit [DecidableEq σ] in
@[simp]
theorem esymmToeplitz_apply (n : ℕ) (i j : Fin n) :
    esymmToeplitz σ R n i j =
      (-1 : MvPolynomial σ R) ^ ((j : ℤ) - i).toNat * esymmInt σ R ((j : ℤ) - i) := by
  simp [esymmToeplitz]

/-- The entry of `hsymmToeplitz * esymmToeplitz` at `(i, j)` is the convolution of `h` and the
signed `e` over `r + s = j - i`, which is `δ_{ij}`. -/
theorem hsymmToeplitz_mul_esymmToeplitz_apply (n : ℕ) (i j : Fin n) :
    (hsymmToeplitz σ R n * esymmToeplitz σ R n) i j = if i = j then 1 else 0 := by
  rw [Matrix.mul_apply]
  simp only [hsymmToeplitz_apply, esymmToeplitz_apply]
  rw [Fin.sum_univ_eq_sum_range (f := fun k : ℕ =>
    hsymmInt σ R ((k : ℤ) - (i : ℕ)) *
      ((-1 : MvPolynomial σ R) ^ (((j : ℕ) : ℤ) - (k : ℤ)).toNat *
        esymmInt σ R (((j : ℕ) : ℤ) - (k : ℤ))))]
  have hsub : Finset.Icc (i : ℕ) (j : ℕ) ⊆ Finset.range n := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact Finset.mem_range.mpr (lt_of_le_of_lt hk.2 j.isLt)
  rw [← Finset.sum_subset hsub ?_]
  · simpa only [Fin.ext_iff] using sum_Icc_hsymmInt_mul_neg_one_pow_mul_esymmInt (σ := σ) R
  · intro k _ hki
    rw [Finset.mem_Icc] at hki
    simp only [not_and_or, not_le] at hki
    exact hsymmInt_sub_mul_neg_one_pow_mul_esymmInt_sub_eq_zero (σ := σ) R hki

/-- **The Toeplitz matrices of `h` and signed `e` are inverse**:
`(h_{j - i}) · ((-1)^{j - i} e_{j - i}) = 1`.  This is the matrix form of the `h`--`e`
convolution `TauCeti.sum_Icc_hsymmInt_mul_neg_one_pow_mul_esymmInt`, and the input to Jacobi's
complementary-minor identity in the dual (transpose) Jacobi--Trudi formula. -/
theorem hsymmToeplitz_mul_esymmToeplitz (n : ℕ) :
    hsymmToeplitz σ R n * esymmToeplitz σ R n = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [hsymmToeplitz_mul_esymmToeplitz_apply, Matrix.one_apply]

/-- The Toeplitz matrix `(h_{j - i})` is upper unitriangular, so its determinant is `1`. -/
@[simp]
theorem det_hsymmToeplitz (n : ℕ) : (hsymmToeplitz σ R n).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (M := hsymmToeplitz σ R n) ?_]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [hsymmToeplitz_apply]
  · intro i j hij
    have h : ((j : ℤ) - i) < 0 := by
      have : (j : ℤ) < (i : ℤ) := by exact_mod_cast hij
      linarith
    rw [hsymmToeplitz_apply, hsymmInt_of_neg h]

omit [DecidableEq σ] in
/-- The signed Toeplitz matrix `((-1)^{j - i} e_{j - i})` is upper unitriangular, so its
determinant is `1`. -/
@[simp]
theorem det_esymmToeplitz (n : ℕ) : (esymmToeplitz σ R n).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (M := esymmToeplitz σ R n) ?_]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [esymmToeplitz_apply]
  · intro i j hij
    have h : ((j : ℤ) - i) < 0 := by
      have : (j : ℤ) < (i : ℤ) := by exact_mod_cast hij
      linarith
    rw [esymmToeplitz_apply, esymmInt_of_neg h, mul_zero]

end Toeplitz

end TauCeti
