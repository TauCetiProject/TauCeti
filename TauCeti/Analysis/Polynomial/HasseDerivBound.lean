/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic

/-!
# Bounds on evaluated Hasse derivatives

The `k`-th Hasse derivative of `f = ∑ⱼ cⱼ Xʲ` at a point `a` is
`∑ⱼ cⱼ · choose j k · a ^ (j - k)`, so the triangle inequality bounds its norm by the
binomial-weighted sum of the coefficient norms. This file records that bound, its form for a
polynomial of degree at most `d` with coefficients of norm at most `H` evaluated at a point of
norm at most `A`, the coarser bound `H (d + 1) 2 ^ d max(1, A) ^ d`, the analogous product-binomial
bound for multivariate polynomials supported on a finite set of exponents, and the resulting row
bounds of jet matrices, whose entries are evaluated Hasse derivatives of monomials.

The length form `‖D^[k] f (a)‖ ≤ 2 ^ natDegree f ‖f‖₁ max(1, ‖a‖) ^ natDegree f` is the composite
of `Polynomial.norm_eval_le_l1Norm_mul`, `Polynomial.l1Norm_hasseDeriv_le` and
`Polynomial.natDegree_hasseDeriv_le`, and the multivariate coarse bound is
`AbsoluteValue.apply_eval_hasseDeriv_le`; neither is restated here.

## Main results

* `Polynomial.norm_hasseDeriv_monomial_eval_le`: the entry bound
  `‖D^[k] (c Xʲ) (a)‖ ≤ ‖c‖ · choose j k · ‖a‖ ^ (j - k)` of a jet matrix.
* `Polynomial.norm_hasseDeriv_eval_le_sum_support`: the coefficient-weighted `ℓ¹` bound
  `‖D^[k] f (a)‖ ≤ ∑_{j ∈ supp f} ‖cⱼ‖ · choose j k · ‖a‖ ^ (j - k)`.
* `Polynomial.norm_hasseDeriv_eval_le`: for `natDegree f ≤ d`, `‖cⱼ‖ ≤ H` and `‖a‖ ≤ A`,
  `‖D^[k] f (a)‖ ≤ H ∑_{j = k}^{d} choose j k · A ^ (j - k)`.
* `Nat.sum_Icc_choose_mul_pow_le`: `∑_{j = k}^{d} choose j k · A ^ (j - k) ≤
  (d + 1) 2 ^ d max(1, A) ^ d` for `0 ≤ A`, and `Polynomial.norm_hasseDeriv_eval_le_coarse`, the
  resulting coarse bound.
* `MvPolynomial.norm_eval_hasseDeriv_le`: for `F` supported on a finite set `T` of exponents,
  `‖∂^d F (a)‖ ≤ H ∑_{μ ∈ T} ∏ₛ choose (μ s) (d s) · A s ^ (μ s - d s)`.
* `MvPolynomial.norm_jet_entry_le_sup'` and `MvPolynomial.sum_sq_norm_jet_entry_le`: the row
  bounds of a matrix whose entry in row `r` and column `c` is `∂^(d r) (X ^ μ c)` evaluated at the
  node `a r`, in the maximum form consumed by row-dependent determinant bounds and the Euclidean
  form consumed by Hadamard's inequality; `Polynomial.norm_jet_entry_le_sup'` and
  `Polynomial.sum_sq_norm_jet_entry_le` are the univariate forms, for confluent Vandermonde
  matrices.

## References

* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, p. 282, for `E^k X^n = choose n k X^(n - k)`.
* A. Prasolov, *Polynomials*, Lemma 2.6.1 and (2.34), pp. 68–69, for the product of binomial
  coefficients in several variables.
-/

public section

open Finset

/-- The binomial-weighted power sum `∑_{j = k}^{d} choose j k · A ^ (j - k)` is at most
`(d + 1) 2 ^ d max(1, A) ^ d` when `0 ≤ A`. -/
theorem Nat.sum_Icc_choose_mul_pow_le (k d : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    ∑ j ∈ Icc k d, (j.choose k : ℝ) * A ^ (j - k) ≤ (d + 1) * 2 ^ d * max 1 A ^ d := by
  calc
    ∑ j ∈ Icc k d, (j.choose k : ℝ) * A ^ (j - k) ≤ ∑ _j ∈ Icc k d, 2 ^ d * max 1 A ^ d := by
      gcongr with j hj
      · exact_mod_cast (j.choose_le_two_pow k).trans
          (Nat.pow_le_pow_right two_pos (mem_Icc.1 hj).2)
      · exact (pow_le_pow_left₀ hA (le_max_right 1 A) _).trans
          (pow_le_pow_right₀ (le_max_left 1 A) (by grind))
    _ ≤ (d + 1) * 2 ^ d * max 1 A ^ d := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc, mul_assoc]
      gcongr
      exact_mod_cast Nat.sub_le _ _

namespace Polynomial

variable {R : Type*} [SeminormedRing R] [NormOneClass R]

/-- The entry bound of a jet matrix: `‖D^[k] (c Xʲ) (a)‖ ≤ ‖c‖ · choose j k · ‖a‖ ^ (j - k)`. -/
theorem norm_hasseDeriv_monomial_eval_le (k j : ℕ) (c a : R) :
    ‖(hasseDeriv k (monomial j c)).eval a‖ ≤ ‖c‖ * ((j.choose k : ℝ) * ‖a‖ ^ (j - k)) := by
  rw [hasseDeriv_monomial, eval_monomial, ← nsmul_eq_mul]
  calc
    ‖(j.choose k • c) * a ^ (j - k)‖ ≤ ‖j.choose k • c‖ * ‖a‖ ^ (j - k) :=
      (norm_mul_le _ _).trans (by gcongr; exact norm_pow_le a _)
    _ ≤ ‖c‖ * ((j.choose k : ℝ) * ‖a‖ ^ (j - k)) := by
      rw [mul_left_comm, ← mul_assoc]
      gcongr
      exact norm_nsmul_le

/-- The entry bound of a confluent Vandermonde matrix:
`‖D^[k] (Xʲ) (a)‖ ≤ choose j k · ‖a‖ ^ (j - k)`. -/
theorem norm_hasseDeriv_X_pow_eval_le (k j : ℕ) (a : R) :
    ‖(hasseDeriv k (X ^ j : R[X])).eval a‖ ≤ (j.choose k : ℝ) * ‖a‖ ^ (j - k) := by
  simpa [← monomial_one_right_eq_X_pow] using norm_hasseDeriv_monomial_eval_le k j (1 : R) a

/-- The evaluated Hasse derivative is bounded by the binomial-weighted sum of the coefficient
norms over any finite set containing the support. -/
theorem norm_hasseDeriv_eval_le_sum_of_support_subset (k : ℕ) {f : R[X]} {s : Finset ℕ}
    (hs : f.support ⊆ s) (a : R) :
    ‖(hasseDeriv k f).eval a‖ ≤ ∑ j ∈ s, ‖f.coeff j‖ * ((j.choose k : ℝ) * ‖a‖ ^ (j - k)) := by
  have hf : f = ∑ j ∈ s, monomial j (f.coeff j) := f.as_sum_support.trans <|
    sum_subset hs fun j _ hj ↦ by rw [notMem_support_iff.1 hj, map_zero]
  conv_lhs => rw [hf, map_sum, eval_finsetSum]
  exact (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ norm_hasseDeriv_monomial_eval_le k j _ a)

/-- The evaluated Hasse derivative is bounded by the binomial-weighted sum of the coefficient
norms: `‖D^[k] f (a)‖ ≤ ∑_{j ∈ supp f} ‖cⱼ‖ · choose j k · ‖a‖ ^ (j - k)`. -/
theorem norm_hasseDeriv_eval_le_sum_support (k : ℕ) (f : R[X]) (a : R) :
    ‖(hasseDeriv k f).eval a‖ ≤
      ∑ j ∈ f.support, ‖f.coeff j‖ * ((j.choose k : ℝ) * ‖a‖ ^ (j - k)) :=
  norm_hasseDeriv_eval_le_sum_of_support_subset k subset_rfl a

/-- **The evaluated Hasse derivative bound**: for `natDegree f ≤ d`, coefficients of norm at most
`H` and `‖a‖ ≤ A`, `‖D^[k] f (a)‖ ≤ H ∑_{j = k}^{d} choose j k · A ^ (j - k)`. For `k > d` the
sum is empty and the left side is `0`. -/
theorem norm_hasseDeriv_eval_le {f : R[X]} {d : ℕ} (hd : f.natDegree ≤ d) {H : ℝ}
    (hcoeff : ∀ j ≤ d, ‖f.coeff j‖ ≤ H) {a : R} {A : ℝ} (ha : ‖a‖ ≤ A) (k : ℕ) :
    ‖(hasseDeriv k f).eval a‖ ≤ H * ∑ j ∈ Icc k d, (j.choose k : ℝ) * A ^ (j - k) := by
  have hs : f.support ⊆ range (d + 1) := fun j hj ↦
    mem_range.2 (Nat.lt_succ_of_le ((le_natDegree_of_mem_supp j hj).trans hd))
  refine (norm_hasseDeriv_eval_le_sum_of_support_subset k hs a).trans ?_
  rw [mul_sum, ← sum_subset (s₁ := Icc k d) (fun j hj ↦ mem_range.2 (by grind)) fun j hj hj' ↦ by
    rw [Nat.choose_eq_zero_of_lt (by grind)]; simp]
  refine sum_le_sum fun j hj ↦ ?_
  have hj : j ≤ d := (mem_Icc.1 hj).2
  gcongr
  · exact (norm_nonneg _).trans (hcoeff j hj)
  · exact hcoeff j hj

/-- The coarse evaluated Hasse derivative bound: for `natDegree f ≤ d`, coefficients of norm at
most `H` and `‖a‖ ≤ A`, `‖D^[k] f (a)‖ ≤ H (d + 1) 2 ^ d max(1, A) ^ d`. -/
theorem norm_hasseDeriv_eval_le_coarse {f : R[X]} {d : ℕ} (hd : f.natDegree ≤ d) {H : ℝ}
    (hcoeff : ∀ j ≤ d, ‖f.coeff j‖ ≤ H) {a : R} {A : ℝ} (ha : ‖a‖ ≤ A) (k : ℕ) :
    ‖(hasseDeriv k f).eval a‖ ≤ H * ((d + 1) * 2 ^ d * max 1 A ^ d) :=
  (norm_hasseDeriv_eval_le hd hcoeff ha k).trans <| mul_le_mul_of_nonneg_left
    (Nat.sum_Icc_choose_mul_pow_le k d ((norm_nonneg a).trans ha))
    ((norm_nonneg _).trans (hcoeff 0 d.zero_le))

/-- The row bound of a univariate jet matrix in maximum form: if the entry in row `r` and column
`c` is `D^[k r] (X ^ e c)` at the node `a r`, with `‖a r‖ ≤ A r`, then every entry of row `r` is
at most the maximum over the columns of `choose (e c) (k r) · A r ^ (e c - k r)`. -/
theorem norm_jet_entry_le_sup' {ρ κ : Type*} [Fintype κ] [Nonempty κ] {M : ρ → κ → R}
    {a : ρ → R} {k : ρ → ℕ} {e : κ → ℕ}
    (hM : ∀ r c, M r c = (hasseDeriv (k r) (X ^ e c)).eval (a r))
    {A : ρ → ℝ} (hA : ∀ r, ‖a r‖ ≤ A r) (r : ρ) (c : κ) :
    ‖M r c‖ ≤ univ.sup' univ_nonempty fun c' ↦ ((e c').choose (k r) : ℝ) * A r ^ (e c' - k r) := by
  rw [hM]
  refine (norm_hasseDeriv_X_pow_eval_le _ _ _).trans <| le_sup'_of_le _ (mem_univ c) ?_
  gcongr
  exact hA r

/-- The row bound of a univariate jet matrix in Euclidean form: if the entry in row `r` and
column `c` is `D^[k r] (X ^ e c)` at the node `a r`, with `‖a r‖ ≤ A r`, then the squared
Euclidean length of row `r` is at most `∑_c (choose (e c) (k r) · A r ^ (e c - k r)) ^ 2`. -/
theorem sum_sq_norm_jet_entry_le {ρ κ : Type*} [Fintype κ] {M : ρ → κ → R}
    {a : ρ → R} {k : ρ → ℕ} {e : κ → ℕ}
    (hM : ∀ r c, M r c = (hasseDeriv (k r) (X ^ e c)).eval (a r))
    {A : ρ → ℝ} (hA : ∀ r, ‖a r‖ ≤ A r) (r : ρ) :
    ∑ c, ‖M r c‖ ^ 2 ≤ ∑ c, (((e c).choose (k r) : ℝ) * A r ^ (e c - k r)) ^ 2 := by
  refine sum_le_sum fun c _ ↦ ?_
  rw [hM]
  gcongr
  refine (norm_hasseDeriv_X_pow_eval_le _ _ _).trans ?_
  gcongr
  exact hA r

end Polynomial

namespace MvPolynomial

variable {R σ : Type*} [NormedCommRing R] [NormOneClass R] [Fintype σ]

/-- The entry bound of a multivariate jet matrix:
`‖∂^d (c X^μ) (a)‖ ≤ ‖c‖ ∏ₛ choose (μ s) (d s) · ‖a s‖ ^ (μ s - d s)`. -/
theorem norm_eval_hasseDeriv_monomial_le (d μ : σ →₀ ℕ) (c : R) (a : σ → R) :
    ‖eval a (hasseDeriv d (monomial μ c))‖ ≤
      ‖c‖ * ∏ s, ((μ s).choose (d s) : ℝ) * ‖a s‖ ^ (μ s - d s) := by
  rw [hasseDeriv_monomial, eval_monomial,
    Finsupp.prod_fintype _ _ fun s ↦ Nat.choose_zero_right (μ s),
    Finsupp.prod_fintype _ _ fun s ↦ pow_zero (a s), Nat.cast_prod, prod_mul_distrib]
  calc
    ‖(∏ s, ((μ s).choose (d s) : R)) * c * ∏ s, a s ^ ((μ - d) s)‖ ≤
        (∏ s, ‖((μ s).choose (d s) : R)‖) * ‖c‖ * ∏ s, ‖a s ^ ((μ - d) s)‖ :=
      (norm_mul_le _ _).trans <| mul_le_mul ((norm_mul_le _ _).trans <|
        mul_le_mul_of_nonneg_right (Finset.norm_prod_le _ _) (norm_nonneg _))
        (Finset.norm_prod_le _ _) (norm_nonneg _) (by positivity)
    _ ≤ ‖c‖ * ((∏ s, ((μ s).choose (d s) : ℝ)) * ∏ s, ‖a s‖ ^ (μ s - d s)) := by
      rw [mul_comm _ ‖c‖, mul_assoc]
      gcongr with s
      · rw [← nsmul_one]
        exact norm_nsmul_le.trans (by simp)
      · exact norm_pow_le _ _

/-- **The multivariate evaluated Hasse derivative bound**: for `F` supported on a finite set `T`
of exponents, with coefficients of norm at most `H` on `T`, and a point with `‖a s‖ ≤ A s`,
`‖∂^d F (a)‖ ≤ H ∑_{μ ∈ T} ∏ₛ choose (μ s) (d s) · A s ^ (μ s - d s)`. -/
theorem norm_eval_hasseDeriv_le {T : Finset (σ →₀ ℕ)} {F : MvPolynomial σ R}
    (hF : F ∈ restrictSupport R (T : Set (σ →₀ ℕ))) {H : ℝ} (hcoeff : ∀ μ ∈ T, ‖F.coeff μ‖ ≤ H)
    {a : σ → R} {A : σ → ℝ} (ha : ∀ s, ‖a s‖ ≤ A s) (d : σ →₀ ℕ) :
    ‖eval a (hasseDeriv d F)‖ ≤
      H * ∑ μ ∈ T, ∏ s, ((μ s).choose (d s) : ℝ) * A s ^ (μ s - d s) := by
  have hT : F.support ⊆ T := fun μ hμ ↦ (mem_restrictSupport_iff R).1 hF hμ
  have hF' : F = ∑ μ ∈ T, monomial μ (F.coeff μ) := F.as_sum.trans <|
    sum_subset hT fun μ _ hμ ↦ by rw [notMem_support_iff.1 hμ, map_zero]
  conv_lhs => rw [hF', map_sum, map_sum]
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun μ hμ ↦ ?_)
  refine (norm_eval_hasseDeriv_monomial_le d μ _ a).trans ?_
  gcongr with s
  · exact (norm_nonneg _).trans (hcoeff μ hμ)
  · exact hcoeff μ hμ
  · exact ha s

/-- The row bound of a multivariate jet matrix in maximum form: if the entry in row `r` and
column `c` is `∂^(d r) (X ^ μ c)` at the node `a r`, with `‖a r s‖ ≤ A r s`, then every entry of
row `r` is at most the maximum over the columns of `∏ₛ choose (μ c s) (d r s) ·
A r s ^ (μ c s - d r s)`. -/
theorem norm_jet_entry_le_sup' {ρ κ : Type*} [Fintype κ] [Nonempty κ] {M : ρ → κ → R}
    {a : ρ → σ → R} {d : ρ → σ →₀ ℕ} {μ : κ → σ →₀ ℕ}
    (hM : ∀ r c, M r c = eval (a r) (hasseDeriv (d r) (monomial (μ c) 1)))
    {A : ρ → σ → ℝ} (hA : ∀ r s, ‖a r s‖ ≤ A r s) (r : ρ) (c : κ) :
    ‖M r c‖ ≤ univ.sup' univ_nonempty fun c' ↦
      ∏ s, ((μ c' s).choose (d r s) : ℝ) * A r s ^ (μ c' s - d r s) := by
  rw [hM]
  refine (norm_eval_hasseDeriv_monomial_le _ _ _ _).trans <| le_sup'_of_le _ (mem_univ c) ?_
  rw [norm_one, one_mul]
  gcongr with s
  exact hA r s

/-- The row bound of a multivariate jet matrix in Euclidean form: if the entry in row `r` and
column `c` is `∂^(d r) (X ^ μ c)` at the node `a r`, with `‖a r s‖ ≤ A r s`, then the squared
Euclidean length of row `r` is at most
`∑_c (∏ₛ choose (μ c s) (d r s) · A r s ^ (μ c s - d r s)) ^ 2`. -/
theorem sum_sq_norm_jet_entry_le {ρ κ : Type*} [Fintype κ] {M : ρ → κ → R}
    {a : ρ → σ → R} {d : ρ → σ →₀ ℕ} {μ : κ → σ →₀ ℕ}
    (hM : ∀ r c, M r c = eval (a r) (hasseDeriv (d r) (monomial (μ c) 1)))
    {A : ρ → σ → ℝ} (hA : ∀ r s, ‖a r s‖ ≤ A r s) (r : ρ) :
    ∑ c, ‖M r c‖ ^ 2 ≤
      ∑ c, (∏ s, ((μ c s).choose (d r s) : ℝ) * A r s ^ (μ c s - d r s)) ^ 2 := by
  refine sum_le_sum fun c _ ↦ ?_
  rw [hM]
  gcongr
  refine (norm_eval_hasseDeriv_monomial_le _ _ _ _).trans ?_
  rw [norm_one, one_mul]
  gcongr with s
  exact hA r s

end MvPolynomial
