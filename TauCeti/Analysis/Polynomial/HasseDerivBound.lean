/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import TauCeti.Data.Nat.Choose.Bounds

/-!
# Bounds on evaluated Hasse derivatives

The `k`-th Hasse derivative of `f = ∑ⱼ cⱼ Xʲ` at a point `a` is
`∑ⱼ cⱼ · choose j k · a ^ (j - k)`, so the triangle inequality bounds its norm by the
binomial-weighted sum of the coefficient norms. This file records that bound, its form for a
polynomial of degree at most `d` with coefficients of norm at most `H` evaluated at a point of
norm at most `A`, the coarser bound `H (d + 1) 2 ^ d max(1, A) ^ d`, and the resulting row bounds
of confluent Vandermonde matrices, whose entries are evaluated Hasse derivatives of monomials. The
multivariate bounds are in `TauCeti/Analysis/MvPolynomial/HasseDerivBound.lean`.

The length form `‖D^[k] f (a)‖ ≤ 2 ^ natDegree f ‖f‖₁ max(1, ‖a‖) ^ natDegree f` is the composite
of `Polynomial.norm_eval_le_l1Norm_mul`, `Polynomial.l1Norm_hasseDeriv_le` and
`Polynomial.natDegree_hasseDeriv_le`, and is not restated here.

## Main results

* `Polynomial.norm_eval_hasseDeriv_monomial_le`: the entry bound
  `‖D^[k] (c Xʲ) (a)‖ ≤ ‖c‖ · choose j k · ‖a‖ ^ (j - k)` of a jet matrix.
* `Polynomial.norm_eval_hasseDeriv_le_sum_support`: the coefficient-weighted `ℓ¹` bound
  `‖D^[k] f (a)‖ ≤ ∑_{j ∈ supp f} ‖cⱼ‖ · choose j k · ‖a‖ ^ (j - k)`.
* `Polynomial.norm_eval_hasseDeriv_le`: for `natDegree f ≤ d`, `‖cⱼ‖ ≤ H` and `‖a‖ ≤ A`,
  `‖D^[k] f (a)‖ ≤ H ∑_{j = k}^{d} choose j k · A ^ (j - k)`.
* `Polynomial.norm_eval_hasseDeriv_le_coarse`: the coarse bound
  `‖D^[k] f (a)‖ ≤ H (d + 1) 2 ^ d max(1, A) ^ d`, from `Nat.sum_Icc_choose_mul_pow_le`.
* `Polynomial.norm_jet_entry_le`: the bound on one entry of a matrix whose entry in row `r` and
  column `c` is `D^[k r] (X ^ e c)` evaluated at the node `a r`, given a bound on the node.
* `Polynomial.norm_jet_entry_le_sup'` and `Polynomial.sum_sq_norm_jet_entry_le`: the row bounds of
  such a confluent Vandermonde matrix, in the maximum form consumed by row-dependent determinant
  bounds and the Euclidean form consumed by Hadamard's inequality.

## References

* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, p. 282, for `E^k X^n = choose n k X^(n - k)`.
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [SeminormedRing R] [NormOneClass R]

/-- The entry bound of a jet matrix: `‖D^[k] (c Xʲ) (a)‖ ≤ ‖c‖ · choose j k · ‖a‖ ^ (j - k)`. -/
theorem norm_eval_hasseDeriv_monomial_le (k j : ℕ) (c a : R) :
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
theorem norm_eval_hasseDeriv_X_pow_le (k j : ℕ) (a : R) :
    ‖(hasseDeriv k (X ^ j : R[X])).eval a‖ ≤ (j.choose k : ℝ) * ‖a‖ ^ (j - k) := by
  simpa [← monomial_one_right_eq_X_pow] using norm_eval_hasseDeriv_monomial_le k j (1 : R) a

/-- The evaluated Hasse derivative is bounded by the binomial-weighted sum of the coefficient
norms over any finite set containing the support. -/
theorem norm_eval_hasseDeriv_le_sum_of_support_subset (k : ℕ) {f : R[X]} {s : Finset ℕ}
    (hs : f.support ⊆ s) (a : R) :
    ‖(hasseDeriv k f).eval a‖ ≤ ∑ j ∈ s, ‖f.coeff j‖ * ((j.choose k : ℝ) * ‖a‖ ^ (j - k)) := by
  have hf : f = ∑ j ∈ s, monomial j (f.coeff j) := f.as_sum_support.trans <|
    sum_subset hs fun j _ hj ↦ by rw [notMem_support_iff.1 hj, map_zero]
  conv_lhs => rw [hf, map_sum, eval_finsetSum]
  exact (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ norm_eval_hasseDeriv_monomial_le k j _ a)

/-- The evaluated Hasse derivative is bounded by the binomial-weighted sum of the coefficient
norms: `‖D^[k] f (a)‖ ≤ ∑_{j ∈ supp f} ‖cⱼ‖ · choose j k · ‖a‖ ^ (j - k)`. -/
theorem norm_eval_hasseDeriv_le_sum_support (k : ℕ) (f : R[X]) (a : R) :
    ‖(hasseDeriv k f).eval a‖ ≤
      ∑ j ∈ f.support, ‖f.coeff j‖ * ((j.choose k : ℝ) * ‖a‖ ^ (j - k)) :=
  norm_eval_hasseDeriv_le_sum_of_support_subset k subset_rfl a

/-- **The evaluated Hasse derivative bound**: for `natDegree f ≤ d`, coefficients of norm at most
`H` and `‖a‖ ≤ A`, `‖D^[k] f (a)‖ ≤ H ∑_{j = k}^{d} choose j k · A ^ (j - k)`. For `k > d` the
sum is empty and the left side is `0`. -/
theorem norm_eval_hasseDeriv_le {f : R[X]} {d : ℕ} (hd : f.natDegree ≤ d) {H : ℝ}
    (hcoeff : ∀ j ≤ d, ‖f.coeff j‖ ≤ H) {a : R} {A : ℝ} (ha : ‖a‖ ≤ A) (k : ℕ) :
    ‖(hasseDeriv k f).eval a‖ ≤ H * ∑ j ∈ Icc k d, (j.choose k : ℝ) * A ^ (j - k) := by
  have hs : f.support ⊆ range (d + 1) := fun j hj ↦
    mem_range.2 (Nat.lt_succ_of_le ((le_natDegree_of_mem_supp j hj).trans hd))
  refine (norm_eval_hasseDeriv_le_sum_of_support_subset k hs a).trans ?_
  rw [mul_sum, ← sum_subset (s₁ := Icc k d) (fun j hj ↦ mem_range.2 (by grind)) fun j hj hj' ↦ by
    rw [Nat.choose_eq_zero_of_lt (by grind)]; simp]
  refine sum_le_sum fun j hj ↦ ?_
  have hj : j ≤ d := (mem_Icc.1 hj).2
  gcongr
  · exact (norm_nonneg _).trans (hcoeff j hj)
  · exact hcoeff j hj

/-- The coarse evaluated Hasse derivative bound: for `natDegree f ≤ d`, coefficients of norm at
most `H` and `‖a‖ ≤ A`, `‖D^[k] f (a)‖ ≤ H (d + 1) 2 ^ d max(1, A) ^ d`. -/
theorem norm_eval_hasseDeriv_le_coarse {f : R[X]} {d : ℕ} (hd : f.natDegree ≤ d) {H : ℝ}
    (hcoeff : ∀ j ≤ d, ‖f.coeff j‖ ≤ H) {a : R} {A : ℝ} (ha : ‖a‖ ≤ A) (k : ℕ) :
    ‖(hasseDeriv k f).eval a‖ ≤ H * ((d + 1) * 2 ^ d * max 1 A ^ d) :=
  (norm_eval_hasseDeriv_le hd hcoeff ha k).trans <| mul_le_mul_of_nonneg_left
    (Nat.sum_Icc_choose_mul_pow_le k d ((norm_nonneg a).trans ha))
    ((norm_nonneg _).trans (hcoeff 0 d.zero_le))

section Jet

variable {ρ κ : Type*} {M : ρ → κ → R} {a : ρ → R} {k : ρ → ℕ} {e : κ → ℕ}
  (hM : ∀ r c, M r c = (hasseDeriv (k r) (X ^ e c)).eval (a r)) {A : ρ → ℝ}
  (hA : ∀ r, ‖a r‖ ≤ A r)
include hM hA

/-- The entry bound of a univariate jet matrix: if the entry in row `r` and column `c` is
`D^[k r] (X ^ e c)` at the node `a r`, with `‖a r‖ ≤ A r`, then
`‖M r c‖ ≤ choose (e c) (k r) · A r ^ (e c - k r)`. -/
theorem norm_jet_entry_le (r : ρ) (c : κ) :
    ‖M r c‖ ≤ ((e c).choose (k r) : ℝ) * A r ^ (e c - k r) := by
  rw [hM]
  refine (norm_eval_hasseDeriv_X_pow_le _ _ _).trans ?_
  gcongr
  exact hA r

/-- The row bound of a univariate jet matrix in maximum form: if the entry in row `r` and column
`c` is `D^[k r] (X ^ e c)` at the node `a r`, with `‖a r‖ ≤ A r`, then every entry of row `r` is
at most the maximum over the columns of `choose (e c) (k r) · A r ^ (e c - k r)`. -/
theorem norm_jet_entry_le_sup' [Fintype κ] [Nonempty κ] (r : ρ) (c : κ) :
    ‖M r c‖ ≤ univ.sup' univ_nonempty fun c' ↦ ((e c').choose (k r) : ℝ) * A r ^ (e c' - k r) :=
  (norm_jet_entry_le hM hA r c).trans <| le_sup'_of_le _ (mem_univ c) le_rfl

/-- The row bound of a univariate jet matrix in Euclidean form: if the entry in row `r` and
column `c` is `D^[k r] (X ^ e c)` at the node `a r`, with `‖a r‖ ≤ A r`, then the squared
Euclidean length of row `r` is at most `∑_c (choose (e c) (k r) · A r ^ (e c - k r)) ^ 2`. -/
theorem sum_sq_norm_jet_entry_le [Fintype κ] (r : ρ) :
    ∑ c, ‖M r c‖ ^ 2 ≤ ∑ c, (((e c).choose (k r) : ℝ) * A r ^ (e c - k r)) ^ 2 :=
  sum_le_sum fun c _ ↦ by gcongr; exact norm_jet_entry_le hM hA r c

end Jet

end Polynomial
