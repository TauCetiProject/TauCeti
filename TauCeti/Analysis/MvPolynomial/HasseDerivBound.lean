/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic

/-!
# Bounds on evaluated multivariate Hasse derivatives

The Hasse derivative `∂^d (c X^μ)` is `c ∏ₛ choose (μ s) (d s) · X^(μ - d)`, so the triangle
inequality bounds the norm of `∂^d F` at a point `a` by a product-binomial-weighted sum of the
coefficient norms of `F`. This file records that bound for a polynomial supported on a finite set
of exponents, and the resulting entry and row bounds of multivariate jet matrices, whose entries
are evaluated Hasse derivatives of monomials. The one-variable bounds are in
`TauCeti/Analysis/Polynomial/HasseDerivBound.lean`.

For an absolute value `v : AbsoluteValue R ℝ`, a coarse bound in terms of the coefficient length
is `AbsoluteValue.apply_eval_hasseDeriv_le`; the norm on a normed commutative ring need not be
multiplicative, and this file does not restate that bound for it.

## Main results

* `MvPolynomial.norm_eval_hasseDeriv_monomial_le`: the entry bound
  `‖∂^d (c X^μ) (a)‖ ≤ ‖c‖ ∏ₛ choose (μ s) (d s) · ‖a s‖ ^ (μ s - d s)`.
* `MvPolynomial.norm_eval_hasseDeriv_le`: for `F` supported on a finite set `T` of exponents,
  `‖∂^d F (a)‖ ≤ H ∑_{μ ∈ T} ∏ₛ choose (μ s) (d s) · A s ^ (μ s - d s)`.
* `MvPolynomial.norm_jet_entry_le`: the bound on one entry of a matrix whose entry in row `r` and
  column `c` is `∂^(d r) (X ^ μ c)` evaluated at the node `a r`, given a bound on the node.
* `MvPolynomial.norm_jet_entry_le_sup'` and `MvPolynomial.sum_sq_norm_jet_entry_le`: the row
  bounds of such a matrix, in the maximum form consumed by row-dependent determinant bounds and
  the Euclidean form consumed by Hadamard's inequality.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes, version of 17 January 2022,
  Lemma 2.6.1 and (2.34), pp. 68–69, for the product of binomial coefficients in several
  variables.
-/

public section

open Finset

namespace MvPolynomial

variable {R σ : Type*} [NormedCommRing R] [NormOneClass R] [Fintype σ]

/-- The entry bound of a multivariate jet matrix:
`‖∂^d (c X^μ) (a)‖ ≤ ‖c‖ ∏ₛ choose (μ s) (d s) · ‖a s‖ ^ (μ s - d s)`. -/
theorem norm_eval_hasseDeriv_monomial_le (d μ : σ →₀ ℕ) (c : R) (a : σ → R) :
    ‖eval a (hasseDeriv d (monomial μ c))‖ ≤
      ‖c‖ * ∏ s, ((μ s).choose (d s) : ℝ) * ‖a s‖ ^ (μ s - d s) := by
  rw [hasseDeriv_monomial, eval_monomial,
    Finsupp.prod_fintype _ _ fun s ↦ Nat.choose_zero_right (μ s),
    Finsupp.prod_fintype _ _ fun s ↦ pow_zero (a s)]
  simp only [Finsupp.tsub_apply, Nat.cast_prod]
  calc
    ‖(∏ s, ((μ s).choose (d s) : R)) * c * ∏ s, a s ^ (μ s - d s)‖ ≤
        ‖∏ s, ((μ s).choose (d s) : R)‖ * ‖c‖ * ‖∏ s, a s ^ (μ s - d s)‖ :=
      norm_mul₃_le
    _ ≤ (∏ s, ‖((μ s).choose (d s) : R)‖) * ‖c‖ * ∏ s, ‖a s ^ (μ s - d s)‖ := by
      gcongr <;> exact Finset.norm_prod_le _ _
    _ ≤ (∏ s, ((μ s).choose (d s) : ℝ)) * ‖c‖ * ∏ s, ‖a s‖ ^ (μ s - d s) := by
      gcongr with s _
      · rw [← nsmul_one]
        exact norm_nsmul_le.trans (by simp)
      · exact norm_pow_le _ _
    _ = ‖c‖ * ∏ s, ((μ s).choose (d s) : ℝ) * ‖a s‖ ^ (μ s - d s) := by
      rw [prod_mul_distrib]
      ring

/-- The entry bound of a multivariate jet matrix with coefficient `1`:
`‖∂^d (X^μ) (a)‖ ≤ ∏ₛ choose (μ s) (d s) · ‖a s‖ ^ (μ s - d s)`. -/
theorem norm_eval_hasseDeriv_monomial_one_le (d μ : σ →₀ ℕ) (a : σ → R) :
    ‖eval a (hasseDeriv d (monomial μ (1 : R)))‖ ≤
      ∏ s, ((μ s).choose (d s) : ℝ) * ‖a s‖ ^ (μ s - d s) := by
  simpa using norm_eval_hasseDeriv_monomial_le d μ (1 : R) a

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

section Jet

variable {ρ κ : Type*} {M : ρ → κ → R} {a : ρ → σ → R} {d : ρ → σ →₀ ℕ} {μ : κ → σ →₀ ℕ}
  (hM : ∀ r c, M r c = eval (a r) (hasseDeriv (d r) (monomial (μ c) 1))) {A : ρ → σ → ℝ}
  (hA : ∀ r s, ‖a r s‖ ≤ A r s)
include hM hA

/-- The entry bound of a multivariate jet matrix: if the entry in row `r` and column `c` is
`∂^(d r) (X ^ μ c)` at the node `a r`, with `‖a r s‖ ≤ A r s`, then
`‖M r c‖ ≤ ∏ₛ choose (μ c s) (d r s) · A r s ^ (μ c s - d r s)`. -/
theorem norm_jet_entry_le (r : ρ) (c : κ) :
    ‖M r c‖ ≤ ∏ s, ((μ c s).choose (d r s) : ℝ) * A r s ^ (μ c s - d r s) := by
  rw [hM]
  refine (norm_eval_hasseDeriv_monomial_one_le _ _ _).trans ?_
  gcongr with s
  exact hA r s

/-- The row bound of a multivariate jet matrix in maximum form: if the entry in row `r` and
column `c` is `∂^(d r) (X ^ μ c)` at the node `a r`, with `‖a r s‖ ≤ A r s`, then every entry of
row `r` is at most the maximum over the columns of `∏ₛ choose (μ c s) (d r s) ·
A r s ^ (μ c s - d r s)`. -/
theorem norm_jet_entry_le_sup' [Fintype κ] [Nonempty κ] (r : ρ) (c : κ) :
    ‖M r c‖ ≤ univ.sup' univ_nonempty fun c' ↦
      ∏ s, ((μ c' s).choose (d r s) : ℝ) * A r s ^ (μ c' s - d r s) :=
  (norm_jet_entry_le hM hA r c).trans <| le_sup'_of_le _ (mem_univ c) le_rfl

/-- The row bound of a multivariate jet matrix in Euclidean form: if the entry in row `r` and
column `c` is `∂^(d r) (X ^ μ c)` at the node `a r`, with `‖a r s‖ ≤ A r s`, then the squared
Euclidean length of row `r` is at most
`∑_c (∏ₛ choose (μ c s) (d r s) · A r s ^ (μ c s - d r s)) ^ 2`. -/
theorem sum_sq_norm_jet_entry_le [Fintype κ] (r : ρ) :
    ∑ c, ‖M r c‖ ^ 2 ≤
      ∑ c, (∏ s, ((μ c s).choose (d r s) : ℝ) * A r s ^ (μ c s - d r s)) ^ 2 :=
  sum_le_sum fun c _ ↦ by gcongr; exact norm_jet_entry_le hM hA r c

end Jet

end MvPolynomial
