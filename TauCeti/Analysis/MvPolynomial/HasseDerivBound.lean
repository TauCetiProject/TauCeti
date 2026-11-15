/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Bounds on evaluated multivariate Hasse derivatives

The Hasse derivative `∂^d (c X^μ)` is `c ∏ₛ choose (μ s) (d s) · X^(μ - d)`, so the triangle
inequality bounds the norm of `∂^d F` at a point `a` by a product-binomial-weighted sum of the
coefficient norms of `F`. This file records the resulting bound
`H ∑_{μ ∈ T} ∏ₛ choose (μ s) (d s) · A s ^ (μ s - d s)` for a polynomial supported on a finite set
`T` of exponents with coefficients of norm at most `H` on `T`, evaluated at a point with
`‖a s‖ ≤ A s`, and the bounds on the family `μ ↦ ∂^d (X^μ) (a)` over a finite set of exponents,
which is a row of a multivariate jet matrix. The one-variable bounds are in
`TauCeti/Analysis/Polynomial/HasseDerivBound.lean`.

For an absolute value `v : AbsoluteValue R ℝ`, a coarse bound in terms of a bound `B` on the
absolute values of all coefficients and partial degrees `degreeOf i P ≤ L i`,
`v((∂^d P)(a)) ≤ B ∏ᵢ (L i + 1) ∏ᵢ (2 max(v(aᵢ), 1)) ^ L i`, is
`AbsoluteValue.apply_eval_hasseDeriv_le`; the norm on a seminormed commutative ring need not be
multiplicative, and this file does not restate that bound for it.

## Main results

* `MvPolynomial.norm_eval_hasseDeriv_monomial_le`: the entry bound
  `‖∂^d (c X^μ) (a)‖ ≤ ‖c‖ ∏ₛ choose (μ s) (d s) · ‖a s‖ ^ (μ s - d s)`.
* `MvPolynomial.norm_eval_hasseDeriv_le`: for `F` supported on a finite set `T` of exponents,
  `‖∂^d F (a)‖ ≤ H ∑_{μ ∈ T} ∏ₛ choose (μ s) (d s) · A s ^ (μ s - d s)`.
* `MvPolynomial.norm_eval_hasseDeriv_monomial_one_le_sup'` and
  `MvPolynomial.sum_sq_norm_eval_hasseDeriv_monomial_one_le`: for `‖a s‖ ≤ A s` and a finite set
  `T` of exponents, the bounds on the family `μ ↦ ∂^d (X^μ) (a)`, `μ ∈ T`, in the maximum form
  consumed by row-dependent determinant bounds and the Euclidean form consumed by Hadamard's
  inequality. The row of the jet `(a, d)` of the jet matrix on `T`-supported polynomials in the
  monomial basis is this family.

## References

* L. Pottmeyer, *Diophantine Approximation*, lecture notes, version of 17 January 2022,
  Lemma 2.6.1 and (2.34), pp. 68–69, for the product of binomial coefficients in several
  variables.
-/

public section

open Finset

namespace MvPolynomial

variable {R σ : Type*} [SeminormedCommRing R] [Fintype σ]

/-- The entry bound of a multivariate jet matrix:
`‖∂^d (c X^μ) (a)‖ ≤ ‖c‖ ∏ₛ choose (μ s) (d s) · ‖a s‖ ^ (μ s - d s)`. -/
theorem norm_eval_hasseDeriv_monomial_le (d μ : σ →₀ ℕ) (c : R) (a : σ → R) :
    ‖eval a (hasseDeriv d (monomial μ c))‖ ≤
      ‖c‖ * ∏ s, ((μ s).choose (d s) : ℝ) * ‖a s‖ ^ (μ s - d s) := by
  rw [hasseDeriv_monomial, eval_monomial,
    Finsupp.prod_fintype _ _ fun s ↦ Nat.choose_zero_right (μ s),
    Finsupp.prod_fintype _ _ fun s ↦ pow_zero (a s), ← nsmul_eq_mul, smul_mul_assoc]
  simp only [Finsupp.tsub_apply]
  calc
    _ ≤ ((∏ s, (μ s).choose (d s) : ℕ) : ℝ) * ‖c * ∏ s, a s ^ (μ s - d s)‖ := norm_nsmul_le
    _ ≤ ((∏ s, (μ s).choose (d s) : ℕ) : ℝ) * (‖c‖ * ∏ s, ‖a s‖ ^ (μ s - d s)) := by
      gcongr
      exact Finset.norm_mul_prod_pow_le _ _ _ _
    _ = ‖c‖ * ∏ s, ((μ s).choose (d s) : ℝ) * ‖a s‖ ^ (μ s - d s) := by
      rw [prod_mul_distrib, Nat.cast_prod]
      ring

/-- The entry bound of a multivariate jet matrix with coefficient `1`:
`‖∂^d (X^μ) (a)‖ ≤ ∏ₛ choose (μ s) (d s) · ‖a s‖ ^ (μ s - d s)`. -/
theorem norm_eval_hasseDeriv_monomial_one_le [NormOneClass R] (d μ : σ →₀ ℕ) (a : σ → R) :
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

section Row

variable [NormOneClass R] {a : σ → R} {A : σ → ℝ}

/-- The row bound of a multivariate jet matrix in maximum form: for `‖a s‖ ≤ A s` and an exponent
`μ` in a finite set `T`, `‖∂^d (X^μ) (a)‖` is at most the maximum over `ν ∈ T` of
`∏ₛ choose (ν s) (d s) · A s ^ (ν s - d s)`. -/
theorem norm_eval_hasseDeriv_monomial_one_le_sup' (ha : ∀ s, ‖a s‖ ≤ A s) (d : σ →₀ ℕ)
    {T : Finset (σ →₀ ℕ)} {μ : σ →₀ ℕ} (hμ : μ ∈ T) :
    ‖eval a (hasseDeriv d (monomial μ (1 : R)))‖ ≤
      T.sup' ⟨μ, hμ⟩ fun ν ↦ ∏ s, ((ν s).choose (d s) : ℝ) * A s ^ (ν s - d s) :=
  (norm_eval_hasseDeriv_monomial_one_le d μ a).trans <|
    le_sup'_of_le _ hμ (by gcongr with s; exact ha s)

/-- The row bound of a multivariate jet matrix in Euclidean form: for `‖a s‖ ≤ A s` and a finite
set `T` of exponents, `∑_{μ ∈ T} ‖∂^d (X^μ) (a)‖ ^ 2` is at most
`∑_{μ ∈ T} (∏ₛ choose (μ s) (d s) · A s ^ (μ s - d s)) ^ 2`. -/
theorem sum_sq_norm_eval_hasseDeriv_monomial_one_le (ha : ∀ s, ‖a s‖ ≤ A s) (d : σ →₀ ℕ)
    (T : Finset (σ →₀ ℕ)) :
    ∑ μ ∈ T, ‖eval a (hasseDeriv d (monomial μ (1 : R)))‖ ^ 2 ≤
      ∑ μ ∈ T, (∏ s, ((μ s).choose (d s) : ℝ) * A s ^ (μ s - d s)) ^ 2 :=
  sum_le_sum fun μ _ ↦ by
    gcongr
    exact (norm_eval_hasseDeriv_monomial_one_le d μ a).trans
      (by gcongr with s; exact ha s)

end Row

end MvPolynomial
