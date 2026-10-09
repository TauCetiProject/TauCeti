/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Polynomials with coefficients in the closed unit ball

Over an ultrametric seminormed commutative ring with `‖1‖ ≤ 1`, the multivariate polynomials whose
coefficients all have norm at most `1` are closed under products and powers: each coefficient of a
product is a finite sum of products of coefficients, so the ultrametric inequality bounds it by
`1`.

This is the estimate that makes substituting such polynomials into restricted power series
preserve unit-radius restrictedness and not increase the Gauss norm.

## Main results

* `MvPolynomial.norm_coeff_mul_le` and `MvPolynomial.norm_coeff_pow_le`: uniform coefficient
  bounds multiply under multiplication and exponentiate under powers.
* `TauCeti.MvPolynomial.norm_coeff_prod_pow_le_one`: a product of powers again has coefficients
  of norm at most `1`, assuming the bounds only for factors in the exponent's support.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.3.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]

/-- A uniform coefficient bound for a product is the product of uniform coefficient bounds
for its factors. -/
theorem norm_coeff_mul_le (p q : MvPolynomial σ R) {r s : ℝ}
    (hp : ∀ t, ‖p.coeff t‖ ≤ r) (hq : ∀ t, ‖q.coeff t‖ ≤ s) (t : σ →₀ ℕ) :
    ‖(p * q).coeff t‖ ≤ r * s := by
  classical
  rw [coeff_mul]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg ((norm_nonneg _).trans (hp 0)) ((norm_nonneg _).trans (hq 0)))
    fun x _ ↦ norm_mul_le_of_le (hp x.1) (hq x.2)

/-- Raising a polynomial to a power raises its uniform coefficient bound to the same power,
provided `‖1‖ ≤ 1`. -/
theorem norm_coeff_pow_le (p : MvPolynomial σ R) (h1 : ‖(1 : R)‖ ≤ 1) {r : ℝ}
    (hp : ∀ t, ‖p.coeff t‖ ≤ r) (n : ℕ) (t : σ →₀ ℕ) :
    ‖(p ^ n).coeff t‖ ≤ r ^ n := by
  classical
  induction n generalizing t with
  | zero =>
    rw [pow_zero, coeff_one]
    split_ifs <;> simp [h1]
  | succ n ih =>
    rw [pow_succ]
    simpa only [pow_succ] using norm_coeff_mul_le _ _ ih hp t

end MvPolynomial

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial

variable {σ τ R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]

/-- Products of powers of polynomials whose coefficients have norm at most `1` again have
coefficients of norm at most `1`, provided `‖1‖ ≤ 1`. Only the factors in the exponent's support
need coefficient bounds. -/
theorem norm_coeff_prod_pow_le_one (h1 : ‖(1 : R)‖ ≤ 1) {a : σ → MvPolynomial τ R}
    (d : σ →₀ ℕ) (ha : ∀ s ∈ d.support, ∀ t, ‖(a s).coeff t‖ ≤ 1) (t : τ →₀ ℕ) :
    ‖(d.prod fun s n ↦ a s ^ n).coeff t‖ ≤ 1 := by
  classical
  have hone (t : τ →₀ ℕ) : ‖(1 : MvPolynomial τ R).coeff t‖ ≤ 1 := by
    rw [coeff_one]
    split_ifs <;> simp [h1]
  exact Finset.prod_induction _ (fun q : MvPolynomial τ R ↦ ∀ t, ‖q.coeff t‖ ≤ 1)
    (fun p q hp hq t ↦ by simpa only [one_mul] using norm_coeff_mul_le p q hp hq t) hone
    (fun s hs t ↦ by simpa only [one_pow] using norm_coeff_pow_le (a s) h1 (ha s hs) _ t) t

end TauCeti.MvPolynomial
