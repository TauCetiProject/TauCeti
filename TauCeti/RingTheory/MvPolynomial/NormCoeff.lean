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

Over an ultrametric normed commutative ring with `‖1‖ = 1`, the multivariate polynomials whose
coefficients all have norm at most `1` are closed under products and powers: each coefficient of a
product is a finite sum of products of coefficients, so the ultrametric inequality bounds it by
`1`.

This is the estimate that makes substituting such polynomials into restricted power series
preserve unit-radius restrictedness and not increase the Gauss norm.

## Main results

* `TauCeti.MvPolynomial.norm_coeff_prod_pow_le_one`: a product of powers of polynomials with
  coefficients of norm at most `1` again has coefficients of norm at most `1`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.3.
-/

public section

namespace TauCeti.MvPolynomial

open _root_.MvPolynomial

variable {σ τ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

/-- Products of powers of polynomials whose coefficients have norm at most `1` again have
coefficients of norm at most `1`. -/
theorem norm_coeff_prod_pow_le_one {a : σ → MvPolynomial τ R}
    (ha : ∀ s t, ‖(a s).coeff t‖ ≤ 1) (d : σ →₀ ℕ) (t : τ →₀ ℕ) :
    ‖(d.prod fun s n ↦ a s ^ n).coeff t‖ ≤ 1 := by
  classical
  have hmul (p q : MvPolynomial τ R) (hp : ∀ t, ‖p.coeff t‖ ≤ 1) (hq : ∀ t, ‖q.coeff t‖ ≤ 1)
      (t : τ →₀ ℕ) : ‖(p * q).coeff t‖ ≤ 1 := by
    rw [coeff_mul]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ ↦
      (norm_mul_le _ _).trans <| (mul_le_mul (hp _) (hq _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
  have hone (t : τ →₀ ℕ) : ‖(1 : MvPolynomial τ R).coeff t‖ ≤ 1 := by
    rw [coeff_one]
    split_ifs <;> simp
  have hpow (s : σ) (n : ℕ) (t : τ →₀ ℕ) : ‖(a s ^ n).coeff t‖ ≤ 1 := by
    induction n generalizing t with
    | zero => simpa using hone t
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih (ha s) t
  exact Finset.prod_induction _ (fun q : MvPolynomial τ R ↦ ∀ t, ‖q.coeff t‖ ≤ 1) hmul hone
    (fun s _ ↦ hpow s _) t

end TauCeti.MvPolynomial
