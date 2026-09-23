/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.EulerProduct
public import TauCeti.NumberTheory.ModularForms.LFunction.Basic
public import TauCeti.NumberTheory.ModularForms.Newforms.Eigenform

/-!
# The Euler product of a normalized Hecke eigenform

Let `f` be a normalized full Hecke eigenform of weight `k` and nebentypus `χ` on `Γ₁(N)`: a cusp
form in `S_k(N, χ)` that is an eigenvector of `T_n` for every positive index `n`, with `a₁(f) = 1`.
Its coefficients are multiplicative and satisfy the prime-power recurrence
`a_{p^{r+2}} = a_p a_{p^{r+1}} - χ(p) p^{k-1} a_{p^r}` at every prime, with `χ(p) = 0` for `p ∣ N`
(Diamond–Shurman Proposition 5.8.5). On the half-plane `Re s > k/2 + 1` of absolute convergence,
its L-function is therefore the Euler product

`L(s, f) = ∏_p (1 - a_p p^{-s} + χ(p) p^{k-1-2s})⁻¹`.

At a prime `p ∣ N` the local factor degenerates to `(1 - a_p p^{-s})⁻¹`, so the bad primes are
included, with the eigenvalue of `U_p = T_p` as their coefficient.

## Main results

* `HeckeRing.GL2.Eigenform.LSeries_eulerProduct_hasProd`: the Euler product, as a `HasProd`.
* `HeckeRing.GL2.Eigenform.LSeries_eulerProduct_tprod`: the same, as an equality with `∏'`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.8.5 and Theorem 5.9.2.
-/

public section

open UpperHalfPlane CongruenceSubgroup

namespace HeckeRing.GL2.Eigenform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **The Euler product of a normalized Hecke eigenform.** For a full Hecke eigenform `f` of
weight `k` and nebentypus `χ` with `a₁(f) = 1`, and `Re s > k/2 + 1`,

`∏_p (1 - a_p p^{-s} + χ(p) p^{k-1-2s})⁻¹ = L(s, f)`,

the product running over all primes, with `χ` zero-extended to the primes dividing the level. -/
theorem LSeries_eulerProduct_hasProd (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦
        (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹)
      (LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s) := by
  have hsum : LSeriesSummable (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s := by
    refine LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_
    have := CuspForm.abscissaOfAbsConv_qExpansion_coeff_le f.toCuspForm
    rw [strictWidthInfty_Gamma1] at this
    exact this.trans_lt (mod_cast hs)
  have H := TauCeti.LSeries_eulerProduct_hasProd_of_recurrence
    (c := fun p ↦ (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1)) h₁
    (f.qExpansion_coeff_mul h₁) (fun p hp r ↦ f.qExpansion_coeff_prime_pow_add_two h₁ hp r) hsum
  -- `p ^ (k - 1) * p ^ (-2 s) = p ^ (k - 1 - 2 s)`
  have hpow (p : Nat.Primes) :
      (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s) = (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s) := by
    rw [sub_eq_add_neg _ (2 * s), ← neg_mul,
      Complex.cpow_add _ _ (by exact_mod_cast p.prop.ne_zero), ← Complex.cpow_intCast,
      Int.cast_sub, Int.cast_one]
  simpa only [mul_assoc, hpow] using H

/-- **The Euler product of a normalized Hecke eigenform**, as an equality with `∏'`: for a full
Hecke eigenform `f` with `a₁(f) = 1` and `Re s > k/2 + 1`,

`∏' p, (1 - a_p p^{-s} + χ(p) p^{k-1-2s})⁻¹ = L(s, f)`. -/
theorem LSeries_eulerProduct_tprod (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    ∏' p : Nat.Primes,
        (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹ =
      LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s :=
  (f.LSeries_eulerProduct_hasProd h₁ hs).tprod_eq

end HeckeRing.GL2.Eigenform
