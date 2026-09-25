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

* `HeckeRing.GL2.Eigenform.LSeries_localFactor_mul_tsum_eq_one`: the factor identity.
* `HeckeRing.GL2.Eigenform.LSeries_tsum_term_prime_pow_eq_inv`: the sum of prime-power terms.
* `HeckeRing.GL2.Eigenform.LSeries_localFactor_ne_zero`: nonvanishing of each local factor.
* `HeckeRing.GL2.Eigenform.LSeries_eulerProduct_hasProd`: the Euler product, as a `HasProd`.
* `HeckeRing.GL2.Eigenform.LSeries_eulerProduct_tprod`: the same, as an equality with `∏'`.
* `HeckeRing.GL2.Eigenform.LSeries_eulerProduct`: the same, as convergence of the finite partial
  products over `Nat.primesBelow n`.
* `HeckeRing.GL2.Eigenform.L_eulerProduct_hasProd`, `L_eulerProduct_tprod`, and
  `L_eulerProduct`: the corresponding statements for Mathlib's `ModularForm.L`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.8.5 and Theorem 5.9.2.
-/

public section

open UpperHalfPlane CongruenceSubgroup Filter Topology

namespace HeckeRing.GL2.Eigenform

variable {N : ℕ} [NeZero N] {k : ℤ}

private theorem prime_cpow_sub (p : Nat.Primes) (k : ℤ) (s : ℂ) :
    (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (-2 * s) = (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s) := by
  rw [sub_eq_add_neg _ (2 * s), ← neg_mul,
    Complex.cpow_add _ _ (by exact_mod_cast p.prop.ne_zero), ← Complex.cpow_intCast,
    Int.cast_sub, Int.cast_one]

private theorem localFactor_eq (f : Eigenform N k) (p : Nat.Primes) (s : ℂ) :
    1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
        ((MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1)) *
          (p : ℂ) ^ (-2 * s) =
      1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
        (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p *
          (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s) := by
  rw [mul_assoc, prime_cpow_sub]

/-- For a normalized full eigenform, the quadratic Euler factor times its prime-power sum is
`1` in the half-plane of absolute convergence. -/
theorem LSeries_localFactor_mul_tsum_eq_one (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (p : Nat.Primes)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
        (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p *
          (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s)) *
      (∑' e : ℕ, LSeries.term (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s (p ^ e)) = 1 := by
  have H := TauCeti.LSeries.localFactor_mul_tsum_term_prime_pow_eq_one_of_recurrence
    (c := fun q ↦ (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) q * (q : ℂ) ^ (k - 1))
    h₁ p (f.qExpansion_coeff_prime_pow_add_two h₁ p.prop)
    ((by simpa only [strictWidthInfty_Gamma1] using
      CuspForm.LSeriesSummable_qExpansion_coeff f.toCuspForm hs :
        LSeriesSummable (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s).comp_injective
      (Nat.pow_right_injective p.prop.two_le))
  simpa only [localFactor_eq] using H

/-- The prime-power sum of a normalized full eigenform is the inverse quadratic Euler factor. -/
@[simp]
theorem LSeries_tsum_term_prime_pow_eq_inv (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (p : Nat.Primes)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    ∑' e : ℕ, LSeries.term (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s (p ^ e) =
      (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
        (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p *
          (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹ :=
  eq_inv_of_mul_eq_one_right (f.LSeries_localFactor_mul_tsum_eq_one h₁ p hs)

/-- The quadratic Euler factor of a normalized full eigenform does not vanish where its
L-series converges absolutely. -/
theorem LSeries_localFactor_ne_zero (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (p : Nat.Primes)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
      (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p *
        (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s) ≠ 0 :=
  left_ne_zero_of_mul_eq_one (f.LSeries_localFactor_mul_tsum_eq_one h₁ p hs)

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
  have H := TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence
    (c := fun p ↦ (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1)) h₁
    (fun _ _ hmn ↦ f.qExpansion_coeff_mul h₁ hmn)
    (fun p hp r ↦ f.qExpansion_coeff_prime_pow_add_two h₁ hp r)
    (by simpa only [strictWidthInfty_Gamma1] using
      CuspForm.LSeriesSummable_qExpansion_coeff f.toCuspForm hs)
  simpa only [localFactor_eq] using H

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

/-- **The Euler product of a normalized Hecke eigenform**, as convergence of the finite partial
products: for a full Hecke eigenform `f` with `a₁(f) = 1` and `Re s > k/2 + 1`,

`∏_{p < n} (1 - a_p p^{-s} + χ(p) p^{k-1-2s})⁻¹ → L(s, f)` as `n → ∞`. -/
theorem LSeries_eulerProduct (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ n.primesBelow,
        (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹)
      atTop (𝓝 (LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s)) := by
  refine (TauCeti.LSeries.LSeries_eulerProduct_of_recurrence
    (c := fun p ↦ (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ (k - 1)) h₁
    (fun _ _ hmn ↦ f.qExpansion_coeff_mul h₁ hmn)
    (fun p hp r ↦ f.qExpansion_coeff_prime_pow_add_two h₁ hp r)
    (by simpa only [strictWidthInfty_Gamma1] using
      CuspForm.LSeriesSummable_qExpansion_coeff f.toCuspForm hs)).congr fun n ↦
    Finset.prod_congr rfl fun p hp ↦ ?_
  rw [localFactor_eq f ⟨p, Nat.prime_of_mem_primesBelow hp⟩ s]

/-- The Euler product of a positive-weight normalized full eigenform, expressed using
Mathlib's modular-form L-function. -/
theorem L_eulerProduct_hasProd (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (hk : 0 < k)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦
        (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹)
      (ModularForm.L hk f.toCuspForm s) := by
  have hL : LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s =
      ModularForm.L hk f.toCuspForm s := by
    simpa [strictWidthInfty_Gamma1] using
      CuspForm.LSeries_qExpansion_coeff_eq hk f.toCuspForm hs
  have H := f.LSeries_eulerProduct_hasProd h₁ hs
  rwa [hL] at H

/-- The Euler product of a positive-weight normalized full eigenform, as a `tprod`
identity for Mathlib's modular-form L-function. -/
theorem L_eulerProduct_tprod (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (hk : 0 < k)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    ∏' p : Nat.Primes,
        (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹ =
      ModularForm.L hk f.toCuspForm s :=
  (f.L_eulerProduct_hasProd h₁ hk hs).tprod_eq

/-- The finite Euler products of a positive-weight normalized full eigenform converge to
Mathlib's modular-form L-function. -/
theorem L_eulerProduct (f : Eigenform N k)
    (h₁ : (qExpansion 1 f.toCuspForm).coeff 1 = 1) (hk : 0 < k)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ n.primesBelow,
        (1 - (qExpansion 1 f.toCuspForm).coeff p * (p : ℂ) ^ (-s) +
          (MulChar.ofUnitHom f.χ : DirichletCharacter ℂ N) p * (p : ℂ) ^ ((k : ℂ) - 1 - 2 * s))⁻¹)
      atTop (𝓝 (ModularForm.L hk f.toCuspForm s)) := by
  have hL : LSeries (fun n ↦ (qExpansion 1 f.toCuspForm).coeff n) s =
      ModularForm.L hk f.toCuspForm s := by
    simpa [strictWidthInfty_Gamma1] using
      CuspForm.LSeries_qExpansion_coeff_eq hk f.toCuspForm hs
  have H := f.LSeries_eulerProduct h₁ hs
  rwa [hL] at H

end HeckeRing.GL2.Eigenform
