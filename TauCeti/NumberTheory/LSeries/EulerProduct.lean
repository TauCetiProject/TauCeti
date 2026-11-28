/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.Topology.Algebra.InfiniteSum.LinearRecurrence
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Nat.Prime.Int

/-!
# Euler products with quadratic local factors

Let `a : ℕ → ℂ` be multiplicative on coprime arguments with `a 1 = 1`, and suppose that along the
powers of every prime `p` its values obey the second-order recurrence

`a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r)`.

Wherever the L-series of `a` converges absolutely, it is then the Euler product

`L(a, s) = ∏_p (1 - a p * p ^ (-s) + c p * p ^ (-2 s))⁻¹`.

At each prime, the quadratic factor times the sum of the prime-power terms is `1`. Thus each
factor is nonzero, and its inverse is the local contribution to the Euler product.

This is the shape of the L-function of a normalized Hecke eigenform, where `c p = χ(p) p^(k-1)`
(Diamond–Shurman, Theorem 5.9.2), and it covers the completely multiplicative case `c = 0`.

Restricting `a` to the indices prime to a modulus `Q` keeps the recurrence, with `c` restricted
in the same way, so its L-series is the Euler product over the primes `p ∤ Q`; for `Q ≠ 0` it is
`L(a, s)` times the finitely many quadratic factors at the primes `p ∣ Q`.

Where the L-series converges absolutely and no local factor vanishes, `L(a, s) ≠ 0`: the Euler
product is then an absolutely convergent product of nonzero factors. Under the recurrence the
local factors never vanish, so the L-series is nonzero throughout its region of absolute
convergence.

## Main results

* `TauCeti.LSeries.localFactor_mul_tsum_term_prime_pow_eq_one_of_recurrence`: the factor
  identity.
* `TauCeti.LSeries.tsum_term_prime_pow_eq_inv_of_recurrence`: the prime-power sum is the
  inverse factor.
* `TauCeti.LSeries.localFactor_ne_zero_of_recurrence`: each quadratic factor is nonzero.
* `TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence`: the Euler product, as a
  `HasProd`.
* `TauCeti.LSeries.LSeries_eulerProduct_tprod_of_recurrence`: the same, as an equality with
  `∏'`.
* `TauCeti.LSeries.LSeries_eulerProduct_of_recurrence`: the same, as convergence of the finite
  partial products over `Nat.primesBelow n`.
* `TauCeti.LSeries.LSeries_coprime_eulerProduct_hasProd_of_recurrence`: the Euler product of
  the coefficients prime to a modulus `Q`, over the primes `p ∤ Q`.
* `TauCeti.LSeries.LSeries_coprime_eq_mul_prod_of_recurrence`: for `Q ≠ 0`, the L-series of
  the coefficients prime to `Q` is `L(a, s)` times the quadratic factors at the primes `p ∣ Q`.
* `TauCeti.LSeries.LSeries_ne_zero_of_tsum_term_prime_pow_ne_zero`: for a multiplicative `a` with
  absolutely convergent L-series, `L(a, s) ≠ 0` as soon as no local factor vanishes.
* `TauCeti.LSeries.LSeries_ne_zero_of_recurrence`: under the recurrence, `L(a, s) ≠ 0` wherever
  the L-series converges absolutely.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  §5.9.
-/

public section

open LSeries Nat Filter Topology

namespace TauCeti.LSeries

variable {a c : ℕ → ℂ} {s : ℂ}

/-- An L-series term at a power of a nonzero index, written as a coefficient times a power of
the index's Dirichlet weight. -/
theorem term_pow (p : ℕ) (hp : p ≠ 0) (e : ℕ) :
    term a s (p ^ e) = a (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
  rw [term_of_ne_zero (pow_ne_zero e hp), cast_pow,
    ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul, Complex.cpow_neg, inv_pow,
    div_eq_mul_inv]

/-- The quadratic factor times the sum over powers of a prime is `1` whenever the
prime-power coefficients satisfy the second-order recurrence. -/
theorem localFactor_mul_tsum_term_prime_pow_eq_one_of_recurrence (h₁ : a 1 = 1) (p : Primes)
    (hrec : ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : Summable (fun e : ℕ ↦ term a s (p ^ e))) :
    (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s)) *
      (∑' e : ℕ, term a s (p ^ e)) = 1 := by
  have hterm (e : ℕ) := term_pow (a := a) (s := s) p p.prop.ne_zero e
  have key := hs.hasSum
    |>.one_sub_add_mul_eq_of_linearRec₂ (D := a p * (p : ℂ) ^ (-s))
      (S := c p * ((p : ℂ) ^ (-s)) ^ 2) fun r ↦ by
        simp only [hterm, hrec r]; ring
  rw [hterm 0, hterm 1] at key
  -- Convert the exponent to a natural multiple before applying `Complex.cpow_nat_mul`.
  have hexponent : -2 * s = (2 : ℕ) * -s := by push_cast; ring
  rw [hexponent, Complex.cpow_nat_mul]
  exact key.trans (by simp [h₁])

/-- The sum over powers of a prime is the inverse quadratic Euler factor. -/
theorem tsum_term_prime_pow_eq_inv_of_recurrence (h₁ : a 1 = 1) (p : Primes)
    (hrec : ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : Summable (fun e : ℕ ↦ term a s (p ^ e))) :
    ∑' e : ℕ, term a s (p ^ e) =
      (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s))⁻¹ :=
  eq_inv_of_mul_eq_one_right
    (localFactor_mul_tsum_term_prime_pow_eq_one_of_recurrence h₁ p hrec hs)

/-- Each quadratic Euler factor is nonzero when its prime-power series converges. -/
theorem localFactor_ne_zero_of_recurrence (h₁ : a 1 = 1) (p : Primes)
    (hrec : ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : Summable (fun e : ℕ ↦ term a s (p ^ e))) :
    1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s) ≠ 0 :=
  left_ne_zero_of_mul_eq_one
    (localFactor_mul_tsum_term_prime_pow_eq_one_of_recurrence h₁ p hrec hs)

/-- The L-series terms of a coefficient sequence multiplicative on nonzero coprime arguments
are themselves multiplicative on coprime arguments. -/
theorem term_mul_of_coprime
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → a (m * n) = a m * a n)
    {m n : ℕ} (hmn : m.Coprime n) : term a s (m * n) = term a s m * term a s n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero (mul_ne_zero hm hn), term_of_ne_zero hm, term_of_ne_zero hn,
    hmul hm hn hmn,
    cast_mul, Complex.natCast_mul_cpow, mul_div_mul_comm]

/-- **The Euler product with quadratic local factors.** Let `a : ℕ → ℂ` satisfy `a 1 = 1`, be
multiplicative on nonzero coprime arguments, and obey the recurrence
`a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r)` along the powers of every prime `p`.
Where its L-series converges absolutely,

`∏_p (1 - a p * p ^ (-s) + c p * p ^ (-2 s))⁻¹ = L(a, s)`. -/
theorem LSeries_eulerProduct_hasProd_of_recurrence (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : LSeriesSummable a s) :
    HasProd (fun p : Primes ↦ (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s))⁻¹)
      (LSeries a s) := by
  have hlocal (p : Primes) : ∑' e : ℕ, term a s (p ^ e) =
      (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s))⁻¹ := by
    exact tsum_term_prime_pow_eq_inv_of_recurrence h₁ p (hrec p p.prop)
      (hs.comp_injective (Nat.pow_right_injective p.prop.two_le))
  have H := EulerProduct.eulerProduct_hasProd (by simp [h₁])
    (term_mul_of_coprime hmul) hs.norm (term_zero a s)
  rwa [funext hlocal] at H

/-- **The Euler product with quadratic local factors**, as an equality with `∏'`: under the
hypotheses of `TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence`,
`∏' p, (1 - a p * p ^ (-s) + c p * p ^ (-2 s))⁻¹ = L(a, s)`. -/
theorem LSeries_eulerProduct_tprod_of_recurrence (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : LSeriesSummable a s) :
    ∏' p : Primes, (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s))⁻¹ = LSeries a s :=
  (LSeries_eulerProduct_hasProd_of_recurrence h₁ hmul hrec hs).tprod_eq

/-- **The Euler product with quadratic local factors**, as convergence of the finite partial
products: under the hypotheses of `TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence`,
`∏_{p < n} (1 - a p * p ^ (-s) + c p * p ^ (-2 s))⁻¹ → L(a, s)` as `n → ∞`. -/
theorem LSeries_eulerProduct_of_recurrence (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : LSeriesSummable a s) :
    Tendsto (fun n : ℕ ↦
        ∏ p ∈ primesBelow n, (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s))⁻¹)
      atTop (𝓝 (LSeries a s)) := by
  refine (EulerProduct.eulerProduct (by simp [h₁]) (term_mul_of_coprime hmul) hs.norm
    (term_zero a s)).congr fun n ↦ Finset.prod_congr rfl fun p hp ↦ ?_
  have hp := prime_of_mem_primesBelow hp
  exact tsum_term_prime_pow_eq_inv_of_recurrence (p := ⟨p, hp⟩) h₁ (hrec p hp)
    (hs.comp_injective (Nat.pow_right_injective hp.two_le))

/-! ### Removing the Euler factors at the primes dividing a modulus -/

/-- **The Euler product of the coefficients prime to a modulus.** Under the hypotheses of
`TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence`, the L-series of the coefficients
`a n` with `n` prime to `Q`, the others replaced by `0`, is the Euler product over the primes
`p ∤ Q` of the quadratic factors, the factors at the primes `p ∣ Q` being replaced by `1`. -/
theorem LSeries_coprime_eulerProduct_hasProd_of_recurrence (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : LSeriesSummable a s) (Q : ℕ) :
    HasProd (fun p : Primes ↦ if (p : ℕ).Coprime Q then
        (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s))⁻¹ else 1)
      (LSeries (fun n ↦ if n.Coprime Q then a n else 0) s) := by
  -- the restricted coefficients satisfy the recurrence with `c` restricted in the same way
  have H := LSeries_eulerProduct_hasProd_of_recurrence
    (a := fun n ↦ if n.Coprime Q then a n else 0) (c := fun n ↦ if n.Coprime Q then c n else 0)
    (s := s) (by simp [h₁])
    (fun {m n} hm hn hmn ↦ by
      by_cases hmQ : m.Coprime Q
      · by_cases hnQ : n.Coprime Q
        · simp only [ite_eq_left (Nat.Coprime.mul_left hmQ hnQ), ite_eq_left hmQ,
            ite_eq_left hnQ, hmul hm hn hmn]
        · simp only [ite_eq_right (mt Nat.Coprime.coprime_mul_left hnQ), ite_eq_right hnQ,
            mul_zero]
      · simp only [ite_eq_right (mt Nat.Coprime.coprime_mul_right hmQ), ite_eq_right hmQ,
          zero_mul])
    (fun p hp r ↦ by
      by_cases hpQ : p.Coprime Q
      · simp only [ite_eq_left (Nat.Coprime.pow_left _ hpQ), ite_eq_left hpQ]
        exact hrec p hp r
      · have hpow (e : ℕ) : ¬(p ^ (e + 1)).Coprime Q := by
          rwa [Nat.coprime_pow_left_iff e.succ_pos]
        simp only [ite_eq_right (hpow _), ite_eq_right hpQ, zero_mul, sub_zero])
    (Summable.of_norm_bounded hs.norm fun n ↦ ?_)
  · refine H.congr_fun fun p ↦ ?_
    by_cases hpQ : (p : ℕ).Coprime Q
    · simp only [ite_eq_left hpQ]
    · simp only [ite_eq_right hpQ, zero_mul, sub_zero, add_zero, inv_one]
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    split_ifs
    · exact le_rfl
    · rw [zero_div, norm_zero]
      exact norm_nonneg _

/-- **Removing the Euler factors at the primes dividing a modulus.** Under the hypotheses of
`TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence`, for a nonzero modulus `Q` the
L-series of the coefficients prime to `Q` is the L-series of `a` times the quadratic factors at
the primes dividing `Q`:

`L(a · 1_{(n, Q) = 1}, s) = L(a, s) ∏_{p ∣ Q} (1 - a p * p ^ (-s) + c p * p ^ (-2 s))`. -/
theorem LSeries_coprime_eq_mul_prod_of_recurrence (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : LSeriesSummable a s) {Q : ℕ} (hQ : Q ≠ 0) :
    LSeries (fun n ↦ if n.Coprime Q then a n else 0) s =
      LSeries a s *
        ∏ p ∈ Q.primeFactors, (1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s)) := by
  set E : ℕ → ℂ := fun p ↦ 1 - a p * (p : ℂ) ^ (-s) + c p * (p : ℂ) ^ (-2 * s)
  -- the factors at the primes dividing `Q`, as a finitely supported family over the primes
  have hT (p : Primes) : p ∈ Q.primeFactors.preimage (fun p : Primes ↦ (p : ℕ))
      Subtype.val_injective.injOn ↔ ¬(p : ℕ).Coprime Q := by
    refine Finset.mem_preimage.trans ?_
    rw [Nat.mem_primeFactors_of_ne_zero hQ, Nat.Prime.coprime_iff_not_dvd p.prop, not_not]
    exact and_iff_right p.prop
  have hfin : HasProd (fun p : Primes ↦ if (p : ℕ).Coprime Q then 1 else E p)
      (∏ p ∈ Q.primeFactors, E p) := by
    have H := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional Primes)
      (s := Q.primeFactors.preimage (fun p : Primes ↦ (p : ℕ)) Subtype.val_injective.injOn)
      (f := fun p : Primes ↦ if (p : ℕ).Coprime Q then 1 else E p) fun p hp ↦
        ite_eq_left (not_not.mp (mt (hT p).mpr hp))
    convert H using 1
    symm
    refine Finset.prod_bij (fun p _ ↦ (p : ℕ)) (fun p hp ↦ Finset.mem_preimage.mp hp)
      (fun p _ q _ h ↦ Subtype.ext h) (fun p hp ↦ ⟨⟨p, Nat.prime_of_mem_primeFactors hp⟩,
        Finset.mem_preimage.mpr hp, rfl⟩) fun p hp ↦ ite_eq_right ((hT p).mp hp)
  have H := (LSeries_eulerProduct_hasProd_of_recurrence h₁ hmul hrec hs).mul hfin
  refine (LSeries_coprime_eulerProduct_hasProd_of_recurrence h₁ hmul hrec hs Q).unique
    (H.congr_fun fun p ↦ ?_)
  by_cases hpQ : (p : ℕ).Coprime Q
  · rw [ite_eq_left hpQ, ite_eq_left hpQ, mul_one]
  · rw [ite_eq_right hpQ, ite_eq_right hpQ]
    exact (inv_mul_cancel₀ (localFactor_ne_zero_of_recurrence h₁ p (hrec p p.prop)
      (hs.comp_injective (Nat.pow_right_injective p.prop.two_le)))).symm

/-! ### Nonvanishing -/

/-- **An absolutely convergent Euler product of nonzero local factors does not vanish.** Let
`a : ℕ → ℂ` satisfy `a 1 = 1`, be multiplicative on nonzero coprime arguments, and have an
absolutely convergent L-series at `s`. If no local factor `∑' e, a (p ^ e) p ^ (-e s)` vanishes,
then `L(a, s) ≠ 0`. -/
theorem LSeries_ne_zero_of_tsum_term_prime_pow_ne_zero (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → a (m * n) = a m * a n)
    (hs : LSeriesSummable a s) (hloc : ∀ p : Primes, ∑' e : ℕ, term a s (p ^ e) ≠ 0) :
    LSeries a s ≠ 0 := by
  -- A convergent product of nonzero factors may still be zero. Here the local factor at `p` is
  -- `1 + g p` with `∑_p ‖g p‖ ≤ ∑_{n ≥ 2} ‖a n n ^ (-s)‖` finite, which rules this out.
  -- The terms at the positive powers of the primes are summable, since `(p, e) ↦ p ^ (e + 1)` is
  -- injective.
  have hpow : Summable fun x : Primes × ℕ ↦ ‖term a s (x.1 ^ (x.2 + 1))‖ :=
    hs.norm.comp_injective fun x y h ↦ by
      obtain ⟨hp, he⟩ := Nat.Prime.pow_inj x.1.prop y.1.prop h
      exact Prod.ext (Subtype.ext hp) he
  -- so the local factor at `p` is `1 + g p` for a summable `g`.
  have hfactor (p : Primes) : ∑' e : ℕ, term a s (p ^ e) =
      1 + ∑' e : ℕ, term a s (p ^ (e + 1)) := by
    have hp : Summable fun e : ℕ ↦ term a s (p ^ e) :=
      hs.comp_injective (Nat.pow_right_injective p.prop.two_le)
    rw [hp.tsum_eq_zero_add]
    simp [h₁]
  have hg : Summable fun p : Primes ↦ ‖∑' e : ℕ, term a s (p ^ (e + 1))‖ :=
    hpow.prod.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun p ↦
      norm_tsum_le_tsum_norm (hpow.prod_factor p)
  have H := EulerProduct.eulerProduct_hasProd (by simp [h₁]) (term_mul_of_coprime hmul) hs.norm
    (term_zero a s)
  rw [LSeries, ← H.tprod_eq, funext hfactor]
  exact tprod_one_add_ne_zero_of_summable (fun p ↦ hfactor p ▸ hloc p) hg

/-- **An Euler product with quadratic local factors does not vanish.** Under the hypotheses of
`TauCeti.LSeries.LSeries_eulerProduct_hasProd_of_recurrence`, `L(a, s) ≠ 0` wherever the L-series
of `a` converges absolutely. -/
theorem LSeries_ne_zero_of_recurrence (h₁ : a 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - c p * a (p ^ r))
    (hs : LSeriesSummable a s) :
    LSeries a s ≠ 0 :=
  LSeries_ne_zero_of_tsum_term_prime_pow_ne_zero h₁ hmul hs fun p ↦
    right_ne_zero_of_mul_eq_one (localFactor_mul_tsum_term_prime_pow_eq_one_of_recurrence h₁ p
      (hrec p p.prop) (hs.comp_injective (Nat.pow_right_injective p.prop.two_le)))

end TauCeti.LSeries
