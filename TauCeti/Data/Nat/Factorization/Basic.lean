/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Removing prime-power factors

The least prime belongs to the prime factors of a natural number greater than one, and removing
its full multiplicity gives a smaller number. Removing the `p`-part erases `p` from the prime
factors. These facts support induction by successively removing prime-power blocks. For a
divisor `n ∣ m`, the `p`-free parts are related by `m / n * ordCompl[p] n =
ordCompl[p] m * p ^ (v_p(m) - v_p(n))`, which is how a power map `x ↦ x ^ (m / n)` between groups
of roots of unity acts on their `p`-primary parts. For a prime `p`, a divisor of `p * k` with the
same `p`-free part as `k` either divides `k` or is `p * k`. The product of any set of prime
factors of `n` divides `n`, and for `n ≠ 0` a number is coprime to the product of all the prime
factors of `n` exactly when it is coprime to `n`. Monomial products of an injective family of
primes (or fixed positive powers of their casts in characteristic zero) are injective on finitely
supported exponent tuples.
-/

public section

namespace Nat

/-- For `1 < n` the least prime factor of `n` is one of its primes. -/
theorem minFac_mem_primeFactors {n : ℕ} (hn : 1 < n) : n.minFac ∈ n.primeFactors :=
  Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hn.ne', n.minFac_dvd, by omega⟩

/-- The product of a set of prime factors of `n` divides `n`. -/
theorem prod_dvd_of_subset_primeFactors {n : ℕ} {s : Finset ℕ} (h : s ⊆ n.primeFactors) :
    ∏ p ∈ s, p ∣ n :=
  (Finset.prod_dvd_prod_of_subset _ _ id h).trans (prod_primeFactors_dvd n)

/-- **Coprimality only sees the prime factors.** For nonzero `L`, a number is coprime to the
product of the prime factors of `L` exactly when it is coprime to `L`.

This restates `coprime_prod_primeFactors_iff_coprime` of AINTLIB's `LeanModularForms` project
(`StrongMultiplicityOne.lean`, <https://github.com/CBirkbeck/AINTLIB>, commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0), proved from
`Nat.dvd_prod_primeFactors_pow_self` instead of by contradiction on a common prime divisor. -/
@[simp]
theorem coprime_prod_primeFactors_right_iff {n L : ℕ} (hL : L ≠ 0) :
    Coprime n (∏ p ∈ L.primeFactors, p) ↔ Coprime n L :=
  ⟨fun h ↦ (h.pow_right L).coprime_dvd_right (dvd_prod_primeFactors_pow_self hL),
    fun h ↦ h.coprime_dvd_right (prod_primeFactors_dvd L)⟩

/-- **Coprimality only sees the prime factors.** For nonzero `L`, the product of the prime factors
of `L` is coprime to a number exactly when `L` is. -/
@[simp]
theorem coprime_prod_primeFactors_left_iff {n L : ℕ} (hL : L ≠ 0) :
    Coprime (∏ p ∈ L.primeFactors, p) n ↔ Coprime L n := by
  rw [coprime_comm, coprime_prod_primeFactors_right_iff hL, coprime_comm]

/-- Peeling the block at the least prime factor makes `n` strictly smaller. -/
theorem ordCompl_minFac_lt {n : ℕ} (hn : 1 < n) : ordCompl[n.minFac] n < n :=
  Nat.div_lt_self (by omega) (Nat.one_lt_pow
    ((Nat.minFac_prime hn.ne').factorization_pos_of_dvd (by omega) n.minFac_dvd).ne'
    (Nat.minFac_prime hn.ne').one_lt)

/-- Removing the `p`-part of a natural number removes `p` from its prime factors. -/
@[simp]
theorem primeFactors_ordCompl (n p : ℕ) :
    (ordCompl[p] n).primeFactors = n.primeFactors.erase p := by
  rw [← support_factorization, factorization_ordCompl, Finsupp.support_erase,
    support_factorization]

/-- For a divisor `n ∣ m`, the cofactor `m / n` times the `p`-free part of `n` is the `p`-free
part of `m` times the power of `p` by which the `p`-parts of `m` and `n` differ. -/
theorem div_mul_ordCompl_of_dvd {m n : ℕ} (p : ℕ) (h : n ∣ m) :
    m / n * ordCompl[p] n = ordCompl[p] m * p ^ (m.factorization p - n.factorization p) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hn : n ≠ 0 := ne_zero_of_dvd_ne_zero hm h
  have hle : n.factorization p ≤ m.factorization p := (factorization_le_iff_dvd hn hm).2 h p
  refine Nat.eq_of_mul_eq_mul_right (ordProj_pos n p) ?_
  rw [mul_assoc, mul_comm (ordCompl[p] n), ordProj_mul_ordCompl_eq_self, Nat.div_mul_cancel h,
    mul_assoc, ← pow_add, Nat.sub_add_cancel hle, mul_comm, ordProj_mul_ordCompl_eq_self]

/-- For a prime `p`, a divisor `d` of `p * k` with the same `p`-free part as `k` that does not
divide `k` is `p * k`. -/
theorem Prime.eq_mul_of_dvd_mul_of_not_dvd_of_ordCompl_eq {p d k : ℕ} (hp : p.Prime)
    (hd : d ∣ p * k) (hdk : ¬d ∣ k) (h : ordCompl[p] d = ordCompl[p] k) : d = p * k := by
  have hk : k ≠ 0 := by
    rintro rfl
    exact hdk (dvd_zero d)
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (mul_ne_zero hp.ne_zero hk) hd
  have hpk : (p * k).factorization p = k.factorization p + 1 := by
    simp [factorization_mul hp.ne_zero hk, hp.factorization_self, add_comm]
  have hle : d.factorization p ≤ k.factorization p + 1 :=
    hpk ▸ (factorization_le_iff_dvd hd0 (mul_ne_zero hp.ne_zero hk)).2 hd p
  -- If the `p`-part of `d` were at most that of `k`, then `d` would divide `k`.
  have hlt : k.factorization p < d.factorization p := by
    by_contra hge
    refine hdk ?_
    rw [← ordProj_mul_ordCompl_eq_self d p, ← ordProj_mul_ordCompl_eq_self k p, h]
    exact mul_dvd_mul_right (Nat.pow_dvd_pow p (not_lt.1 hge)) _
  rw [← ordProj_mul_ordCompl_eq_self d p, h, ← ordProj_mul_ordCompl_eq_self (p * k) p,
    ordCompl_mul, hpk, show d.factorization p = k.factorization p + 1 by omega]
  simp [hp.factorization_self, Nat.div_self hp.pos]

end Nat

namespace TauCeti

/-- Monomial products of an injective family of prime natural numbers are injective on finitely
supported exponent tuples. -/
theorem finsuppProd_prime_pow_injective {ι : Type*} {p : ι → ℕ}
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p) :
    Function.Injective fun d : ι →₀ ℕ ↦ d.prod fun i k ↦ p i ^ k := by
  classical
  intro d₁ d₂ h
  have hmap (d : ι →₀ ℕ) : (d.prod fun i k ↦ p i ^ k).factorization = d.mapDomain p := by
    rw [← Finsupp.prod_mapDomain_index_inj hinj]
    exact Nat.factorization_prod_pow_eq_self fun q hq ↦ by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hq)
      exact hp i
  exact Finsupp.mapDomain_injective hinj
    ((hmap d₁).symm.trans ((congrArg Nat.factorization h).trans (hmap d₂)))

/-- In a characteristic-zero commutative semiring `R`, monomial products of fixed positive powers
`(p i : R) ^ m` (`m ≠ 0`) of an injective family of primes are injective on finitely supported
exponent tuples. -/
theorem finsuppProd_natCast_prime_pow_injective {R ι : Type*} [CommSemiring R] [CharZero R]
    {p : ι → ℕ} (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p) {m : ℕ}
    (hm : m ≠ 0) :
    Function.Injective fun d : ι →₀ ℕ ↦ d.prod fun i k ↦ ((p i : R) ^ m) ^ k := by
  have hcast (d : ι →₀ ℕ) :
      (d.prod fun i k ↦ ((p i : R) ^ m) ^ k) =
        (((d.mapRange (m * ·) (mul_zero m)).prod fun i k ↦ p i ^ k : ℕ) : R) := by
    have hhom := map_finsuppProd (Nat.castRingHom R) d fun i k ↦ p i ^ (m * k)
    simp only [Nat.coe_castRingHom] at hhom
    rw [Finsupp.prod_mapRange_index (fun _ ↦ rfl), hhom]
    exact Finsupp.prod_congr fun i _ ↦ by simp [pow_mul]
  intro d₁ d₂ h
  have hmap := finsuppProd_prime_pow_injective hp hinj
    (Nat.cast_injective ((hcast d₁).symm.trans (h.trans (hcast d₂))))
  ext i
  exact mul_left_cancel₀ hm (DFunLike.congr_fun hmap i)

end TauCeti
