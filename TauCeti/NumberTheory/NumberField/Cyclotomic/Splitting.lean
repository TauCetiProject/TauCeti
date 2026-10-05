/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import TauCeti.NumberTheory.Cyclotomic.OddLevel
import TauCeti.Data.Nat.Totient
import TauCeti.NumberTheory.NumberField.PrimeIdeal

/-!
# The splitting law in cyclotomic fields

Let `K` be an `n`-th cyclotomic field over `ℚ`, let `p` be a rational prime, and write
`n = p ^ k * m` with `p ∤ m`. The **cyclotomic splitting law** says that

`p 𝓞 K = (P₁ ⋯ P_g) ^ φ(p ^ k)`,

where the `Pᵢ` are distinct primes, each of residue degree `f`, the multiplicative order of `p`
modulo `m`, and `g = φ(m) / f`. Mathlib computes the ramification index and residue degree
(`IsCyclotomicExtension.Rat.ramificationIdxIn_eq` and `IsCyclotomicExtension.Rat.inertiaDegIn_eq`)
in separate statements for `k = 0` and for `k > 0`. This file states them uniformly in `k`, counts
the primes above `p`, and factors `p 𝓞 K`.

Two classical criteria follow. Their statements depend on the residue of `n` modulo `4`, because an
`n`-th cyclotomic field with `n ≡ 2 mod 4` is also an `n / 2`-th cyclotomic field, and the splitting
of `p` is governed by the odd level `n / 2`. For `n ≢ 2 mod 4`:

* `p` splits completely in `K` iff `p ≡ 1 mod n`;
* `p` is inert in `K` iff `p ∤ n` and `p` generates `(ZMod n)ˣ`.

Neither criterion holds at levels `n ≡ 2 mod 4` as stated: in `ℚ(ζ₆) = ℚ(ζ₃)` the prime `2` is
inert although `2 ∣ 6`, and in `ℚ(ζ₂) = ℚ` the prime `2` splits completely although `2 ≢ 1 mod 2`.

## Main results

* `TauCeti.NumberField.ramificationIdxIn_eq_totient`: the ramification index of `p` is
  `φ(p ^ k)`.
* `TauCeti.NumberField.inertiaDegIn_eq_orderOf`: the residue degree of `p` is the order of `p`
  modulo `m`.
* `TauCeti.NumberField.ncard_primesOver_mul_orderOf_eq_totient_of_eq_pow_mul`: the number of
  primes above `p` times that order is `φ(m)`.
* `TauCeti.NumberField.span_natCast_eq_prod_primesOverFinset_pow`: `p 𝓞 K` is the product of
  the primes above `p`, raised to the power `φ(p ^ k)`.
* `TauCeti.NumberField.ncard_primesOver_eq_totient_iff`: for `n ≢ 2 mod 4`, the prime `p` splits
  completely iff `p ≡ 1 mod n`; `ncard_primesOver_eq_totient_iff_of_mod_four_eq_two` is the
  version for `n ≡ 2 mod 4`.
* `TauCeti.NumberField.isPrime_span_natCast_iff_orderOf_eq_totient`: for `n ≢ 2 mod 4`, the
  prime `p` is inert iff `p ∤ n` and `p` has order `φ(n)` modulo `n`;
  `isPrime_span_natCast_iff_orderOf_eq_totient_of_mod_four_eq_two` is the version for
  `n ≡ 2 mod 4`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Proposition 10.3.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 2.13.
-/

public section
noncomputable section

open Ideal NumberField
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

section Level

variable {n p k m : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {n} ℚ K]

/-- **The ramification index in a cyclotomic field.** If `n = p ^ k * m` with `p ∤ m`, the
ramification index of `p` in an `n`-th cyclotomic field over `ℚ` is `φ(p ^ k)`. -/
theorem ramificationIdxIn_eq_totient (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = (p ^ k).totient := by
  cases k with
  | zero =>
    rw [pow_zero, one_mul] at hn
    subst hn
    have : NeZero n := ⟨by rintro rfl; exact hm (dvd_zero p)⟩
    rw [pow_zero, Nat.totient_one]
    exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hm
  | succ k =>
    rw [Nat.totient_prime_pow_succ hp.out]
    exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq n K hn hm

/-- **The residue degree in a cyclotomic field.** If `n = p ^ k * m` with `p ∤ m`, the residue
degree of `p` in an `n`-th cyclotomic field over `ℚ` is the order of `p` modulo `m`. -/
theorem inertiaDegIn_eq_orderOf (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = orderOf (p : ZMod m) := by
  cases k with
  | zero =>
    rw [pow_zero, one_mul] at hn
    subst hn
    have : NeZero n := ⟨by rintro rfl; exact hm (dvd_zero p)⟩
    exact IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hm
  | succ k => exact IsCyclotomicExtension.Rat.inertiaDegIn_eq n K hn hm

/-- **The number of primes above `p` in a cyclotomic field.** If `n = p ^ k * m` with `p ∤ m`,
the number of primes above `p` in an `n`-th cyclotomic field over `ℚ`, times the order of `p`
modulo `m`, is `φ(m)`. -/
theorem ncard_primesOver_mul_orderOf_eq_totient_of_eq_pow_mul (hn : n = p ^ k * m)
    (hm : ¬ p ∣ m) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard * orderOf (p : ZMod m) = m.totient := by
  have : NeZero m := ⟨by rintro rfl; exact hm (dvd_zero p)⟩
  have : NeZero n := ⟨hn ▸ NeZero.ne (p ^ k * m)⟩
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  have h := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [ramificationIdxIn_eq_totient hn hm, inertiaDegIn_eq_orderOf hn hm,
    IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.Rat.finrank n K, hn,
    Nat.totient_mul ((Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)))]
    at h
  refine Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.2 (pow_pos hp.out.pos k)) ?_
  rw [← h]
  ring

/-- **The splitting law in a cyclotomic field.** If `n = p ^ k * m` with `p ∤ m`, then in an
`n`-th cyclotomic field over `ℚ` the ideal `p 𝓞 K` is the product of the distinct primes above
`p`, raised to the power `φ(p ^ k)`. -/
theorem span_natCast_eq_prod_primesOverFinset_pow (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    span {(p : 𝓞 K)} =
      (∏ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K), P) ^ (p ^ k).totient := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.out.ne_zero
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)}) = span {(p : 𝓞 K)} := by
    simp [Ideal.map_span]
  rw [← hmap, Ideal.map_algebraMap_eq_finsetProd_pow hp0, ← Finset.prod_pow]
  refine Finset.prod_congr (Finset.coe_injective ?_) fun P hP ↦ ?_
  · rw [IsDedekindDomain.coe_primesOverFinset hp0, Set.coe_toFinset]
  · obtain ⟨_, _⟩ : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by
      rw [← IsDedekindDomain.coe_primesOverFinset hp0]
      exact hP
    rw [← ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) P Gal(K/ℚ),
      ramificationIdxIn_eq_totient hn hm]

/-- **The inert primes in terms of the level decomposition.** If `n = p ^ k * m` with `p ∤ m`,
then `p` is inert in an `n`-th cyclotomic field over `ℚ` iff `φ(p ^ k) = 1` and `p` has order
`φ(m)` modulo `m`. -/
private theorem isPrime_span_natCast_iff_of_eq_pow_mul (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    (span {(p : 𝓞 K)}).IsPrime ↔ (p ^ k).totient = 1 ∧ orderOf (p : ZMod m) = m.totient := by
  have : NeZero m := ⟨by rintro rfl; exact hm (dvd_zero p)⟩
  have hg := ncard_primesOver_mul_orderOf_eq_totient_of_eq_pow_mul (K := K) hn hm
  rw [isPrime_span_natCast_iff_of_eq_prod_primesOverFinset_pow
      (span_natCast_eq_prod_primesOverFinset_pow hn hm),
    and_comm]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ by rw [← hg, h, one_mul], fun h ↦ ?_⟩
  rw [h] at hg
  exact (Nat.mul_eq_right (Nat.totient_pos.2 (NeZero.pos m)).ne').1 hg

/-- **Complete splitting in a cyclotomic field.** If `n ≢ 2 mod 4`, a prime `p` splits completely
in an `n`-th cyclotomic field over `ℚ` (there are `φ(n) = [K : ℚ]` primes above it) iff
`p ≡ 1 mod n`. -/
theorem ncard_primesOver_eq_totient_iff [NeZero n] (hn4 : n % 4 ≠ 2) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = n.totient ↔ (p : ZMod n) = 1 := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne n) p hp.out.ne_one
  have : NeZero m := ⟨by rintro rfl; exact hm (dvd_zero p)⟩
  have hg := ncard_primesOver_mul_orderOf_eq_totient_of_eq_pow_mul (K := K) hn hm
  have hm0 := Nat.totient_pos.2 (NeZero.pos m)
  constructor
  · intro h
    rw [h, hn, Nat.totient_mul (Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)), mul_assoc] at hg
    have h1 : (p ^ k).totient * orderOf (p : ZMod m) = 1 := by
      refine Nat.eq_of_mul_eq_mul_left hm0 ?_
      calc m.totient * ((p ^ k).totient * orderOf (p : ZMod m))
          = (p ^ k).totient * (m.totient * orderOf (p : ZMod m)) := by ring
        _ = m.totient * 1 := by rw [hg, mul_one]
    obtain rfl : k = 0 := by
      refine ((Nat.totient_prime_pow_eq_one_iff hp.out).1
        (Nat.eq_one_of_mul_eq_one_right h1)).resolve_right ?_
      rintro ⟨rfl, rfl⟩
      obtain ⟨j, rfl⟩ : Odd m := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hm)
      omega
    rw [pow_zero, one_mul] at hn
    subst hn
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_mul_eq_one_left h1)
  · intro h
    obtain rfl : k = 0 := by
      by_contra hk
      have hpn : p ∣ n := hn ▸ Dvd.dvd.mul_right (dvd_pow_self p hk) m
      have := congrArg (ZMod.castHom hpn (ZMod p)) h
      rw [map_natCast, map_one, ZMod.natCast_self] at this
      exact zero_ne_one this
    rw [pow_zero, one_mul] at hn
    subst hn
    rw [h, orderOf_one, mul_one] at hg
    exact hg

/-- **Inert primes in a cyclotomic field.** If `n ≢ 2 mod 4`, a prime `p` is inert in an `n`-th
cyclotomic field over `ℚ` (that is, `p 𝓞 K` is prime) iff `p ∤ n` and `p` generates `(ZMod n)ˣ`,
in the form that the order of `p` modulo `n` is `φ(n)`. -/
theorem isPrime_span_natCast_iff_orderOf_eq_totient [NeZero n] (hn4 : n % 4 ≠ 2) :
    (span {(p : 𝓞 K)}).IsPrime ↔ ¬ p ∣ n ∧ orderOf (p : ZMod n) = n.totient := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne n) p hp.out.ne_one
  rw [isPrime_span_natCast_iff_of_eq_pow_mul hn hm, Nat.totient_prime_pow_eq_one_iff hp.out]
  constructor
  · rintro ⟨rfl | ⟨rfl, rfl⟩, h⟩
    · rw [pow_zero, one_mul] at hn
      exact hn ▸ ⟨hm, h⟩
    · obtain ⟨j, rfl⟩ : Odd m := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hm)
      omega
  · rintro ⟨hpn, h⟩
    obtain rfl : k = 0 := by
      by_contra hk
      exact hpn (hn ▸ Dvd.dvd.mul_right (dvd_pow_self p hk) m)
    rw [pow_zero, one_mul] at hn
    exact ⟨Or.inl rfl, hn ▸ h⟩

end Level

section ModFourEqTwo

variable {n p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {n} ℚ K]

/-- **Complete splitting at a level `≡ 2 mod 4`.** If `n ≡ 2 mod 4`, a prime `p` splits completely
in an `n`-th cyclotomic field over `ℚ` iff `p ≡ 1 mod n / 2`: the field is also an `n / 2`-th
cyclotomic field. -/
theorem ncard_primesOver_eq_totient_iff_of_mod_four_eq_two (hn4 : n % 4 = 2) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = n.totient ↔ (p : ZMod (n / 2)) = 1 := by
  have : IsCyclotomicExtension {n / 2} ℚ K :=
    IsCyclotomicExtension.singleton_div_two_of_mod_four_eq_two hn4 two_ne_zero
  have : NeZero (n / 2) := ⟨by omega⟩
  have hn : n = 2 * (n / 2) := by omega
  rw [hn, Nat.totient_two_mul_of_odd (Nat.odd_iff.2 (by omega)), ← hn]
  exact ncard_primesOver_eq_totient_iff (by omega)

/-- **Inert primes at a level `≡ 2 mod 4`.** If `n ≡ 2 mod 4`, a prime `p` is inert in an `n`-th
cyclotomic field over `ℚ` iff `p ∤ n / 2` and the order of `p` modulo `n / 2` is `φ(n / 2)`: the
field is also an `n / 2`-th cyclotomic field. -/
theorem isPrime_span_natCast_iff_orderOf_eq_totient_of_mod_four_eq_two (hn4 : n % 4 = 2) :
    (span {(p : 𝓞 K)}).IsPrime ↔ ¬ p ∣ n / 2 ∧ orderOf (p : ZMod (n / 2)) = (n / 2).totient := by
  have : IsCyclotomicExtension {n / 2} ℚ K :=
    IsCyclotomicExtension.singleton_div_two_of_mod_four_eq_two hn4 two_ne_zero
  have : NeZero (n / 2) := ⟨by omega⟩
  exact isPrime_span_natCast_iff_orderOf_eq_totient (by omega)

end ModFourEqTwo

/-- **The number of primes above an unramified prime.** For a rational prime `p` not dividing `m`,
the number of primes above `p` in an `m`-th cyclotomic field over `ℚ`, times the order of `p`
modulo `m`, is `φ(m)`. -/
theorem ncard_primesOver_mul_orderOf_eq_totient {m : ℕ} [IsCyclotomicExtension {m} ℚ K] (p : ℕ)
    [Fact p.Prime] (hm : ¬ p ∣ m) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard * orderOf (p : ZMod m) = Nat.totient m :=
  ncard_primesOver_mul_orderOf_eq_totient_of_eq_pow_mul (k := 0) (by rw [pow_zero, one_mul]) hm

end TauCeti.NumberField

end
