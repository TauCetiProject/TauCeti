/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting

import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Indexing the prime-power ideals by a prime and an exponent

Every prime-power ideal of `𝓞 K` is `𝔭 ^ (k + 1)` for a unique height-one prime `𝔭` and a unique
`k : ℕ`. This file records that bijection and what it does to an infinite sum: a sum over the
prime-power ideals is the iterated sum over primes and exponents, and a sum over *all* nonzero
ideals collapses to the same thing whenever the summand is supported on prime powers.

This is the ideal analogue of Mathlib's `Nat.Primes.prodNatEquiv` and the two summation lemmas
built on it, `tsum_primes_pow_eq` and `tsum_eq_tsum_primes_of_support_subset_prime_powers`. Those
are what turns an Euler-product logarithm, which is naturally indexed by `(𝔭, k)`, into a Dirichlet
series indexed by ideals — the shape a von Mangoldt coefficient identity needs.

## Main definitions

* `TauCeti.idealPrimePowerOf`: the prime-power ideal `𝔭 ^ (k + 1)`.
* `TauCeti.idealPrimePowerEquiv`: the bijection `(𝔭, k) ↦ 𝔭 ^ (k + 1)` onto the prime-power ideals.

## Main results

* `TauCeti.tsum_idealPrimePower_eq`: an absolutely convergent sum over the prime-power ideals is
  the iterated sum over primes and exponents.
* `TauCeti.tsum_eq_tsum_idealPrimePower_of_support_subset`: a summable family on the nonzero
  ideals supported on prime powers has the same sum as that iterated sum.

## Implementation notes

The inverse sends `A` to `(primePowerBase A, primePowerExponent A - 1)`. The truncated subtraction
is harmless because `primePowerExponent A` is positive, and the `+ 1` in the forward map is what
keeps the exponent positive without carrying a hypothesis.
-/

public section

open scoped nonZeroDivisors NumberField
open IsDedekindDomain NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- The prime-power ideal `𝔭 ^ (k + 1)`. -/
@[expose] def idealPrimePowerOf (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) : IdealPrimePower K :=
  ⟨⟨P.asIdeal ^ (k + 1), pow_mem (mem_nonZeroDivisors_of_ne_zero P.ne_bot) _⟩,
    ⟨P.asIdeal, k + 1, Ideal.prime_of_isPrime P.ne_bot P.isPrime, k.succ_pos, rfl⟩⟩

@[simp]
theorem coe_idealPrimePowerOf (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    ((idealPrimePowerOf P k : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = P.asIdeal ^ (k + 1) :=
  rfl

@[simp]
theorem primePowerBase_idealPrimePowerOf (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    primePowerBase (idealPrimePowerOf P k) = P :=
  HeightOneSpectrum.ext
    (primePowerBase_asIdeal_eq (Ideal.prime_of_isPrime P.ne_bot P.isPrime) rfl)

@[simp]
theorem primePowerExponent_idealPrimePowerOf (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    primePowerExponent (idealPrimePowerOf P k) = k + 1 :=
  primePowerExponent_eq (Ideal.prime_of_isPrime P.ne_bot P.isPrime) rfl

/-- **A prime-power ideal is a prime and an exponent.** The bijection `(𝔭, k) ↦ 𝔭 ^ (k + 1)` from
height-one primes and natural numbers onto the prime-power ideals of `𝓞 K`.

This is the ideal analogue of `Nat.Primes.prodNatEquiv`. -/
@[expose] noncomputable def idealPrimePowerEquiv :
    HeightOneSpectrum (𝓞 K) × ℕ ≃ IdealPrimePower K where
  toFun Pk := idealPrimePowerOf Pk.1 Pk.2
  invFun A := (primePowerBase A, primePowerExponent A - 1)
  left_inv := by
    rintro ⟨P, k⟩
    simp
  right_inv A := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [coe_idealPrimePowerOf, Nat.sub_add_cancel (primePowerExponent_pos A)]
    exact primePowerBase_pow_primePowerExponent A

@[simp]
theorem idealPrimePowerEquiv_apply (P : HeightOneSpectrum (𝓞 K)) (k : ℕ) :
    idealPrimePowerEquiv (P, k) = idealPrimePowerOf P k :=
  rfl

variable {α : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α] [CompleteSpace α]
  [T0Space α] {f : (Ideal (𝓞 K))⁰ → α}

/-- **Summing over prime-power ideals is summing over primes and exponents.** -/
theorem tsum_idealPrimePower_eq (hf : Summable fun A : IdealPrimePower K ↦ f A.1) :
    ∑' (P : HeightOneSpectrum (𝓞 K)) (k : ℕ), f (idealPrimePowerOf P k : (Ideal (𝓞 K))⁰)
      = ∑' A : IdealPrimePower K, f A.1 := calc
  _ = ∑' Pk : HeightOneSpectrum (𝓞 K) × ℕ, f (idealPrimePowerEquiv Pk : (Ideal (𝓞 K))⁰) := by
    simpa using (hf.comp_injective idealPrimePowerEquiv.injective).tsum_prod.symm
  _ = _ := by rw [← Equiv.tsum_eq idealPrimePowerEquiv]

/-- **A sum supported on prime powers is a sum over primes and exponents.** -/
theorem tsum_eq_tsum_idealPrimePower_of_support_subset (hfm : Summable f)
    (hf : Function.support f ⊆ {A : (Ideal (𝓞 K))⁰ | IsPrimePow (A : Ideal (𝓞 K))}) :
    ∑' A : (Ideal (𝓞 K))⁰, f A
      = ∑' (P : HeightOneSpectrum (𝓞 K)) (k : ℕ),
          f (idealPrimePowerOf P k : (Ideal (𝓞 K))⁰) := by
  rw [tsum_idealPrimePower_eq (hfm.subtype _)]
  exact (tsum_subtype_eq_of_support_subset hf).symm

end TauCeti
