/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.Data.Int.Progression
import Mathlib.RingTheory.Int.Basic

/-!
# Perfect powers in primitive arithmetic progressions

A `PrimitiveSolution` is a nontrivial primitive progression whose product is an integer
power with prime exponent. Its terms are nonzero. A prime at least the progression length
divides at most one term by `Int.eq_of_dvd_progressionTerm_of_length_le`, so the exponent
divides each term's valuation at that prime.

See M. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
sums*, Lemma 3.1.
-/

public section

/-- If only the factor at `i` can contribute to the valuation at a prime, that factor's
valuation is divisible by the exponent of the perfect-power product. -/
theorem Finset.dvd_padicValInt_of_prod_eq_pow {ι : Type*} {s : Finset ι} {i : ι}
    {f : ι → ℤ} {y : ℤ} {ℓ q : ℕ} (hi : i ∈ s) (hp : q.Prime)
    (hprod : ∏ j ∈ s, f j = y ^ ℓ)
    (huniq : (q : ℤ) ∣ f i → ∀ j ∈ s, (q : ℤ) ∣ f j → j = i) :
    ℓ ∣ padicValInt q (f i) := by
  classical
  by_cases hqi : (q : ℤ) ∣ f i
  · have hp' : Prime (q : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
    have hval := congrArg (emultiplicity (q : ℤ)) hprod
    rw [Finset.emultiplicity_prod hp', Finset.sum_eq_single_of_mem i hi] at hval
    · have hmul : multiplicity (q : ℤ) (f i) = multiplicity (q : ℤ) (y ^ ℓ) :=
        congrArg ENat.toNat hval
      rw [padicValInt.of_ne_one_ne_zero, hmul, multiplicity_pow hp']
      exact dvd_mul_right ..
    · exact fun j hj hji ↦ emultiplicity_eq_zero.mpr fun hqj ↦ hji (huniq hqi j hj hqj)
  · rw [padicValInt.eq_zero_of_not_dvd hqi]
    exact dvd_zero _

namespace TauCeti.ProgressionPowers

/-- A nontrivial primitive solution of the progression product equation
`∏ i < k, (n + i*d) = y^ℓ` with prime exponent `ℓ` and signed integer parameters. -/
@[mk_iff]
structure PrimitiveSolution (n d : ℤ) (k : ℕ) (y : ℤ) (ℓ : ℕ) : Prop where
  length_pos : 0 < k
  prime : ℓ.Prime
  gcd_eq_one : n.gcd d = 1
  prod_eq_pow : ∏ i ∈ Finset.range k, n.progressionTerm d i = y ^ ℓ
  mul_ne_zero : y * d ≠ 0

variable {n d y : ℤ} {k ℓ i q : ℕ}

/-- Every term of a primitive solution is nonzero. -/
theorem PrimitiveSolution.progressionTerm_ne_zero (h : PrimitiveSolution n d k y ℓ) (hi : i < k) :
    n.progressionTerm d i ≠ 0 :=
  Finset.prod_ne_zero_iff.mp (h.prod_eq_pow ▸ pow_ne_zero _ (left_ne_zero_of_mul h.mul_ne_zero))
    i (Finset.mem_range.mpr hi)

/-- At a prime at least the progression length, the full exponent divides the valuation of
each term. This also holds for a zero product, using the library's zero valuation at zero. -/
theorem dvd_padicValInt_progressionTerm (h : n.gcd d = 1)
    (hprod : ∏ j ∈ Finset.range k, n.progressionTerm d j = y ^ ℓ)
    (hp : q.Prime) (hq : k ≤ q) (hi : i < k) :
    ℓ ∣ padicValInt q (n.progressionTerm d i) :=
  Finset.dvd_padicValInt_of_prod_eq_pow (Finset.mem_range.mpr hi) hp hprod fun hqi _ hj hqj ↦
    Int.eq_of_dvd_progressionTerm_of_length_le h hq (Finset.mem_range.mp hj) hi hqj hqi

end TauCeti.ProgressionPowers
