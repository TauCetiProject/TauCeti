/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Recovering an ideal from its relative norm

For a finite torsion-free extension `A → B` of Dedekind domains, the relative norm
`Ideal.relNorm A : Ideal B →*₀ Ideal A` is monotone but far from injective. It is, however,
injective on any chain: two nested ideals with the same relative norm are equal.

This is the step that turns a containment obtained from generators into an equality, which is how
norm computations identify an ideal. Mathlib's `Mathlib/RingTheory/Ideal/Norm/RelNorm.lean` has the
ingredients — multiplicativity, `Ideal.relNorm_eq_bot_iff` and `Ideal.relNorm_le_comap` — but not
this consequence.

## Main results

* `Ideal.eq_of_le_of_relNorm_eq`: a containment of ideals of `B` with equal relative norms over `A`
  is an equality.
* `Ideal.dvd_relNorm_iff_exists_liesOver_dvd`: a nonzero prime divides a relative norm exactly
  when a prime above it divides the original ideal.
-/

public section

namespace Ideal

variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

/-- **A containment of ideals with equal relative norms is an equality.** -/
theorem eq_of_le_of_relNorm_eq {I J : Ideal B} (hIJ : I ≤ J)
    (hnorm : relNorm A I = relNorm A J) : I = J := by
  rcases eq_or_ne J 0 with rfl | hJne
  · -- `I ≤ 0` leaves no room for `I`.
    simpa [zero_eq_bot, le_bot_iff] using hIJ
  -- `J ∣ I`, so `I = J * C`; cancelling the norms gives `relNorm C = 1`, and an ideal whose norm
  -- is the unit ideal is itself the unit ideal, its norm lying below its contraction.
  obtain ⟨C, hC⟩ := dvd_iff_le.mpr hIJ
  have hJnorm_ne : relNorm A J ≠ 0 := by
    rw [Ne, zero_eq_bot, relNorm_eq_bot_iff, ← zero_eq_bot]; exact hJne
  have hC1 : relNorm A C = 1 := by
    apply mul_left_cancel₀ hJnorm_ne
    rw [mul_one, ← map_mul (relNorm A), ← hC, hnorm]
  have hCtop : C = ⊤ := by
    have hle : (⊤ : Ideal A) ≤ comap (algebraMap A B) C := by
      rw [← one_eq_top, ← hC1]; exact relNorm_le_comap A C
    rw [eq_top_iff_one]
    have := hle (Submodule.mem_top (x := (1 : A)))
    rwa [mem_comap, map_one] at this
  rw [hC, hCtop, mul_top]

/-- **Prime divisors of a relative norm are exactly the primes lying below prime divisors.**

For a nonzero prime ideal `p` of `A` and an ideal `I` of `B`, `p` divides the relative norm of `I`
if and only if some prime ideal of `B` lying over `p` divides `I`. -/
theorem dvd_relNorm_iff_exists_liesOver_dvd {p : Ideal A} [p.IsPrime] (hp : p ≠ ⊥)
    {I : Ideal B} :
    p ∣ relNorm A I ↔ ∃ P : p.primesOver B, (P : Ideal B) ∣ I := by
  by_cases hI : I = ⊥
  · subst I
    obtain ⟨P⟩ := (inferInstance : Nonempty (p.primesOver B))
    exact ⟨fun _ ↦ ⟨P, dvd_zero _⟩, fun _ ↦ by rw [relNorm_bot]; exact dvd_zero _⟩
  have hp_prime : Prime p := prime_of_isPrime hp inferInstance
  constructor
  · intro hpdvd
    rw [← prod_normalizedFactors_eq_self hI, map_multiset_prod] at hpdvd
    obtain ⟨N, hNmem, hpN⟩ := hp_prime.exists_mem_multiset_dvd hpdvd
    obtain ⟨P, hPmem, rfl⟩ := Multiset.mem_map.mp hNmem
    have hPdata := (Ideal.mem_normalizedFactors_iff (A := B) hI).mp hPmem
    have hPprime : P.IsPrime := hPdata.1
    have hPdvd : P ∣ I := dvd_iff_le.mpr hPdata.2
    let _ : P.IsPrime := hPprime
    have hP0 : P ≠ ⊥ := ne_bot_of_le_ne_bot hI hPdata.2
    have hunder0 : P.under A ≠ ⊥ := by
      intro h
      have : P.LiesOver (⊥ : Ideal A) := h ▸ inferInstance
      exact hP0 (eq_bot_of_liesOver_bot A P)
    have hunder_prime : Prime (P.under A) := prime_of_isPrime hunder0 inferInstance
    obtain ⟨n, hn⟩ := exists_relNorm_eq_pow_of_isPrime P (P.under A)
    rw [hn] at hpN
    have hpunder : p ∣ P.under A := hp_prime.dvd_of_dvd_pow hpN
    have hpeq : p = P.under A := by
      rw [Prime.dvd_prime_iff_associated hp_prime hunder_prime, associated_iff_eq] at hpunder
      exact hpunder
    exact ⟨⟨P, hPprime, hpeq ▸ inferInstance⟩, hPdvd⟩
  · rintro ⟨P, hPdvd⟩
    obtain ⟨n, hn⟩ := exists_relNorm_eq_pow_of_isPrime (P : Ideal B) p
    have hn0 : n ≠ 0 := by
      intro hnzero
      have hnorm_top : relNorm A (P : Ideal B) = ⊤ := by simpa [hnzero] using hn
      have htop_le : (⊤ : Ideal A) ≤ p := by
        have hover : p = (P : Ideal B).under A := Ideal.LiesOver.over
        rw [hover]
        exact hnorm_top ▸ relNorm_le_comap A (P : Ideal B)
      exact (inferInstance : p.IsPrime).ne_top (top_unique htop_le)
    exact (hn ▸ dvd_pow_self p hn0).trans (map_dvd (relNorm A) hPdvd)

end Ideal

end
