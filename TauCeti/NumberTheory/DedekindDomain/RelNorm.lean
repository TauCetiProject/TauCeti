/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.RamificationInertia.Basic
-- Proof-only: the factorisation of an extended maximal ideal into the primes above it.
import Mathlib.RingTheory.DedekindDomain.Factorization

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
* `Ideal.relNorm_eq_of_forall_inertiaDeg_eq_one`: over a maximal ideal `p` all of whose primes
  have inertia degree one, the relative norm of each prime above `p` is `p` itself. This is the
  formula `N(P) = p ^ f(P ∣ p)` with every `f` equal to `1`, stated without the perfect-base-field
  hypothesis of Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal`, so that it applies to extensions of
  function fields in positive characteristic.
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

/-- **Over a maximal ideal all of whose primes have inertia degree one, the relative norm of each
prime above it is that maximal ideal.** This is `N(P) = p ^ f(P ∣ p)` when every `f` is `1`, with
no separability or Galois hypothesis on the extension. -/
theorem relNorm_eq_of_forall_inertiaDeg_eq_one {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (hf : ∀ Q ∈ p.primesOver B, Q.inertiaDeg A = 1) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    relNorm A P = p := by
  -- The norm of a prime `Q` over `p` is some power `p ^ s_Q` with `s_Q ≥ 1`, and applying the norm
  -- to `p B = ∏ Q ^ e_Q` gives `∑ e_Q · s_Q = n`; the fundamental identity `∑ e_Q · f_Q = n` with
  -- every `f_Q = 1` then forces every `s_Q = 1`.
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have hpt : p ≠ ⊤ := IsMaximal.ne_top inferInstance
  -- the norm of each prime over `p` is a positive power of `p`
  have hpow : ∀ Q ∈ p.primesOver B, ∃ s, 0 < s ∧ relNorm A Q = p ^ s := by
    intro Q hQ
    have := hQ.1
    have := hQ.2
    obtain ⟨s, hs⟩ := exists_relNorm_eq_pow_of_isPrime Q p
    refine ⟨s, Nat.pos_of_ne_zero fun h0 ↦ hpt ?_, hs⟩
    have hle : relNorm A Q ≤ p := (relNorm_le_comap A Q).trans_eq (over_def Q p).symm
    rw [hs, h0, pow_zero, one_eq_top] at hle
    exact top_le_iff.mp hle
  choose! s hs_pos hs using hpow
  -- norming `p B = ∏ Q ^ e_Q` gives `∑ s_Q · e_Q = n`
  have hsum₁ : ∑ Q ∈ (p.primesOver B).toFinset, s Q * Q.ramificationIdx A =
      Module.finrank A B := by
    have h := relNorm_algebraMap B p
    rw [map_algebraMap_eq_finsetProd_pow hp, map_prod,
      Finset.prod_congr rfl fun Q hQ ↦ by
        rw [map_pow, hs Q (Set.mem_toFinset.mp hQ), ← pow_mul],
      Finset.prod_pow_eq_pow_sum] at h
    exact (pow_right_strictAnti p hp hpt).injective h
  -- the fundamental identity with every inertia degree equal to one: `∑ 1 · e_Q = n`
  have hsum₂ : ∑ Q ∈ (p.primesOver B).toFinset, 1 * Q.ramificationIdx A =
      Module.finrank A B := by
    rw [← sum_ramification_inertia_eq_finrank p B,
      Finset.sum_set_coe (f := fun Q : Ideal B ↦ Q.ramificationIdx A * Q.inertiaDeg A)]
    exact Finset.sum_congr rfl fun Q hQ ↦ by rw [hf Q (Set.mem_toFinset.mp hQ), one_mul, mul_one]
  -- termwise comparison of the two sums pins `s_P = 1`
  have hP : P ∈ p.primesOver B := ⟨inferInstance, inferInstance⟩
  have key := (Finset.sum_eq_sum_iff_of_le fun Q hQ ↦
    Nat.mul_le_mul_right _ (hs_pos Q (Set.mem_toFinset.mp hQ))).mp (hsum₂.trans hsum₁.symm) P
    (Set.mem_toFinset.mpr hP)
  rw [hs P hP, ← Nat.eq_of_mul_eq_mul_right (ramificationIdx_pos A P) key, pow_one]

end Ideal

end
