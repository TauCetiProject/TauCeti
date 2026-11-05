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
* `Ideal.dvd_relNorm_iff_exists_liesOver_dvd`: a prime divides a relative norm exactly
  when a prime above it divides the original ideal.
* `Ideal.relNorm_eq_of_forall_inertiaDeg_eq_one`: over a prime ideal `p` all of whose primes
  have inertia degree one, the relative norm of each prime above `p` is `p` itself. This is the
  formula `N(P) = p ^ f(P ∣ p)` with every `f` equal to `1`, stated without the separability
  hypothesis of Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal`, so that it applies to inseparable
  extensions of function fields in positive characteristic.
-/

public section

namespace Ideal

variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

/-- **A containment of ideals with equal relative norms is an equality.** -/
theorem eq_of_le_of_relNorm_eq {I J : Ideal B} (hIJ : I ≤ J)
    (hnorm : relNorm A I = relNorm A J) : I = J := by
  rcases eq_or_ne J ⊥ with rfl | hJ
  · exact le_bot_iff.mp hIJ
  -- `J ∣ I`, so `I = J * C`; cancelling the norms gives `relNorm C = 1`, and an ideal whose norm
  -- is the unit ideal is itself the unit ideal, its norm lying below its contraction.
  obtain ⟨C, rfl⟩ := dvd_iff_le.mpr hIJ
  rw [map_mul, mul_eq_left₀ (by simpa using hJ), one_eq_top, ← top_le_iff] at hnorm
  rw [comap_eq_top_iff.mp (top_le_iff.mp (hnorm.trans (relNorm_le_comap A C))), mul_top]

/-- **Prime divisors of a relative norm are exactly the primes lying below prime divisors.**

For a prime ideal `p` of `A` and an ideal `I` of `B`, `p` divides the relative norm of `I` if and
only if some prime ideal of `B` lying over `p` divides `I`. -/
theorem dvd_relNorm_iff_exists_liesOver_dvd {p : Ideal A} [p.IsPrime] {I : Ideal B} :
    p ∣ relNorm A I ↔ ∃ P : p.primesOver B, (P : Ideal B) ∣ I := by
  refine ⟨fun h ↦ ?_, fun ⟨P, hPI⟩ ↦ ?_⟩
  · rcases eq_or_ne I ⊥ with rfl | hI
    · obtain ⟨P⟩ := (inferInstance : Nonempty (p.primesOver B))
      exact ⟨P, dvd_zero _⟩
    -- `p` is nonzero since `relNorm I` is, so the prime element `p` divides the norm of some prime
    -- factor `P` of `I`; that norm is a power of `P.under A`, which is maximal, so it equals `p`.
    have hp : p ≠ ⊥ := by
      rintro rfl
      rw [← zero_eq_bot, zero_dvd_iff, zero_eq_bot, relNorm_eq_bot_iff] at h
      exact hI h
    rw [← prod_normalizedFactors_eq_self hI, map_multiset_prod] at h
    obtain ⟨P, hPI, hpP⟩ := (prime_of_isPrime hp ‹_›).exists_mem_multiset_map_dvd h
    have hP := UniqueFactorizationMonoid.prime_of_normalized_factor P hPI
    have : P.IsPrime := isPrime_of_prime hP
    have : P.IsMaximal := this.isMaximal (by simpa using hP.ne_zero)
    obtain ⟨n, hn⟩ := exists_relNorm_eq_pow_of_isPrime P (P.under A)
    rw [hn, dvd_iff_le] at hpP
    have hPp : P.under A = p := IsMaximal.eq_of_le inferInstance (IsPrime.ne_top ‹_›)
      (IsPrime.le_of_pow_le hpP)
    exact ⟨⟨P, this.isPrime, ⟨hPp.symm⟩⟩,
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPI⟩
  · -- `relNorm I ≤ relNorm P ≤ P.under A = p`.
    exact dvd_iff_le.mpr ((relNorm_mono A (le_of_dvd hPI)).trans <|
      (relNorm_le_comap A _).trans_eq (over_def (P : Ideal B) p).symm)

/-- **Over a prime ideal all of whose primes above it have inertia degree one, the relative norm
of each prime above it is that prime ideal.** This is `N(P) = p ^ f(P ∣ p)` when every `f` is `1`,
with no separability or Galois hypothesis on the extension. -/
theorem relNorm_eq_of_forall_inertiaDeg_eq_one {p : Ideal A} [p.IsPrime]
    (hf : ∀ Q ∈ p.primesOver B, Q.inertiaDeg A = 1) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    relNorm A P = p := by
  -- The only prime over `⊥` is `⊥`, whose norm is `⊥`.
  rcases eq_or_ne p ⊥ with rfl | hp
  · rw [eq_bot_of_liesOver_bot A P, relNorm_bot]
  -- The norm of a prime `Q` over `p` is some power `p ^ s_Q` with `s_Q ≥ 1`, and applying the norm
  -- to `p B = ∏ Q ^ e_Q` gives `∑ e_Q · s_Q = n`; the fundamental identity `∑ e_Q · f_Q = n` with
  -- every `f_Q = 1` then forces every `s_Q = 1`.
  have : p.IsMaximal := IsPrime.isMaximal inferInstance hp
  have hpt : p ≠ ⊤ := IsPrime.ne_top inferInstance
  -- the norm of each prime over `p` is a positive power of `p`, as it lies below `p`
  have hpow : ∀ Q ∈ p.primesOver B, ∃ s, 0 < s ∧ relNorm A Q = p ^ s := by
    rintro Q ⟨_, _⟩
    obtain ⟨s, hs⟩ := exists_relNorm_eq_pow_of_isPrime Q p
    refine ⟨s, Nat.pos_of_ne_zero fun h0 ↦ hpt <| top_le_iff.mp ?_, hs⟩
    rw [← one_eq_top, ← pow_zero p, ← h0, ← hs, over_def Q p]
    exact relNorm_le_comap A Q
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
