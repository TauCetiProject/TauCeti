/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic

/-!
# Positivity of prime-discriminant factors

In a positive product of prime discriminants with at most one even factor, the absence of prime
divisors congruent to `3` modulo `4` forces all factors to be positive. This criterion is used
in the principal genus test for the different class in Duke, Imamoglu and Toth,
*Geometric invariants for real quadratic fields*, §4, p. 960.
-/

public section

namespace TauCeti.Multiquadratic

/-- A positive product of distinct prime discriminants, at most one even, has all factors
positive if and only if it has no prime divisor congruent to `3` modulo `4`. -/
theorem forall_pos_iff_forall_prime_dvd_mod_four_ne_three {s : Finset ℤ}
    (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ Q ∈ s, IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant Q → P = Q)
    (hpos : 0 < ∏ P ∈ s, P) :
    (∀ P ∈ s, 0 < P) ↔
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (∏ P ∈ s, P) → p % 4 ≠ 3 := by
  classical
  constructor
  · intro h p hp hpd
    obtain ⟨P, hP, hpdP⟩ := (Nat.prime_iff_prime_int.mp hp).exists_mem_finset_dvd hpd
    have hpP := (natCast_dvd_primeDiscriminant_iff (hs P hP) hp).mp hpdP
    have hPpos := h P hP
    rcases isPrimeDiscriminant_iff.mp (hs P hP) with he | ⟨q, -, hq, rfl⟩
    · rw [primeDiscriminantPrime_of_isEvenPrimeDiscriminant he] at hpP
      simp [hpP]
    · rw [primeDiscriminantPrime_oddPrimeDiscriminant hq] at hpP
      rw [oddPrimeDiscriminant_pos_iff] at hPpos
      omega
  · intro h
    have hodd (P : ℤ) (hP : P ∈ s) (hPe : ¬ IsEvenPrimeDiscriminant P) : 0 < P := by
      obtain ⟨p, hp, hodd, rfl⟩ := (isPrimeDiscriminant_iff.mp (hs P hP)).resolve_left hPe
      have hpP : (p : ℤ) ∣ oddPrimeDiscriminant p := dvd_oddPrimeDiscriminant_iff.mpr dvd_rfl
      have hp3 := h p hp (hpP.trans (Finset.dvd_prod_of_mem (fun Q => Q) hP))
      rw [oddPrimeDiscriminant_pos_iff]
      exact (Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd)).resolve_right hp3
    intro P hP
    by_cases hPe : IsEvenPrimeDiscriminant P
    · -- Each remaining factor is an odd prime discriminant.
      have hrest : 0 < ∏ Q ∈ s.erase P, Q := by
        apply Finset.prod_pos
        intro Q hQ
        exact hodd Q (Finset.mem_of_mem_erase hQ) fun hQe =>
          Finset.ne_of_mem_erase hQ (heven Q (Finset.mem_of_mem_erase hQ) P hP hQe hPe)
      rw [← Finset.mul_prod_erase s (fun Q => Q) hP] at hpos
      exact pos_of_mul_pos_left hpos hrest.le
    · exact hodd P hP hPe

end TauCeti.Multiquadratic
