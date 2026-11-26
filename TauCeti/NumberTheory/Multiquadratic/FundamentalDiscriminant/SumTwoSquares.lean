/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import Mathlib.NumberTheory.SumTwoSquares

/-!
# Positive discriminants and sums of two squares

In a positive product of prime discriminants with at most one even factor, the absence of prime
divisors congruent to `3` modulo `4` forces all factors to be positive. For a positive fundamental
discriminant the same prime-divisor condition is equivalent to representability as a sum of two
integer squares by the valuation criterion `Nat.eq_sq_add_sq_iff`. These arithmetic criteria
are used in the principal genus test for the different class in Duke, Imamoglu and Toth,
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

namespace Int

/-- A positive fundamental discriminant is a sum of two integer squares exactly when it has no
prime divisor congruent to `3` modulo `4`. -/
theorem IsFundamentalDiscr.exists_sq_add_sq_iff {D : ℤ} (hD : IsFundamentalDiscr D)
    (hpos : 0 < D) :
    (∃ x y : ℤ, D = x ^ 2 + y ^ 2) ↔
      ∀ p : ℕ, p.Prime → (p : ℤ) ∣ D → p % 4 ≠ 3 := by
  have hcast : (D.natAbs : ℤ) = D := Int.natAbs_of_nonneg hpos.le
  have hD0 : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hpos.ne'
  have hrepr : (∃ x y : ℤ, D = x ^ 2 + y ^ 2) ↔ (∃ x y : ℕ, D.natAbs = x ^ 2 + y ^ 2) := by
    constructor
    · rintro ⟨x, y, h⟩
      refine ⟨x.natAbs, y.natAbs, ?_⟩
      exact_mod_cast (by simpa only [Int.natCast_natAbs, sq_abs, hcast] using h :
        (D.natAbs : ℤ) = (x.natAbs : ℤ) ^ 2 + (y.natAbs : ℤ) ^ 2)
    · rintro ⟨x, y, h⟩
      exact ⟨x, y, hcast.symm.trans (by exact_mod_cast h)⟩
  rw [hrepr, Nat.eq_sq_add_sq_iff]
  constructor
  · intro h p hp hpD hp3
    have hpD' : p ∣ D.natAbs := Int.natCast_dvd.mp hpD
    have heven := h p (Nat.mem_primeFactors.mpr ⟨hp, hpD', hD0⟩) hp3
    have hge : 1 ≤ multiplicity p D.natAbs :=
      (Nat.pow_dvd_iff_le_multiplicity (k := 1) hp.ne_one hD0).mp (by simpa using hpD')
    -- A positive even valuation would make the square of this odd prime divide the discriminant.
    rw [Nat.padicValNat_def, Nat.even_iff] at heven
    have hsq : p ^ 2 ∣ D.natAbs :=
      (Nat.pow_dvd_iff_le_multiplicity hp.ne_one hD0).mpr (by omega)
    have hsqD : (p : ℤ) ^ 2 ∣ D := by
      rw [← hcast]
      exact_mod_cast hsq
    exact (isFundamentalDiscr_def.mp hD).2.2 p hp (Nat.odd_iff.mpr (by omega)) hsqD
  · intro h p hp hp3
    obtain ⟨hprime, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
    exact (h p hprime (Int.natCast_dvd.mpr hdvd) hp3).elim

end Int
