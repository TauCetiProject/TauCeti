/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Square products and prime-free parts

A pair of natural numbers has square product exactly when both are squares times a common factor.
For a prime `p`, the `p`-free part of a natural number is square precisely when the number is
square or becomes square after multiplication by `p`. In particular, a product with square odd
part is either a square or twice a square.
-/

public section

namespace Nat

/-- A product is square precisely when its factors are squares times a common natural number. -/
theorem isSquare_mul_iff_exists_eq_mul_sq {m n : ℕ} :
    IsSquare (m * n) ↔ ∃ a b c : ℕ, m = a * b ^ 2 ∧ n = a * c ^ 2 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨r, hr⟩
    by_cases hm : m = 0
    · exact ⟨n, 0, 1, by simp [hm], by simp⟩
    let d := m.gcd n
    have hdm : d ∣ m := Nat.gcd_dvd_left m n
    have hdn : d ∣ n := Nat.gcd_dvd_right m n
    have hd : 0 < d := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)
    have hcop : (m / d).Coprime (n / d) := Nat.coprime_div_gcd_div_gcd hd
    have hu : IsUnit (GCDMonoid.gcd (m / d) (n / d)) := by
      simpa only [gcd_eq_nat_gcd, hcop.gcd_eq_one] using (isUnit_one : IsUnit (1 : ℕ))
    have hu' : IsUnit (GCDMonoid.gcd (n / d) (m / d)) := by
      simpa only [gcd_eq_nat_gcd, hcop.symm.gcd_eq_one] using (isUnit_one : IsUnit (1 : ℕ))
    have hprod : d ^ 2 * (m / d * (n / d)) = r ^ 2 := by
      rw [pow_two, mul_mul_mul_comm, Nat.mul_div_cancel' hdm, Nat.mul_div_cancel' hdn, hr,
        pow_two]
    have hdr : d ∣ r := (Nat.pow_dvd_pow_iff two_ne_zero).mp ⟨_, hprod.symm⟩
    obtain ⟨s, rfl⟩ := hdr
    have hquot : m / d * (n / d) = s ^ 2 :=
      Nat.eq_of_mul_eq_mul_left (pow_pos hd 2) (by simpa only [mul_pow] using hprod)
    obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow hu hquot
    obtain ⟨c, hc⟩ := exists_eq_pow_of_mul_eq_pow hu' ((mul_comm _ _).trans hquot)
    exact ⟨d, b, c, by rw [← hb, Nat.mul_div_cancel' hdm], by rw [← hc, Nat.mul_div_cancel' hdn]⟩
  · rintro ⟨a, b, c, rfl, rfl⟩
    refine ⟨a * b * c, ?_⟩
    simp only [pow_two]
    ac_rfl

/-- A natural number has square `p`-free part if and only if it or its product with `p` is
square, for `p` prime. -/
theorem isSquare_ordCompl_iff {p n : ℕ} (hp : p.Prime) :
    IsSquare (ordCompl[p] n) ↔ IsSquare n ∨ IsSquare (p * n) := by
  constructor
  · rintro ⟨r, hr⟩
    have hn : n = p ^ n.factorization p * (r * r) := by
      rw [← hr, ordProj_mul_ordCompl_eq_self]
    obtain ⟨k, hk | hk⟩ := (n.factorization p).even_or_odd'
    · left
      refine ⟨p ^ k * r, ?_⟩
      have he : n.factorization p = k * 2 := by omega
      rw [hn, he, pow_mul, pow_two, mul_mul_mul_comm]
    · right
      refine ⟨p ^ (k + 1) * r, ?_⟩
      have he : (n.factorization p).succ = (k + 1) * 2 := by omega
      conv_lhs => rw [hn, ← mul_assoc, ← pow_succ', he, pow_mul, pow_two]
      exact mul_mul_mul_comm _ _ _ _
  · rintro (⟨r, hr⟩ | ⟨r, hr⟩)
    · exact ⟨ordCompl[p] r, by rw [hr, ordCompl_mul]⟩
    · refine ⟨ordCompl[p] r, ?_⟩
      have h := congrArg (fun k : ℕ ↦ ordCompl[p] k) hr
      have hp' : ordCompl[p] p = 1 := by
        simpa only [pow_one] using (ordCompl_self_pow (k := 1) hp)
      simpa only [ordCompl_mul, hp', one_mul] using h

end Nat
