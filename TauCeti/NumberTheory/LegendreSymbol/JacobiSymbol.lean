/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import TauCeti.NumberTheory.LegendreSymbol.ZModChar

/-!
# The Jacobi symbol under reflection of the denominator

Mathlib's `jacobiSym.mod_right` says that for odd `b` the Jacobi symbol `J(a | b)` depends only on
`b` modulo `4 |a|`. This file adds the companion statement for the reflected class `-b`: if `b` and
`b'` are odd and `4 |a|` divides `b + b'`, then `J(a | b') = sign a * J(a | b)`. Together the two
say that `b ↦ J(a | b)`, extended to negative odd `b` by `J(a | -b) = sign a * J(a | b)`, is
periodic modulo `4 |a|` on all odd integers; this is the input that makes the Kronecker symbol
`(D / ·)` of a discriminant a Dirichlet character whose value at `-1` is the sign of `D`.

It also records the form of quadratic reciprocity for an integer numerator `a ≡ 1 (mod 4)`, of
either sign: `J(a | b) = J(b | |a|)` for odd `b`.

The proof of the reflection law for a natural numerator is adapted from the proof of Mathlib's
`jacobiSym.mod_right'`: both split off the power of `2` and apply quadratic reciprocity to the odd
part.

## Main statements

* `TauCeti.jacobiSym_eq_sign_mul_of_dvd_add`: `J(a | b') = sign a * J(a | b)` when `b`, `b'` are
  odd and `4 |a| ∣ b + b'`.
* `TauCeti.jacobiSym_eq_sign_mul_of_emod_four_eq_zero`,
  `TauCeti.jacobiSym_mod_natAbs_of_emod_four_eq_zero`: for `a ≡ 0 (mod 4)` the modulus `4 |a|` in
  both statements can be lowered to `|a|`.
* `TauCeti.jacobiSym_eq_jacobiSym_natAbs_of_emod_four_eq_one`: `J(a | b) = J(b | |a|)` for
  `a ≡ 1 (mod 4)` and odd `b`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §1.4.
-/

public section

open ZMod

namespace TauCeti

/-- The reflection law for a natural numerator: the sign `sign a` is `1` here. The proof is
adapted from the proof of Mathlib's `jacobiSym.mod_right'`. -/
private theorem jacobiSym_natCast_eq_of_dvd_add (a : ℕ) {b b' : ℕ} (hb : Odd b) (hb' : Odd b')
    (h : 4 * a ∣ b + b') : jacobiSym a b' = jacobiSym a b := by
  rcases eq_or_ne a 0 with rfl | ha₀
  · rw [mul_zero, zero_dvd_iff] at h
    exact absurd (Nat.eq_zero_of_add_eq_zero_right h) hb.pos.ne'
  obtain ⟨e, a', ha₁', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha₀ 2 (by decide)
  have ha₁ : Odd a' := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp ha₁')
  -- Split `J(2 ^ e * a' | ·)` into `χ₈ ^ e` times `J(a' | ·)`, and apply reciprocity to the latter.
  push_cast
  simp only [jacobiSym.mul_left, jacobiSym.pow_left]
  rw [jacobiSym.at_two hb, jacobiSym.at_two hb', jacobiSym.quadratic_reciprocity' ha₁ hb,
    jacobiSym.quadratic_reciprocity' ha₁ hb']
  -- The factor `χ₈ b ^ e` only matters for `e ≥ 1`, when `8 ∣ b + b'` and `χ₈` is even.
  have h₈ : χ₈ b' ^ e = χ₈ b ^ e := by
    rcases e with - | e
    · rw [pow_zero, pow_zero]
    · refine congrArg (· ^ (e + 1)) (χ₈_natCast_eq_of_dvd_add (dvd_trans ?_ h))
      exact ⟨2 ^ e * a', by rw [pow_succ]; ring⟩
  -- The sign of reciprocity flips with `χ₄ b`, and so does `J(b | a')`; the flips cancel.
  have hqr : qrSign b' a' = χ₄ a' * qrSign b a' := by
    rw [qrSign, qrSign, χ₄_natCast_eq_neg_of_dvd_add (dvd_trans (dvd_mul_right 4 _) h),
      jacobiSym.neg _ ha₁]
  have hJ : jacobiSym b' a' = χ₄ a' * jacobiSym b a' := by
    rw [← jacobiSym.neg _ ha₁]
    have hdvd : (a' : ℤ) ∣ b + b' := by
      exact_mod_cast dvd_trans ⟨4 * 2 ^ e, by ring⟩ h
    refine jacobiSym.mod_left' (Int.modEq_iff_dvd.mpr ?_).eq
    rw [← neg_add']
    exact hdvd.neg_right
  rw [h₈, hqr, hJ, mul_mul_mul_comm (χ₄ a' : ℤ), χ₄_natCast_mul_self ha₁, one_mul]

/-- **Reflection of the denominator of the Jacobi symbol.** If `b` and `b'` are odd and `4 |a|`
divides `b + b'`, so that `b' ≡ -b (mod 4 |a|)`, then `J(a | b') = sign a * J(a | b)`. Together
with `jacobiSym.mod_right`, this says that `J(a | ·)` is an odd or even function on the odd
residues modulo `4 |a|` according to the sign of `a`. -/
theorem jacobiSym_eq_sign_mul_of_dvd_add (a : ℤ) {b b' : ℕ} (hb : Odd b) (hb' : Odd b')
    (h : 4 * a.natAbs ∣ b + b') : jacobiSym a b' = a.sign * jacobiSym a b := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -n := ⟨a.natAbs, by omega⟩
    rw [Int.natAbs_neg, Int.natAbs_natCast] at h
    rw [jacobiSym.neg _ hb, jacobiSym.neg _ hb', jacobiSym_natCast_eq_of_dvd_add n hb hb' h,
      χ₄_natCast_eq_neg_of_dvd_add (dvd_trans (dvd_mul_right 4 _) h),
      Int.sign_eq_neg_one_of_neg ha]
    ring
  · rw [Int.natAbs_zero, mul_zero, zero_dvd_iff] at h
    exact absurd (Nat.eq_zero_of_add_eq_zero_right h) hb.pos.ne'
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n := ⟨a.natAbs, by omega⟩
    rw [Int.natAbs_natCast] at h
    rw [jacobiSym_natCast_eq_of_dvd_add n hb hb' h, Int.sign_eq_one_of_pos ha, one_mul]

/-- **Quadratic reciprocity for a numerator `a ≡ 1 (mod 4)`**, of either sign: for odd `b`,
`J(a | b) = J(b | |a|)`. For `a > 0` this is `jacobiSym.quadratic_reciprocity_one_mod_four`; for
`a < 0` the supplementary factor `J(-1 | b) = χ₄ b` cancels the sign of reciprocity, since then
`|a| ≡ 3 (mod 4)`. -/
theorem jacobiSym_eq_jacobiSym_natAbs_of_emod_four_eq_one {a : ℤ} (ha : a % 4 = 1) {b : ℕ}
    (hb : Odd b) : jacobiSym a b = jacobiSym b a.natAbs := by
  rcases Int.natAbs_eq a with h | h
  · rw [h, Int.natAbs_natCast]
    exact jacobiSym.quadratic_reciprocity_one_mod_four (by omega) hb
  · have h3 : a.natAbs % 4 = 3 := by omega
    have hodd : Odd a.natAbs := Nat.odd_iff.mpr (by omega)
    -- The sign of reciprocity is `(-1) ^ (b / 2) = χ₄ b`, as `a.natAbs / 2` is odd.
    rw [h, Int.natAbs_neg, Int.natAbs_natCast, jacobiSym.neg _ hb,
      jacobiSym.quadratic_reciprocity hodd hb, pow_mul,
      Odd.neg_one_pow (Nat.odd_iff.mpr (by omega)), χ₄_eq_neg_one_pow (Nat.odd_iff.mp hb)]
    simp [← mul_assoc, ← mul_pow]

/-- For `a ≡ 0 (mod 4)`, the Jacobi symbol `J(a | b)` at odd `b` depends only on `b` modulo `|a|`,
not merely modulo `4 |a|` as in `jacobiSym.mod_right`: the factor `J(4 | b) = 1` may be dropped. -/
theorem jacobiSym_mod_natAbs_of_emod_four_eq_zero {a : ℤ} (ha : a % 4 = 0) {b : ℕ}
    (hb : Odd b) : jacobiSym a b = jacobiSym a (b % a.natAbs) := by
  obtain ⟨c, rfl⟩ := Int.dvd_of_emod_eq_zero ha
  have hb' : Odd (b % (4 * c).natAbs) :=
    hb.mod_even (by rw [Int.natAbs_mul]; exact (even_two_mul 2).mul_right _)
  rw [← jacobiSym.div_four_left ha (Nat.odd_iff.mp hb),
    ← jacobiSym.div_four_left ha (Nat.odd_iff.mp hb'), Int.mul_ediv_cancel_left _ four_ne_zero,
    jacobiSym.mod_right c hb, Int.natAbs_mul]
  simp only [Int.reduceAbs]

/-- The reflection law `jacobiSym_eq_sign_mul_of_dvd_add` for `a ≡ 0 (mod 4)`, where it needs only
`|a| ∣ b + b'`. -/
theorem jacobiSym_eq_sign_mul_of_emod_four_eq_zero {a : ℤ} (ha : a % 4 = 0) {b b' : ℕ}
    (hb : Odd b) (hb' : Odd b') (h : a.natAbs ∣ b + b') :
    jacobiSym a b' = a.sign * jacobiSym a b := by
  obtain ⟨c, rfl⟩ := Int.dvd_of_emod_eq_zero ha
  rw [← jacobiSym.div_four_left ha (Nat.odd_iff.mp hb),
    ← jacobiSym.div_four_left ha (Nat.odd_iff.mp hb'), Int.mul_ediv_cancel_left _ four_ne_zero,
    Int.sign_mul, Int.sign_eq_one_of_pos four_pos, one_mul]
  exact jacobiSym_eq_sign_mul_of_dvd_add c hb hb' (by rwa [Int.natAbs_mul] at h)

end TauCeti
