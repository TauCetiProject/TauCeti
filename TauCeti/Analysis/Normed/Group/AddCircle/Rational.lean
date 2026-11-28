/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle
import TauCeti.NumberTheory.DiophantineApproximation.Dirichlet

/-!
# Separation of rational points on `UnitAddCircle`

Two distinct points `a / p` and `b / q` of the circle `ℝ / ℤ` are at distance at least `1 / (p q)`:
after subtracting the nearest integer, their difference is a nonzero integer over `p q`. In
particular the reduced fractions in `[0, 1)` with denominators at most `Q`, the Farey fractions of
order `Q` without the endpoint `1`, are pairwise at circular distance at least `1 / Q ^ 2`. This is
the separation hypothesis under which the additive large sieve is applied to Farey fractions.

## Main results

* `TauCeti.one_div_mul_le_norm_unitAddCircle_div_sub_div`: distinct points `a / p` and `b / q` of
  the circle are at distance at least `1 / (p q)`.
* `TauCeti.one_div_sq_le_norm_unitAddCircle_div_sub_div`: distinct reduced fractions in `[0, 1)`
  with denominators at most `Q` are at circular distance at least `1 / Q ^ 2`.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 16, §16.1.
-/

public section

namespace TauCeti

/-- **Distinct rational points of the circle are separated.** If `a / p` and `b / q` are distinct
points of `UnitAddCircle`, their distance is at least `1 / (p q)`. This is the circular form of
`TauCeti.one_div_mul_le_abs_div_sub_div`, applied after subtracting the nearest integer. For
`p = 0` or `q = 0` the bound is `0`. -/
theorem one_div_mul_le_norm_unitAddCircle_div_sub_div {a b : ℤ} {p q : ℕ}
    (h : (((a : ℝ) / p : ℝ) : UnitAddCircle) ≠ (((b : ℝ) / q : ℝ) : UnitAddCircle)) :
    1 / ((p : ℝ) * q) ≤ ‖(((a : ℝ) / p - b / q : ℝ) : UnitAddCircle)‖ := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  set z : ℤ := round ((a : ℝ) / p - b / q) with hz
  have hsub : (a : ℝ) / p - b / q - z = (a : ℝ) / p - ((b + z * q : ℤ) : ℝ) / q := by
    push_cast
    field_simp
    ring
  have key := one_div_mul_le_abs_div_sub_div (K := ℝ) (a := a) (a' := b + z * q) (q := (p : ℤ))
    (q' := (q : ℤ)) (by omega) (by omega) fun heq ↦ h ?_
  · rw [UnitAddCircle.norm_eq, ← hz, hsub]
    simpa only [Int.cast_natCast] using key
  · have ht : (a : ℝ) / p - b / q = z := by
      rw [← sub_eq_zero, hsub, sub_eq_zero]
      simpa only [Int.cast_natCast] using heq
    rw [← sub_eq_zero, ← AddCircle.coe_sub, ht]
    exact (AddCircle.coe_eq_zero_iff 1).2 ⟨z, by simp⟩

/-- **Circular separation of reduced fractions.** Two distinct reduced fractions `a / p` and
`b / q` in `[0, 1)` with denominators at most `Q` are at distance at least `1 / Q ^ 2` on
`UnitAddCircle`. The distance is the circular one, so wraparound is included. -/
theorem one_div_sq_le_norm_unitAddCircle_div_sub_div {a b p q Q : ℕ} (hpQ : p ≤ Q) (hqQ : q ≤ Q)
    (hap : a < p) (hbq : b < q) (ha : a.Coprime p) (hb : b.Coprime q) (hne : (a, p) ≠ (b, q)) :
    1 / (Q : ℝ) ^ 2 ≤ ‖(((a : ℝ) / p - b / q : ℝ) : UnitAddCircle)‖ := by
  have hp' : (0 : ℝ) < p := Nat.cast_pos.2 (Nat.zero_lt_of_lt hap)
  have hq' : (0 : ℝ) < q := Nat.cast_pos.2 (Nat.zero_lt_of_lt hbq)
  have hdist : (((a : ℝ) / p : ℝ) : UnitAddCircle) ≠ (((b : ℝ) / q : ℝ) : UnitAddCircle) := by
    intro heq
    rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at heq
    obtain ⟨n, hn⟩ := heq
    rw [zsmul_eq_mul, mul_one] at hn
    have ha1 : (a : ℝ) / p < 1 := (div_lt_one hp').2 (Nat.cast_lt.2 hap)
    have hb1 : (b : ℝ) / q < 1 := (div_lt_one hq').2 (Nat.cast_lt.2 hbq)
    have ha0 : (0 : ℝ) ≤ a / p := by positivity
    have hb0 : (0 : ℝ) ≤ b / q := by positivity
    have hn1 : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
    have hn2 : -1 < n := by exact_mod_cast (show ((-1 : ℤ) : ℝ) < n by push_cast; linarith)
    obtain rfl : n = 0 := by omega
    have hcross : a * q = b * p := by
      have h1 : (a : ℝ) / p = b / q := by linarith [hn, Int.cast_zero (R := ℝ)]
      rw [div_eq_div_iff hp'.ne' hq'.ne'] at h1
      exact_mod_cast h1
    have hpq : p ∣ q := ha.symm.dvd_of_dvd_mul_left ⟨b, by linarith⟩
    have hqp : q ∣ p := hb.symm.dvd_of_dvd_mul_left ⟨a, by linarith⟩
    obtain rfl : p = q := Nat.dvd_antisymm hpq hqp
    exact hne (by rw [Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_of_lt hap) hcross])
  have hQ : (0 : ℝ) < Q := hp'.trans_le (Nat.cast_le.2 hpQ)
  calc 1 / (Q : ℝ) ^ 2 ≤ 1 / ((p : ℝ) * q) := by
        rw [sq]
        exact one_div_le_one_div_of_le (mul_pos hp' hq')
          (mul_le_mul (Nat.cast_le.2 hpQ) (Nat.cast_le.2 hqQ) hq'.le hQ.le)
    _ ≤ ‖(((a : ℝ) / p - b / q : ℝ) : UnitAddCircle)‖ := by
        simpa using one_div_mul_le_norm_unitAddCircle_div_sub_div (a := a) (b := b)
          (by simpa using hdist)

/-- `0 / 1` and `3 / 4` are at circular distance at least `1 / 16`, the bound for `Q = 4`; their
circular distance is `1 / 4`, although their distance on the real line is `3 / 4`. -/
example : 1 / ((4 : ℕ) : ℝ) ^ 2 ≤ ‖((((0 : ℕ) : ℝ) / (1 : ℕ) - (3 : ℕ) / (4 : ℕ) : ℝ) :
    UnitAddCircle)‖ :=
  one_div_sq_le_norm_unitAddCircle_div_sub_div (by decide) le_rfl (by decide) (by decide)
    (by decide) (by decide) (by decide)

end TauCeti
