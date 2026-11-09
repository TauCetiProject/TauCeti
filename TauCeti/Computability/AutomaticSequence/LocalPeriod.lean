/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A local period from two close radix scales

This file isolates the arithmetic heart of Krebs's proof of Cobham's theorem. Suppose a
sequence `f : ℕ → Δ` satisfies three block comparisons: the block of `f` of length `2B + 1`
starting at `xB` agrees with the blocks starting at `uB` and at `vB`, and the block of length
`2A + 1` starting at `uA` agrees with the one starting at `vA`. If `u, v < ξ` and the scales
are close, `6ξ|A - B| ≤ B`, then `p = |(u - v)(A - B)|` is a period of `f` on the integer
window `[xB + B/3, xB + 5B/3]`, and `6p ≤ B`. When `u ≠ v` and `A ≠ B` the period is
positive.

In Cobham's theorem `A` and `B` are close powers of two multiplicatively independent bases,
so `A ≠ B`, and the block comparisons come from finitely many automaton states. The windows
`[xB + B/3, xB + 5B/3]` for consecutive `x` overlap by at least `B/3`, enough to glue the
local periods into a period of a whole tail.

All differences are taken in `ℤ`. The window is stated with the inequalities
`3xB + B ≤ 3t` and `3(t + p) ≤ 3xB + 5B`, so that no rounding is involved.

## Main results

* `TauCeti.natAbs_sub_mul_sub_period_on_radix_window`: the period `|(u - v)(A - B)|` is
  positive, at most `B/6`, and a period of `f` on the window `[xB + B/3, xB + 5B/3]`.

## References

* Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem* (2018), §3, the
  definition of `p_st` and the three uses of equation (1) in the proof of Theorem 1.
-/

public section

namespace TauCeti

variable {Δ : Type*} {f : ℕ → Δ} {A B ξ x u v p : ℕ}

/-- The period step when `(u - v)(A - B)` is nonnegative, so that it equals the period. Write
`t = xB + z` and `w = z - v(A - B)`. Then `vA + w = vB + z` and `uA + w = uB + z + p`, and
closeness of `A` and `B` keeps `w` in `[0, 2A]`. -/
private theorem apply_add_eq_of_radix_blocks (hv : v < ξ)
    (hclose : 6 * ξ * |(A : ℤ) - B| ≤ B) (hp : (p : ℤ) = (u - v) * (A - B))
    (hxu : ∀ z ≤ 2 * B, f (x * B + z) = f (u * B + z))
    (hxv : ∀ z ≤ 2 * B, f (x * B + z) = f (v * B + z))
    (huv : ∀ w ≤ 2 * A, f (u * A + w) = f (v * A + w)) {t : ℕ}
    (ht : 3 * (x * B) + B ≤ 3 * t) (htp : 3 * (t + p) ≤ 3 * (x * B) + 5 * B) :
    f (t + p) = f t := by
  obtain ⟨z, rfl⟩ : ∃ z, t = x * B + z := ⟨t - x * B, by omega⟩
  have hz : (B : ℤ) ≤ 3 * z := by exact_mod_cast (by omega : B ≤ 3 * z)
  have hzp : 3 * (z : ℤ) ≤ 5 * B := by exact_mod_cast (by omega : 3 * z ≤ 5 * B)
  -- The bound `6 (v + 1) |A - B| ≤ B` controls the shift `v (A - B)` and `|A - B|` itself.
  have hD := abs_nonneg ((A : ℤ) - B)
  have hv0 : (0 : ℤ) ≤ v := by positivity
  have hvD : ((v : ℤ) + 1) * |(A : ℤ) - B| ≤ ξ * |(A : ℤ) - B| :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hv) hD
  have hvD₀ := mul_nonneg hv0 hD
  have hle : (v : ℤ) * (A - B) ≤ v * |(A : ℤ) - B| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hv0
  have hge : (v : ℤ) * -|(A : ℤ) - B| ≤ v * (A - B) :=
    mul_le_mul_of_nonneg_left (neg_abs_le _) hv0
  have hlow := neg_abs_le ((A : ℤ) - B)
  obtain ⟨w, hw⟩ : ∃ w : ℕ, (w : ℤ) = z - v * (A - B) :=
    ⟨(z - v * (A - B) : ℤ).toNat, Int.toNat_of_nonneg (by linarith)⟩
  have hwA : w ≤ 2 * A := by
    have : (w : ℤ) ≤ 2 * A := by linarith
    exact_mod_cast this
  have hidx₁ : v * A + w = v * B + z := by
    have : ((v * A + w : ℕ) : ℤ) = ((v * B + z : ℕ) : ℤ) := by
      push_cast
      rw [hw]
      ring
    exact_mod_cast this
  have hidx₂ : u * A + w = u * B + (z + p) := by
    have : ((u * A + w : ℕ) : ℤ) = ((u * B + (z + p) : ℕ) : ℤ) := by
      push_cast
      rw [hw, hp]
      ring
    exact_mod_cast this
  calc f (x * B + z + p) = f (x * B + (z + p)) := by rw [Nat.add_assoc]
    _ = f (u * B + (z + p)) := hxu _ (by omega)
    _ = f (u * A + w) := by rw [hidx₂]
    _ = f (v * A + w) := huv w hwA
    _ = f (v * B + z) := by rw [hidx₁]
    _ = f (x * B + z) := (hxv z (by omega)).symm

/-- **The local period from two close radix scales.** Let `u, v < ξ` be distinct and `A ≠ B`
with `6ξ|A - B| ≤ B`. Suppose the blocks of `f` of length `2B + 1` starting at `xB`, `uB` and
`vB` agree, and the blocks of length `2A + 1` starting at `uA` and `vA` agree. Then
`p = |(u - v)(A - B)|` satisfies `0 < p` and `6p ≤ B`, and `f (t + p) = f t` whenever `t` and
`t + p` lie in the integer window `[xB + B/3, xB + 5B/3]`. -/
theorem natAbs_sub_mul_sub_period_on_radix_window (hu : u < ξ) (hv : v < ξ) (huv : u ≠ v)
    (hAB : A ≠ B) (hclose : 6 * ξ * |(A : ℤ) - B| ≤ B)
    (hp : p = ((u - v : ℤ) * (A - B)).natAbs)
    (hxu : ∀ z ≤ 2 * B, f (x * B + z) = f (u * B + z))
    (hxv : ∀ z ≤ 2 * B, f (x * B + z) = f (v * B + z))
    (hA : ∀ w ≤ 2 * A, f (u * A + w) = f (v * A + w)) :
    0 < p ∧ 6 * p ≤ B ∧
      ∀ t, 3 * (x * B) + B ≤ 3 * t → 3 * (t + p) ≤ 3 * (x * B) + 5 * B → f (t + p) = f t := by
  have hpabs : (p : ℤ) = |(u : ℤ) - v| * |(A : ℤ) - B| := by
    rw [hp, Int.natCast_natAbs, abs_mul]
  refine ⟨?_, ?_, fun t ht htp ↦ ?_⟩
  · rw [hp, Int.natAbs_pos]
    exact mul_ne_zero (sub_ne_zero.2 (by exact_mod_cast huv))
      (sub_ne_zero.2 (by exact_mod_cast hAB))
  · have huvξ : |(u : ℤ) - v| ≤ ξ := (abs_sub_lt_iff.2 ⟨by omega, by omega⟩).le
    have := mul_le_mul_of_nonneg_right huvξ (abs_nonneg ((A : ℤ) - B))
    have : (6 * p : ℤ) ≤ B := by linarith
    exact_mod_cast this
  · rcases le_total 0 ((u - v : ℤ) * (A - B)) with h | h
    · exact apply_add_eq_of_radix_blocks hv hclose
        (by rw [hp, Int.natCast_natAbs, abs_of_nonneg h]) hxu hxv hA ht htp
    · exact apply_add_eq_of_radix_blocks hu hclose
        (by rw [hp, Int.natCast_natAbs, abs_of_nonpos h]; ring) hxv hxu
        (fun w hw ↦ (hA w hw).symm) ht htp

-- The period does not depend on the order of the representatives or on the sign of `A - B`.
example : ((0 - 1 : ℤ) * (17 - 18)).natAbs = 1 ∧ ((1 - 0 : ℤ) * (18 - 17)).natAbs = 1 := by
  decide

-- Equal scales or equal representatives give the zero period, which the theorem excludes.
example : ((u - u : ℤ) * (A - B)).natAbs = 0 ∧ ((u - v : ℤ) * (A - A)).natAbs = 0 := by
  simp

-- With `A < B`: the scales `11` and `12` and the representatives `1, 0 < 2` give period one
-- on the window `[12x + 4, 12x + 20]`.
example (hxu : ∀ z ≤ 2 * 12, f (x * 12 + z) = f (1 * 12 + z))
    (hxv : ∀ z ≤ 2 * 12, f (x * 12 + z) = f (0 * 12 + z))
    (hA : ∀ w ≤ 2 * 11, f (1 * 11 + w) = f (0 * 11 + w)) (t : ℕ)
    (ht : 12 * x + 4 ≤ t) (ht' : t + 1 ≤ 12 * x + 20) : f (t + 1) = f t :=
  (natAbs_sub_mul_sub_period_on_radix_window (ξ := 2) (by decide) (by decide) (by decide)
    (by decide) (by norm_num) rfl hxu hxv hA).2.2 t (by omega) (by omega)

end TauCeti
