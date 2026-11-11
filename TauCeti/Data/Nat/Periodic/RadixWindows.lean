/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Periodic.Interval

/-!
# From periodic radix windows to a periodic tail

Suppose each integer window `[xB + B/3, xB + 5B/3]` with index `x ≥ N` has a positive
period at most `B/6`. Then a single positive period at most `B/6` holds on the entire tail
starting at `(N + 1)B`. The periods of the individual windows need not agree.

All endpoints are rounded inward. The inequalities in the public statement avoid division,
so callers can supply local periods without manipulating rounded endpoints.

## References

Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem* (2018), §3, final interval
induction in the proof of Theorem 1.
-/

public section

namespace TauCeti.Nat

/-- Positive periods at most `B/6` on all the radix windows with indices `x ≥ N` force one
positive period, still at most `B/6`, on the tail starting at `(N + 1)B`. -/
theorem exists_periodic_tail_of_period_on_radix_windows {α : Type*} {f : ℕ → α} {B N : ℕ}
    (h : ∀ x, N ≤ x → ∃ p, 0 < p ∧ 6 * p ≤ B ∧
      ∀ t, 3 * (x * B) + B ≤ 3 * t → 3 * (t + p) ≤ 3 * (x * B) + 5 * B →
        f (t + p) = f t) :
    ∃ p, 0 < p ∧ 6 * p ≤ B ∧ ∀ t, (N + 1) * B ≤ t → f (t + p) = f t := by
  obtain ⟨p, hp, hpB, hfirst⟩ := h N le_rfl
  have hB : 0 < B := by omega
  -- The integer endpoints are ceiling(B/3) and floor(5B/3).
  let a := (B + 2) / 3
  let b := 5 * B / 3
  have ha : B ≤ 3 * a ∧ a ≤ B := by dsimp [a]; omega
  have hb : 3 * b ≤ 5 * B := by dsimp [b]; omega
  have hperiod : ∀ k t, N * B + a ≤ t → t + p ≤ (N + k) * B + b →
      f (t + p) = f t := by
    intro k
    induction k with
    | zero =>
      intro t ht htp
      simp only [Nat.add_zero] at htp
      exact hfirst t (by omega) (by omega)
    | succ k ih =>
      obtain ⟨q, hq, hqB, hnext⟩ := h (N + (k + 1)) (by omega)
      have hl : N * B + a ≤ (N + (k + 1)) * B + a := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      have hr : (N + k) * B + b ≤ (N + (k + 1)) * B + b := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      have hoverlap : p + q ≤ (Finset.Icc (max (N * B + a)
          ((N + (k + 1)) * B + a)) (min ((N + k) * B + b)
          ((N + (k + 1)) * B + b))).card := by
        rw [max_eq_right hl, min_eq_left hr, Nat.card_Icc]
        simp only [Nat.add_mul, Nat.one_mul]
        dsimp [a, b]
        omega
      have hglue := period_on_Icc_min_max hq ih
        (fun t ht htp ↦ hnext t (by omega) (by omega)) hoverlap
      simpa only [min_eq_left hl, max_eq_right hr] using hglue
  refine ⟨p, hp, hpB, ?_⟩
  intro t ht
  have hlarge : N + (t + p) ≤ (N + (t + p)) * B :=
    Nat.le_mul_of_pos_right _ hB
  apply hperiod (t + p) t
  · rw [Nat.add_mul, Nat.one_mul] at ht
    omega
  · omega

-- The smallest allowed widths include the endpoint-rounding cases B = 6, 7, 8.
example (B : ℕ) (hB : B = 6 ∨ B = 7 ∨ B = 8) :
    2 ≤ 5 * B / 3 + 1 - (B + (B + 2) / 3) := by omega

-- A finite exceptional prefix is allowed.
example : ∃ p, 0 < p ∧ 6 * p ≤ 6 ∧ ∀ t, (2 + 1) * 6 ≤ t →
    (if t + p < 10 then t + p else 0 : ℕ) = (if t < 10 then t else 0) := by
  apply exists_periodic_tail_of_period_on_radix_windows
    (f := fun t ↦ if t < 10 then t else 0) (B := 6) (N := 2)
  intro x hx
  refine ⟨1, by omega, by omega, ?_⟩
  intro t ht _
  have hxB : 2 * 6 ≤ x * 6 := Nat.mul_le_mul_right 6 hx
  split_ifs <;> omega

end TauCeti.Nat
