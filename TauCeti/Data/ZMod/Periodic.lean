/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.ZMod.Basic

/-!
# Equally spaced cyclic points and periodic functions indexed by `ZMod`

Stepping from `k : ZMod N` to `k + 1` (`N ≠ 0`) either increments the canonical representative
`ZMod.val` by `1` or wraps around from `N - 1` to `0` (`ZMod.val_add_one_eq_or`). Consequently, for
equally spaced points `k.val * (L / N)` of step `L / N` in any division semiring, advancing `k` to
`k + 1` either adds `L / N` or shifts by `L / N - L` (`ZMod.val_add_one_mul_div_eq_or`), and an
`L`-periodic function evaluated at `s₀ + k.val * (L / N)` advances by `±L / N` when `k` steps to
`k ± 1` (`Function.Periodic.apply_add_val_add_one_mul_div`,
`Function.Periodic.apply_add_val_sub_one_mul_div`).

## Main results

* `ZMod.val_add_one_eq_or`: `(k + 1).val = k.val + 1 ∨ (k + 1).val + N = k.val + 1` for `N ≠ 0`.
* `ZMod.val_add_one_mul_div_eq_or`: advancing `k : ZMod N` to `k + 1` in `k.val * (L / N)` either
  adds `L / N` or adds `L / N - L`.
* `Function.Periodic.apply_add_val_add_one_mul_div`,
  `Function.Periodic.apply_add_val_sub_one_mul_div`: stepping `k : ZMod N` by `±1` inside an
  `L`-periodic function evaluated at `s₀ + k.val * (L / N)` shifts the argument by `±L / N`.
-/

public section

namespace ZMod

/-- Stepping by `1` in `ZMod N` (`N ≠ 0`) either increments the canonical representative
`ZMod.val` by `1` or wraps around from `N - 1` to `0` so that `(k + 1).val + N = k.val + 1`. -/
theorem val_add_one_eq_or {N : ℕ} [NeZero N] (k : ZMod N) :
    (k + 1).val = k.val + 1 ∨ (k + 1).val + N = k.val + 1 := by
  have hk : k + 1 = ((k.val + 1 : ℕ) : ZMod N) := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  by_cases hlt : k.val + 1 < N
  · exact Or.inl (by rw [hk, ZMod.val_natCast_of_lt hlt])
  · right
    have hN : k.val + 1 = N := by have := k.val_lt; omega
    rw [hk, hN, ZMod.natCast_self, ZMod.val_zero, zero_add]

/-- For equally spaced points `k.val * (L / N)` of step `L / N` in a division semiring (such as
`ℝ`), advancing `k : ZMod N` to `k + 1` either adds `L / N` or adds `L / N - L`. -/
theorem val_add_one_mul_div_eq_or {𝕜 : Type*} [DivisionSemiring 𝕜] {N : ℕ}
    (k : ZMod N) (L : 𝕜) :
    ((k + 1).val : 𝕜) * (L / N) = (k.val : 𝕜) * (L / N) + L / N ∨
      ((k + 1).val : 𝕜) * (L / N) + L = (k.val : 𝕜) * (L / N) + L / N := by
  rcases eq_or_ne (N : 𝕜) 0 with hN0 | hN0
  · left
    simp [hN0]
  · have : NeZero N := ⟨by rintro rfl; exact hN0 Nat.cast_zero⟩
    rcases k.val_add_one_eq_or with h | h
    · left
      rw [h, Nat.cast_add, Nat.cast_one, add_one_mul]
    · right
      calc
        ((k + 1).val : 𝕜) * (L / N) + L
          = (((k + 1).val : 𝕜) + N) * (L / N) := by
            rw [add_mul, (Nat.cast_commute N (L / N)).eq, div_mul_cancel₀ L hN0]
        _ = ((k.val : 𝕜) + 1) * (L / N) := by rw [← Nat.cast_add, h, Nat.cast_add, Nat.cast_one]
        _ = (k.val : 𝕜) * (L / N) + L / N := add_one_mul _ _

end ZMod

namespace Function

/-- Evaluating an `L`-periodic function at equally spaced points `s₀ + k.val * (L / N)` indexed by
`k : ZMod N` advances the argument by `L / N` when `k` steps to `k + 1`. -/
theorem Periodic.apply_add_val_add_one_mul_div {α β : Type*} [DivisionSemiring α] {f : α → β}
    {L : α} (hf : Periodic f L) {N : ℕ} (s₀ : α) (k : ZMod N) :
    f (s₀ + ((k + 1).val : α) * (L / N)) = f (s₀ + (k.val : α) * (L / N) + L / N) := by
  rcases k.val_add_one_mul_div_eq_or L with h | h
  · rw [h, add_assoc]
  · rw [← hf (s₀ + ((k + 1).val : α) * (L / N)), add_assoc s₀, h, ← add_assoc]

/-- Evaluating an `L`-periodic function at equally spaced points `s₀ + k.val * (L / N)` indexed by
`k : ZMod N` shifts the argument by `-L / N` when `k` steps to `k - 1`. -/
theorem Periodic.apply_add_val_sub_one_mul_div {α β : Type*} [DivisionRing α] {f : α → β}
    {L : α} (hf : Periodic f L) {N : ℕ} (s₀ : α) (k : ZMod N) :
    f (s₀ + ((k - 1).val : α) * (L / N)) = f (s₀ + (k.val : α) * (L / N) - L / N) := by
  rcases (k - 1).val_add_one_mul_div_eq_or L with h | h
  · rw [sub_add_cancel] at h
    rw [h, ← add_assoc, add_sub_cancel_right]
  · rw [sub_add_cancel] at h
    have hsub : (s₀ + (k.val : α) * (L / N) - L / N) + L =
        s₀ + ((k - 1).val : α) * (L / N) := by
      rw [sub_add_eq_add_sub, add_assoc s₀, h, ← add_assoc, add_sub_cancel_right]
    rw [← hsub, hf]

end Function
