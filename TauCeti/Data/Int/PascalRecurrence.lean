/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Lift

/-!
# Uniqueness for the two-variable Pascal recurrence on `ℤ`

An additive-monoid-valued function `D : ℤ → ℤ → ℤ → G` satisfying the Pascal-type recurrence

`D (p + 1) q s = D p q (s + 1) + D p (q + 1) s`

and vanishing on the two coordinate planes `p = 0` and `q = 0` vanishes identically on `ℤ × ℤ × ℤ`.
Starting from `p = 0` and `q = 0`, upward induction on `p : ℕ` and `q : ℕ` covers the nonnegative
quadrant, while downward induction on `-p : ℕ` and `-q : ℕ` using `D (p + 1) q (s - 1) = ...`
covers negative indices.

## Main results

* `TauCeti.eq_zero_of_pascal_recurrence`: uniqueness of the zero solution to the Pascal
  recurrence on `ℤ × ℤ × ℤ` vanishing on both coordinate planes.
-/

public section

namespace TauCeti

/-- An additive-group- or monoid-valued function on `ℤ × ℤ × ℤ` satisfying the Pascal recurrence
`D (p + 1) q s = D p q (s + 1) + D p (q + 1) s` and vanishing on the two axes `p = 0` and `q = 0`
vanishes everywhere. -/
theorem eq_zero_of_pascal_recurrence {G : Type*} [AddZeroClass G] (D : ℤ → ℤ → ℤ → G)
    (hrec : ∀ p q s : ℤ, D (p + 1) q s = D p q (s + 1) + D p (q + 1) s)
    (h0n : ∀ q s : ℤ, D 0 q s = 0) (hm0 : ∀ p s : ℤ, D p 0 s = 0) (m n r : ℤ) :
    D m n r = 0 := by
  have hm0' (k : ℕ) : ∀ q s : ℤ, D k q s = 0 := by
    induction k with
    | zero => exact h0n
    | succ k ih => exact fun q s ↦ by rw [Nat.cast_succ, hrec, ih, ih, add_zero]
  have hn0' (l : ℕ) : ∀ p s : ℤ, D p l s = 0 := by
    induction l with
    | zero => exact hm0
    | succ l ih =>
      intro p s
      have h' := hrec p l s
      rw [ih (p + 1) s, ih p (s + 1), zero_add, eq_comm] at h'
      simpa [Nat.cast_succ] using h'
  have hneg (k : ℕ) : ∀ (l : ℕ) (s : ℤ), D (-(k : ℤ)) (-(l : ℤ)) s = 0 := by
    induction k with
    | zero => exact fun l s ↦ by simpa using h0n _ s
    | succ k ihk =>
      intro l
      induction l with
      | zero => exact fun s ↦ by simpa using hm0 _ s
      | succ l ihl =>
        intro s
        have h' := hrec (-((k + 1 : ℕ) : ℤ)) (-((l + 1 : ℕ) : ℤ)) (s - 1)
        have hk : -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) := by omega
        have hl : -((l + 1 : ℕ) : ℤ) + 1 = -(l : ℤ) := by omega
        rw [hk, hl, sub_add_cancel, ihk (l + 1) (s - 1), ihl (s - 1), add_zero] at h'
        exact h'.symm
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    exact hm0' m n r
  rcases le_or_gt 0 n with hn | hn
  · lift n to ℕ using hn
    exact hn0' n m r
  have hm' : -((-m).toNat : ℤ) = m := by omega
  have hn' : -((-n).toNat : ℤ) = n := by omega
  simpa only [hm', hn'] using hneg (-m).toNat (-n).toNat r

end TauCeti
