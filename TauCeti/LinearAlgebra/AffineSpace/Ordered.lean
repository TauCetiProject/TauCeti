/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Interval.Set.Defs
public import TauCeti.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signs of affine functions on an interval

An affine function `g` on a linearly ordered field, positive at `a`, stays positive on `[a, b]`
until its first zero, and vanishes there only
(`AffineMap.exists_forall_pos_iff_lt_of_pos`).

## Main results

* `AffineMap.exists_forall_pos_iff_lt_of_pos`: the threshold `z > a` such that, on `[a, b]`, an
  affine function positive at `a` is positive exactly before `z` and vanishes exactly at `z`.
-/

public section

open Set

namespace AffineMap

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]

/-- **The first zero of an affine function.** If an affine function `g` on the line is positive
at `a < b`, there is a threshold `z > a`, lying in `(a, b]` exactly when `g b ≤ 0`, such that on
`[a, b]` the function is positive exactly before `z` and vanishes exactly at `z`. -/
theorem exists_forall_pos_iff_lt_of_pos (g : k →ᵃ[k] k) {a b : k} (hab : a < b) (hg : 0 < g a) :
    ∃ z, a < z ∧ (z ≤ b ↔ g b ≤ 0) ∧ ∀ s ∈ Icc a b, (0 < g s ↔ s < z) ∧ (g s = 0 ↔ s = z) := by
  -- `g` has constant slope `m`.
  obtain ⟨m, hgs⟩ : ∃ m, ∀ s, g s = g a + (s - a) * m :=
    ⟨g 1 - g 0, fun s ↦ by rw [g.apply_eq_add_mul_sub s, g.apply_eq_add_mul_sub a]; ring⟩
  rcases lt_or_ge m 0 with hm | hm
  · -- `g s = m * (s - z)` with `z = a - g a / m`.
    have hlin (s : k) : g s = m * (s - (a - g a / m)) := by
      have hm0 : m ≠ 0 := hm.ne
      rw [hgs s]
      field_simp
      ring
    refine ⟨a - g a / m, by linarith [div_neg_of_pos_of_neg hg hm], ?_, fun s _ ↦ ?_⟩
    · rw [hlin b]
      exact ⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩
    · rw [hlin s, mul_eq_zero, sub_eq_zero, or_iff_right hm.ne]
      exact ⟨⟨fun h ↦ by nlinarith, fun h ↦ by nlinarith⟩, Iff.rfl⟩
  · -- `g` does not decrease, so it stays positive.
    have hpos {s : k} (hs : a ≤ s) : 0 < g s := by
      rw [hgs]
      exact add_pos_of_pos_of_nonneg hg (mul_nonneg (sub_nonneg.2 hs) hm)
    refine ⟨b + 1, by linarith, ⟨fun h ↦ by linarith, fun h ↦ ?_⟩, fun s hs ↦ ?_⟩
    · exact absurd h (not_le.2 (hpos hab.le))
    · exact ⟨⟨fun _ ↦ by linarith [hs.2], fun _ ↦ hpos hs.1⟩,
        ⟨fun h ↦ ((hpos hs.1).ne' h).elim, fun h ↦ by linarith [hs.2]⟩⟩

end AffineMap
