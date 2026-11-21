/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Init

/-!
# Isometries of the integers

A map `f : ℤ → ℤ` preserving the distance `|m - n|` is a translation `n ↦ f 0 + n` or a
reflection `n ↦ f 0 - n`: the value `f 1` is `f 0 + 1` or `f 0 - 1`, and then `f n` is the only
integer at distance `|n|` from `f 0` and `|n - 1|` from `f 1`. Such maps occur as
reparametrizations of geodesic lines in graphs.

## Main results

* `Int.forall_eq_add_or_forall_eq_sub_of_natAbs_sub_eq`: an isometry of `ℤ` is a translation or a
  reflection.
-/

public section

namespace Int

/-- **Isometries of the integers.** A map `f : ℤ → ℤ` with `|f m - f n| = |m - n|` is the
translation `n ↦ f 0 + n` or the reflection `n ↦ f 0 - n`. -/
theorem forall_eq_add_or_forall_eq_sub_of_natAbs_sub_eq {f : ℤ → ℤ}
    (hf : ∀ m n, (f m - f n).natAbs = (m - n).natAbs) :
    (∀ n, f n = f 0 + n) ∨ ∀ n, f n = f 0 - n := by
  have h₁₀ := hf 1 0
  obtain h₁ | h₁ : f 1 - f 0 = 1 ∨ f 1 - f 0 = -1 := by omega
  · exact .inl fun n => by have := hf n 0; have := hf n 1; omega
  · exact .inr fun n => by have := hf n 0; have := hf n 1; omega

end Int
