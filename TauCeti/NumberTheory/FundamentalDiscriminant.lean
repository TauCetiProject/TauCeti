/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.FundamentalDiscriminant
import TauCeti.Algebra.Squarefree

/-!
# Fundamental discriminants: basic API

Generic facts about Mathlib's `Int.IsFundamentalDiscr`, independent of any quadratic-field or
prime-discriminant theory.

## Main results

* `Int.IsFundamentalDiscr.not_isSquare_rat`: a fundamental discriminant other than `1` is not a
  rational square, so `ℚ(√D)` is a genuine quadratic field.
-/

public section

namespace Int

/-- A fundamental discriminant other than `1` is not a rational square. Consequently `ℚ(√D)` is a
genuine quadratic field: this is what keeps the genus-field constructions non-degenerate. -/
theorem IsFundamentalDiscr.not_isSquare_rat {D : ℤ} (hD : IsFundamentalDiscr D)
    (h1 : D ≠ 1) : ¬ IsSquare ((D : ℤ) : ℚ) := by
  rcases isFundamentalDiscr_iff_squarefree.mp hD with ⟨-, hsf⟩ | ⟨h0, hmsf, hm4⟩
  · exact not_isSquare_intCast_of_squarefree_of_ne_one hsf h1
  · obtain ⟨m, rfl⟩ : (4 : ℤ) ∣ D := Int.dvd_of_emod_eq_zero h0
    rw [Int.mul_ediv_cancel_left m four_ne_zero] at hmsf hm4
    have hm1 : m ≠ 1 := by rcases hm4 with h | h <;> omega
    have hcast : ((4 * m : ℤ) : ℚ) = 4 * ((m : ℤ) : ℚ) := by push_cast; ring
    rw [hcast]
    exact fun h => not_isSquare_intCast_of_squarefree_of_ne_one hmsf hm1
      (by simpa using h.div (⟨2, by norm_num⟩ : IsSquare (4 : ℚ)))

end Int
