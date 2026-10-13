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
prime-discriminant theory: the base case `1`, accessors for the two branches of the
characterization `Int.isFundamentalDiscr_iff_squarefree`, and the fact that a fundamental
discriminant other than `1` is not a rational square.

## Main results

* `Int.isFundamentalDiscr_one`: `1`, the discriminant of `ℚ`, is a fundamental discriminant.
* `Int.IsFundamentalDiscr.squarefree_of_emod_four_eq_one`,
  `Int.IsFundamentalDiscr.squarefree_div_four` and
  `Int.IsFundamentalDiscr.div_four_emod_four_eq_two_or_three`: accessors for the two branches of
  Mathlib's `Int.isFundamentalDiscr_iff_squarefree`.
* `Int.IsFundamentalDiscr.not_isSquare_rat`: a fundamental discriminant other than `1` is not a
  rational square, so `ℚ(√D)` is a genuine quadratic field.
-/

public section

namespace Int

/-- The discriminant of `ℚ` itself. It is the empty product of prime discriminants, and the
degenerate case of the `D ≡ 1 (mod 4)` branch of `Int.isFundamentalDiscr_iff_squarefree`. -/
@[simp] theorem isFundamentalDiscr_one : IsFundamentalDiscr 1 :=
  isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨by norm_num, squarefree_one⟩)

/-- The first branch accessor: a fundamental discriminant that is `1` modulo `4` is squarefree. -/
theorem IsFundamentalDiscr.squarefree_of_emod_four_eq_one {D : ℤ}
    (hD : IsFundamentalDiscr D) (h : D % 4 = 1) : Squarefree D :=
  ((isFundamentalDiscr_iff_squarefree.mp hD).resolve_right fun h' => by omega).2

/-- The second branch accessor: for a fundamental discriminant divisible by `4`, the quotient
`D / 4` is squarefree. -/
theorem IsFundamentalDiscr.squarefree_div_four {D : ℤ}
    (hD : IsFundamentalDiscr D) (h : D % 4 = 0) : Squarefree (D / 4) :=
  ((isFundamentalDiscr_iff_squarefree.mp hD).resolve_left fun h' => by omega).2.1

/-- The second branch accessor: for a fundamental discriminant divisible by `4`, the quotient
`D / 4` is `2` or `3` modulo `4`. -/
theorem IsFundamentalDiscr.div_four_emod_four_eq_two_or_three {D : ℤ}
    (hD : IsFundamentalDiscr D) (h : D % 4 = 0) : D / 4 % 4 = 2 ∨ D / 4 % 4 = 3 :=
  ((isFundamentalDiscr_iff_squarefree.mp hD).resolve_left fun h' => by omega).2.2

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
