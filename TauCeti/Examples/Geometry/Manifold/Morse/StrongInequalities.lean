/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Polynomial.AlternatingSum
import TauCeti.Geometry.Manifold.Morse.Polynomial

/-!
# Examples: the weak Morse inequalities and Euler's equality do not imply the strong ones

Let `cⱼ` count the critical points of index `j` of a Morse function on a compact manifold `M`,
and let `bⱼ` be the Betti numbers of `M` over a division ring. The weak Morse inequalities
`bⱼ ≤ cⱼ` and Euler's equality `∑ (-1)ʲ bⱼ = ∑ (-1)ʲ cⱼ` are both consequences of the strong
inequalities `bₙ - bₙ₋₁ + ⋯ ± b₀ ≤ cₙ - cₙ₋₁ + ⋯ ± c₀`, but together they do not imply them.

The candidate counts `c = (2, 0, 0, 2)` and Betti numbers `b = (1, 0, 0, 1)`, the Betti numbers of
`S³`, satisfy the weak inequalities and have equal alternating sums `0`. The strong inequality
holds for them in degrees `0`, `2` and `3`, but in degree `1` it reads `-1 ≤ -2`, which fails. So
no polynomial `Q` with natural number coefficients gives
`2 + 2t³ = (1 + t³) + (1 + t) Q(t)`, by the polynomial form of the strong inequalities
(`Polynomial.exists_sum_range_monomial_eq_add_one_add_X_mul_iff`), and no Morse function on a
compact manifold has these critical counts and Betti numbers, by the Morse polynomial identity
(`TauCeti.morse_inequalities`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

open Finset Module Polynomial
open scoped ContDiff Manifold

universe u

namespace TauCeti.Examples.MorseStrongInequalities

-- The candidate counts `c = (2, 0, 0, 2)` and Betti numbers `b = (1, 0, 0, 1)` are written as
-- the lists `[2, 0, 0, 2]` and `[1, 0, 0, 1]`, extended by zero.

/-- The weak Morse inequalities `bⱼ ≤ cⱼ` hold in every degree. -/
example (j : ℕ) : [1, 0, 0, 1].getD j 0 ≤ [2, 0, 0, 2].getD j 0 := by
  rcases j with _ | _ | _ | _ | j <;> simp

/-- Euler's equality holds: both alternating sums vanish. -/
example : ∑ j ∈ range 4, (-1 : ℤ) ^ j * ([1, 0, 0, 1].getD j 0 : ℕ) =
    ∑ j ∈ range 4, (-1 : ℤ) ^ j * ([2, 0, 0, 2].getD j 0 : ℕ) := by
  simp [sum_range_succ]

/-- The strong Morse inequality holds in degrees `0`, `2` and `3`. -/
example (n : ℕ) (hn : n = 0 ∨ n = 2 ∨ n = 3) :
    ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * ([1, 0, 0, 1].getD j 0 : ℕ) ≤
      ∑ j ∈ range (n + 1), (-1 : ℤ) ^ (n - j) * ([2, 0, 0, 2].getD j 0 : ℕ) := by
  rcases hn with rfl | rfl | rfl <;> simp [sum_range_succ]

/-- The strong Morse inequality fails in degree `1`: it reads `b₁ - b₀ = -1 ≤ -2 = c₁ - c₀`. -/
example : ¬∑ j ∈ range 2, (-1 : ℤ) ^ (1 - j) * ([1, 0, 0, 1].getD j 0 : ℕ) ≤
    ∑ j ∈ range 2, (-1 : ℤ) ^ (1 - j) * ([2, 0, 0, 2].getD j 0 : ℕ) := by
  simp [sum_range_succ]

/-- There is no polynomial `Q` with natural number coefficients such that
`2 + 2t³ = (1 + t³) + (1 + t) Q(t)`. -/
example : ¬∃ Q : ℕ[X], ∑ j ∈ range 4, monomial j ([2, 0, 0, 2].getD j 0) =
    ∑ j ∈ range 4, monomial j ([1, 0, 0, 1].getD j 0) + (1 + X) * Q := by
  rw [exists_sum_range_monomial_eq_add_one_add_X_mul_iff]
  rintro ⟨hstrong, -⟩
  simpa [sum_range_succ] using hstrong 1 (by norm_num)

/-- **No Morse function has these counts and Betti numbers.** On a compact boundaryless manifold,
over any division ring `k`, no Morse function has `cⱼ` critical points of index `j` while `M` has
Betti numbers `bⱼ`, for `c = (2, 0, 0, 2)` and `b = (1, 0, 0, 1)`. -/
example {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} (hf : IsMorse I f) (k : Type u) [DivisionRing k] :
    ¬∀ j, criticalCount I f j = ([2, 0, 0, 2].getD j 0 : ℕ) ∧
      bettiNumber k M j = [1, 0, 0, 1].getD j 0 := by
  intro h
  obtain ⟨Q, hQ⟩ := morse_inequalities hf k
  -- In degree `0` the identity gives `Q₀ = c₀ - b₀ = 1`, and in degree `1` it gives
  -- `Q₁ + Q₀ = c₁ - b₁ = 0`.
  have h₀ := hQ 0
  have h₁ := hQ 1
  rw [(h 0).1, (h 0).2, Nat.cast_inj] at h₀
  rw [(h 1).1, (h 1).2, Nat.cast_inj] at h₁
  simp [add_mul, coeff_X_mul] at h₀ h₁
  omega

end TauCeti.Examples.MorseStrongInequalities
