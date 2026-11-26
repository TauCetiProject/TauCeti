/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Int.Interval
import TauCeti.Algebra.Field.GeomSum
import TauCeti.Data.Int.Interval

/-!
# Centred geometric sums on the unit sphere

For `z` of norm `1` in a normed division ring, the centred geometric sum `∑_{j=-n}^{n} z^j` has its
`2 n + 1` terms on the unit sphere, so its norm is at most `2 n + 1`; as soon as `z ≠ 1` it is
bounded independently of `n`, by `2 / ‖1 - z‖`, since `(1 - z)` times it telescopes to
`z^{-n} - z^{n+1}`. For `z = e^{iθ}` it is the Dirichlet kernel `sin((n + 1/2) θ) / sin(θ / 2)`.
The bound uniform in `n` is what makes the root strings `∑_{j=-n}^{n} e^{j α}` of a character
small, after division by their length, at every nontrivial character of a finite group.

## Main results

* `TauCeti.norm_sum_Icc_zpow_le_two_mul_add_one`: `‖∑_{j=-n}^{n} z^j‖ ≤ 2 n + 1` for `‖z‖ = 1`.
* `TauCeti.norm_sum_Icc_zpow_le`: `‖∑_{j=-n}^{n} z^j‖ ≤ 2 / ‖1 - z‖` for `‖z‖ = 1` and `z ≠ 1`.
-/

public section

open Finset

namespace TauCeti

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {z : 𝕜}

/-- A centred geometric sum on the unit sphere has norm at most its number `2 n + 1` of terms. -/
theorem norm_sum_Icc_zpow_le_two_mul_add_one (hz : ‖z‖ = 1) (n : ℕ) :
    ‖∑ j ∈ Icc (-(n : ℤ)) n, z ^ j‖ ≤ 2 * n + 1 := by
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_zpow, hz, one_zpow, sum_const, Int.card_Icc_neg_natCast_natCast, nsmul_eq_mul,
    mul_one]
  push_cast
  exact le_rfl

/-- **A centred geometric sum on the unit sphere is bounded away from `1`**: for `‖z‖ = 1` and
`z ≠ 1`, `‖∑_{j=-n}^{n} z^j‖ ≤ 2 / ‖1 - z‖`, uniformly in `n`. -/
theorem norm_sum_Icc_zpow_le (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (n : ℕ) :
    ‖∑ j ∈ Icc (-(n : ℤ)) n, z ^ j‖ ≤ 2 / ‖1 - z‖ := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; exact one_ne_zero)
  have hpos : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1.symm)
  rw [le_div_iff₀ hpos, mul_comm, ← norm_mul, one_sub_mul_sum_Icc_zpow hz0]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_zpow, norm_pow, hz, one_zpow, one_pow]
  norm_num

end TauCeti
