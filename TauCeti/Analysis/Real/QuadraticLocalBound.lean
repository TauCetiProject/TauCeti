/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A real-variable contradiction from a local quadratic bound

If `δ ^ 2 * V * c ≤ I + 2 * A * c ^ 2 * δ ^ 2 * (δ ^ 2 * V)` holds for all `0 < δ ≤ ε`, with
`c, ε > 0` and `A ≥ 0`, then `4 * A * c * ε ^ 2 > 1` is incompatible with `8 * A * I < V`: take
`δ ^ 2 = 1 / (4 * A * c)`. This is the final step of the mean-value inequality for
`Δ w ≥ -A w ^ 2`.
-/

public section

namespace TauCeti

/-- **The kernel of the contradiction.** If `δ ^ 2 V c ≤ I + 2 A c ^ 2 δ ^ 2 (δ ^ 2 V)` for all
`0 < δ ≤ ε`, with `c, ε > 0` and `A ≥ 0`, then `4 A c ε ^ 2 > 1` is incompatible with
`8 A I < V`. -/
lemma false_of_quadratic_local_bound {V I A c ε : ℝ} (hA : 0 ≤ A) (hc : 0 < c)
    (hε : 0 < ε)
    (hloc : ∀ δ, 0 < δ → δ ≤ ε → δ ^ 2 * V * c ≤ I + 2 * A * c ^ 2 * δ ^ 2 * (δ ^ 2 * V))
    (hcase : 1 < 4 * A * c * ε ^ 2) (hsmall : 8 * A * I < V) : False := by
  have hApos : 0 < A := by
    by_contra h
    rw [le_antisymm (not_lt.mp h) hA] at hcase
    linarith
  set δ := Real.sqrt (1 / (4 * A * c))
  have hδ2 : δ ^ 2 = 1 / (4 * A * c) := Real.sq_sqrt (by positivity)
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδε : δ ≤ ε := by
    refine (pow_le_pow_iff_left₀ hδ.le hε.le two_ne_zero).mp ?_
    rw [hδ2, div_le_iff₀ (by positivity), mul_comm (ε ^ 2)]
    exact hcase.le
  have hAcδ : 4 * A * c * δ ^ 2 = 1 := by
    rw [hδ2]; field_simp
  have h := hloc δ hδ hδε
  have hhalf : 2 * A * c ^ 2 * δ ^ 2 * (δ ^ 2 * V) = δ ^ 2 * V * c / 2 := by
    linear_combination (δ ^ 2 * V * c / 2) * hAcδ
  have _ : δ ^ 2 * V * c ≤ 2 * I := by linarith
  have h3 : V ≤ 8 * A * I := by
    have : δ ^ 2 * V * c * (4 * A) = V := by linear_combination V * hAcδ
    nlinarith
  linarith

end TauCeti
