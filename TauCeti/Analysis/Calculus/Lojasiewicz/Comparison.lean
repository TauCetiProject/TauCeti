/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Comparing Łojasiewicz inequalities with exponent `1 / 2`

A Łojasiewicz inequality with exponent `1 / 2`, `lam * u ≤ g ^ 2` eventually along a filter,
survives replacing `g` by any quantity `h` that dominates a multiple of it. This carries the
inequality between coordinate systems, or from a differential to a gradient, whose norms are
comparable. The statement is elementary and needs none of the integration theory of the scalar
finite-length argument in `TauCeti.Analysis.Calculus.Lojasiewicz`.

## Main results

* `TauCeti.exists_mul_le_sq_of_eventually_le_mul`: a Łojasiewicz inequality with exponent `1 / 2`
  survives a bounded comparison of the quantities on its right-hand side.

## References

* S. Łojasiewicz, *Une propriété topologique des sous-ensembles analytiques réels*, Les Équations
  aux Dérivées Partielles, CNRS, Paris, 1963, 87–89.
-/

public section

namespace TauCeti

/-- **Łojasiewicz's inequality with exponent `1 / 2` survives a bounded comparison of slopes.** If
`lam * u y ≤ g y ^ 2` eventually along `l`, for some `lam > 0`, and `0 ≤ g y ≤ K * h y`
eventually, then `lam' * u y ≤ h y ^ 2` eventually, for some `lam' > 0`. This carries the
inequality between coordinate systems, or from a differential to a gradient, whose norms are
comparable. -/
theorem exists_mul_le_sq_of_eventually_le_mul {α : Type*} {l : Filter α} {u g h : α → ℝ} {K : ℝ}
    (hu : ∃ lam > 0, ∀ᶠ y in l, lam * u y ≤ g y ^ 2) (hg : ∀ᶠ y in l, 0 ≤ g y)
    (hgh : ∀ᶠ y in l, g y ≤ K * h y) :
    ∃ lam > 0, ∀ᶠ y in l, lam * u y ≤ h y ^ 2 := by
  obtain ⟨lam, hlam, hu⟩ := hu
  refine ⟨lam / (K ^ 2 + 1), by positivity, ?_⟩
  filter_upwards [hu, hg, hgh] with y hy hgy hghy
  have hK : 0 < K ^ 2 + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  calc lam * u y ≤ g y ^ 2 := hy
    _ ≤ (K * h y) ^ 2 := pow_le_pow_left₀ hgy hghy 2
    _ ≤ h y ^ 2 * (K ^ 2 + 1) := by nlinarith [sq_nonneg (h y)]

end TauCeti
