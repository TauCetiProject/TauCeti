/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# The reciprocal of a Lipschitz function

If `f` takes values in a normed division ring, is `K`-Lipschitz on a set `s` and stays at norm at
least `m > 0` there, then `x ↦ (f x)⁻¹` is `K / m²`-Lipschitz on `s`, because
`dist a⁻¹ b⁻¹ = dist a b / (‖a‖ ‖b‖)` (`dist_inv_inv₀`). This is how a coefficient bounded below,
such as the normal component of a uniformly elliptic coefficient field, is divided out while
keeping Lipschitz control.

## Main results

* `LipschitzOnWith.inv_of_le_norm`: the reciprocal of a function Lipschitz on `s` and bounded away
  from zero there is Lipschitz on `s`.
-/

public section

open scoped NNReal

namespace LipschitzOnWith

variable {α 𝕜 : Type*} [PseudoMetricSpace α] [NormedDivisionRing 𝕜]

/-- The reciprocal of a `K`-Lipschitz function on `s` whose norm is at least `m > 0` on `s` is
`K / m²`-Lipschitz on `s`. -/
theorem inv_of_le_norm {f : α → 𝕜} {s : Set α} {K m : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hm : 0 < m) (hfm : ∀ x ∈ s, (m : ℝ) ≤ ‖f x‖) :
    LipschitzOnWith (K / m ^ 2) (fun x => (f x)⁻¹) s :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
    have hx' : (0 : ℝ) < ‖f x‖ := (NNReal.coe_pos.2 hm).trans_le (hfm x hx)
    have hy' : (0 : ℝ) < ‖f y‖ := (NNReal.coe_pos.2 hm).trans_le (hfm y hy)
    rw [dist_inv_inv₀ (norm_pos_iff.1 hx') (norm_pos_iff.1 hy'),
      div_le_iff₀ (mul_pos hx' hy')]
    calc dist (f x) (f y) ≤ K * dist x y := hf.dist_le_mul x hx y hy
      _ = K / m ^ 2 * dist x y * (m * m) := by
          field_simp [(NNReal.coe_pos.2 hm).ne']
      _ ≤ (K / m ^ 2 : ℝ≥0) * dist x y * (‖f x‖ * ‖f y‖) := by
          push_cast
          gcongr
          exacts [hfm x hx, hfm y hy]

end LipschitzOnWith
