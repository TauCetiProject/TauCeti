/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.Circle
public import TauCeti.Dynamics.Billiard.InvariantGraph.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The Lipschitz bound for invariant graphs on the circular table: checks

Checks for `TauCeti.StrictConvexBilliardTable.IsInvariantGraph.lipschitzWith_of_forall_le` on the
circular table of radius `R` (`TauCeti.StrictConvexBilliardTable.circle`).

* The slope of the image of the vertical through `(s, v)` is `∂_v w / ∂_v t = -√(1 - v²) / (2 R)`,
  since `w(s, v) = v` and `t(s, v) = s + 2 R arccos v`; its absolute value is at most `1 / (2 R)`.
* So the bound of the theorem shows that the constant graphs are `1 / (2 R)`-Lipschitz, a nonsharp
  bound for these constant functions.
-/

public section

noncomputable section

open Real Set Filter Topology TauCeti StrictConvexBilliardTable

namespace TauCeti.Examples.InvariantGraphLipschitz

attribute [local instance] Complex.finrank_real_complex_fact

variable {R : ℝ}

/-- On the circular table the image of the vertical through `(s, v)` has slope
`-√(1 - v²) / (2 R)` at `B(s, v)`. -/
theorem verticalImageSlope_circle (hR : 0 < R) (s : ℝ) {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    (circle hR).verticalImageSlope s v = -√(1 - v ^ 2) / (2 * R) := by
  have hnhds := Ioo_mem_nhds hv.1 hv.2
  have hT : (circle hR).nextParam s =ᶠ[𝓝 v] fun u ↦ s + 2 * R * arccos u :=
    eventuallyEq_of_mem hnhds fun u hu ↦ nextParam_circle hu s
  have hW : (circle hR).nextTangential s =ᶠ[𝓝 v] id :=
    eventuallyEq_of_mem hnhds fun u hu ↦ nextTangential_circle hu s
  have hsq : 0 < √(1 - v ^ 2) := sqrt_pos.2 (by nlinarith [hv.1, hv.2])
  rw [verticalImageSlope_def, hT.deriv_eq, hW.deriv_eq, deriv_id, deriv_const_add,
    deriv_const_mul _ (differentiableAt_arccos.2 ⟨hv.1.ne', hv.2.ne⟩), deriv_arccos]
  field_simp

/-- The slopes of the images of the verticals of the circular table are at least `-1 / (2 R)`. -/
theorem neg_le_verticalImageSlope_circle (hR : 0 < R) (s : ℝ) {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    -(1 / (2 * R)) ≤ (circle hR).verticalImageSlope s v := by
  rw [verticalImageSlope_circle hR s hv, neg_div, neg_le_neg_iff]
  gcongr
  exact sqrt_le_one.2 (by nlinarith)

/-- The constant graphs of the circular table are `1 / (2 R)`-Lipschitz by the bound of
`IsInvariantGraph.lipschitzWith_of_forall_le`. -/
theorem lipschitzWith_circle (hR : 0 < R) {c : ℝ} (hc : c ∈ Ioo (-1) 1) :
    LipschitzWith (1 / (2 * R)).toNNReal fun _ : ℝ ↦ c := by
  have hpos : 0 ≤ 1 / (2 * R) := by positivity
  refine (isInvariantGraph_circle hR hc).lipschitzWith_of_forall_le contDiff_circle (fun s ↦ ?_)
    (fun s ↦ ?_)
  · rw [coe_toNNReal _ hpos]
    exact neg_le_verticalImageSlope_circle hR s hc
  · rw [coe_toNNReal _ hpos]
    exact neg_le_verticalImageSlope_circle hR s ⟨neg_lt_neg hc.2, neg_lt.1 hc.1⟩

end TauCeti.Examples.InvariantGraphLipschitz
