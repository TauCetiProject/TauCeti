/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.SpecialFunctions.SmoothSegmentPath
import Mathlib.Tactic.Abel
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The smooth path along a segment in `L∞`

For points `x` and `y` in a real normed space and any measure `μ` on `ℝ`, the smooth path
`TauCeti.smoothSegmentPath x y` (`s ↦ x + ψ(s) (y - x)`) is essentially bounded and defines an
element `TauCeti.smoothSegmentPathL x y` of `L∞(μ)`. It depends `1`-Lipschitz on the endpoint `y`
(`TauCeti.lipschitzWith_smoothSegmentPathL`) and reduces to the constant class when `x = y`
(`TauCeti.smoothSegmentPathL_self`).

## Main declarations

* `TauCeti.memLp_smoothSegmentPath`: `TauCeti.smoothSegmentPath x y` belongs to `L∞(μ)`.
* `TauCeti.smoothSegmentPathL`: the `L∞(μ)` class of `TauCeti.smoothSegmentPath x y`.
* `TauCeti.smoothSegmentPathL_def`: definitional equation for `TauCeti.smoothSegmentPathL`.
* `TauCeti.coeFn_smoothSegmentPathL`: almost everywhere agreement with `TauCeti.smoothSegmentPath`.
* `TauCeti.smoothSegmentPathL_self`: normal form for equal endpoints.
* `TauCeti.lipschitzWith_smoothSegmentPathL`: `1`-Lipschitz dependence on the endpoint.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ}

/-- The smooth segment path `TauCeti.smoothSegmentPath x y` is essentially bounded. -/
theorem memLp_smoothSegmentPath (x y : E) : MemLp (smoothSegmentPath x y) ∞ μ := by
  refine memLp_top_of_bound ((contDiff_smoothSegmentPath (x := x) (y := y) (n := 0)).continuous
    |>.aestronglyMeasurable) (‖x‖ + ‖y - x‖) (ae_of_all _ fun s ↦ ?_)
  rw [smoothSegmentPath_def]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul, Real.norm_of_nonneg (Real.smoothTransition.nonneg s)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one s)

/-- The `L∞` class of `TauCeti.smoothSegmentPath x y`. -/
def smoothSegmentPathL (x y : E) : Lp E ∞ μ :=
  (memLp_smoothSegmentPath x y).toLp _

/-- Definitional equation for `TauCeti.smoothSegmentPathL`. -/
theorem smoothSegmentPathL_def (x y : E) :
    (smoothSegmentPathL x y : Lp E ∞ μ) = (memLp_smoothSegmentPath x y).toLp _ :=
  (rfl)

/-- `TauCeti.smoothSegmentPathL x y` agrees almost everywhere with
`TauCeti.smoothSegmentPath x y`. -/
theorem coeFn_smoothSegmentPathL (x y : E) :
    (smoothSegmentPathL x y : Lp E ∞ μ) =ᵐ[μ] smoothSegmentPath x y :=
  (memLp_smoothSegmentPath x y).coeFn_toLp

/-- When the endpoints coincide, `TauCeti.smoothSegmentPathL x x` is the constant class `x`. -/
@[simp]
theorem smoothSegmentPathL_self (x : E) :
    (smoothSegmentPathL x x : Lp E ∞ μ) = (memLp_top_const x).toLp (fun _ ↦ x) :=
  Lp.ext ((coeFn_smoothSegmentPathL x x).trans <|
    (Filter.EventuallyEq.of_eq (funext fun s ↦ smoothSegmentPath_self x s)).trans
      (memLp_top_const x).coeFn_toLp.symm)

/-- The `L∞` class `TauCeti.smoothSegmentPathL x` depends `1`-Lipschitz on the endpoint `y`. -/
theorem lipschitzWith_smoothSegmentPathL (x : E) :
    LipschitzWith 1 (smoothSegmentPathL (μ := μ) x) :=
  LipschitzWith.of_dist_le_mul fun y y' ↦ by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    refine Lp.norm_le_of_ae_bound_top (norm_nonneg _) ?_
    filter_upwards [Lp.coeFn_sub (smoothSegmentPathL x y) (smoothSegmentPathL x y'),
      coeFn_smoothSegmentPathL x y, coeFn_smoothSegmentPathL x y'] with s hs h h'
    rw [hs, Pi.sub_apply, h, h']
    have heq : smoothSegmentPath x y s - smoothSegmentPath x y' s =
        Real.smoothTransition s • (y - y') := by
      simp only [smoothSegmentPath_def, smul_sub]
      abel
    rw [heq, norm_smul, Real.norm_of_nonneg (Real.smoothTransition.nonneg s)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one s)

end TauCeti
