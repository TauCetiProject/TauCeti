/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Darboux

/-!
# Change of variables on an interval with a nonvanishing derivative

Mathlib's one-dimensional change of variables formula
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` asks for `f` to be injective on the set
of integration. On a convex subset `s` of `ℝ`, a derivative that never vanishes already forces
this: by Darboux's theorem the derivative has a constant sign on `s`, so `f` is strictly monotone
there. Hence the integral of `g` over `f '' s` is the integral of `|f'| • g ∘ f` over `s`
(`MeasureTheory.integral_image_eq_integral_abs_deriv_smul_of_ne_zero`). No continuity of the
derivative is needed.
-/

public section

open Set

namespace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set ℝ} {f f' : ℝ → ℝ}

/-- **Change of variables for a nonvanishing derivative.** If `f` has a nonvanishing derivative
`f'` within a convex set `s ⊆ ℝ` at each point of `s`, then the integral of `g` over `f '' s` is
the integral of `|f'| • g ∘ f` over `s`. -/
theorem integral_image_eq_integral_abs_deriv_smul_of_ne_zero (hs : Convex ℝ s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf'0 : ∀ x ∈ s, f' x ≠ 0) (g : ℝ → F) :
    ∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x) := by
  have hc : ContinuousOn f s := fun x hx ↦ (hf' x hx).continuousWithinAt
  have hi (x : ℝ) (hx : x ∈ interior s) : HasDerivWithinAt f (f' x) (interior s) x :=
    (hf' x (interior_subset hx)).mono interior_subset
  have hinj : InjOn f s := by
    rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne hs hf' hf'0 with hneg | hpos
    · exact (strictAntiOn_of_hasDerivWithinAt_neg hs hc hi
        fun x hx ↦ hneg x (interior_subset hx)).injOn
    · exact (strictMonoOn_of_hasDerivWithinAt_pos hs hc hi
        fun x hx ↦ hpos x (interior_subset hx)).injOn
  exact integral_image_eq_integral_abs_deriv_smul hs.ordConnected.measurableSet hf' hinj g

end MeasureTheory
