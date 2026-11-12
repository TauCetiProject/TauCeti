/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.RectangleComparison
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# A continuous field beyond the full `C¹` hypothesis

On the unit square, `P(x,y) = |x - 1/2|` and `Q(x,y) = x` satisfy the two directional
hypotheses with `∂y P = 0` and `∂x Q = 1`. The independent-division Green theorem supplies
both gauge integrabilities and the circulation-area identity. The field is not differentiable
at the midpoint of the square.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green.Examples

/-- The directional theorem applies to a continuous field with a transverse corner. Both
gauge components are integrable, and its circulation and the area integral are one. -/
theorem green_abs_unitSquare :
    let D := verticalRegion 0 1 (fun _ ↦ 0) (fun _ ↦ 1)
    let C := (Division.rectangleRe 0 1 0 1 zero_lt_one zero_lt_one).boundary
    BoundaryChain.Integrable Complex.reCLM (fun z ↦ |z.re - 1 / 2|) C ∧
      BoundaryChain.Integrable Complex.imCLM Complex.re C ∧
      IntegrableOn (fun _ : ℂ ↦ (1 : ℝ)) D ∧
      BoundaryChain.integral Complex.reCLM (fun z ↦ |z.re - 1 / 2|) C +
        BoundaryChain.integral Complex.imCLM Complex.re C = 1 ∧
      (∫ _ : ℂ in D, (1 : ℝ)) = 1 := by
  let V := Division.rectangleRe 0 1 0 1 zero_lt_one zero_lt_one
  let H := Division.rectangleIm 0 1 0 1 zero_lt_one zero_lt_one
  have hP : Continuous (fun z : ℂ ↦ |z.re - 1 / 2|) := by fun_prop
  have hQ : Continuous (Complex.re : ℂ → ℝ) := Complex.continuous_re
  have hV : BoundaryChain.NullChain .re univ (V.boundary - V.boundary) := by
    rw [sub_self]
    exact .zero
  have hH : BoundaryChain.NullChain .im univ (H.boundary - V.boundary) := by
    rw [Division.boundary_rectangleRe_eq_rectangleIm, sub_self]
    exact .zero
  have hg := Division.integrable_and_integral_add_integral_eq_integral_sub
    V H hV hH (subset_univ _) hP.continuousOn hQ.continuousOn
    (RP := fun _ ↦ 0) (RQ := fun _ ↦ 1)
    (fun _ _ x _ y _ ↦ hasDerivAt_const y |x - 1 / 2|)
    (fun _ _ _ _ x _ ↦ hasDerivAt_id x)
    (fun _ _ ↦ integrableOn_zero)
    (fun K _ ↦ continuousOn_const.integrableOn_compact (K.isCompact_region .im))
  have hb := integral_rectangle_boundary zero_lt_one zero_lt_one
    hP.continuousOn hQ.continuousOn
  have hvalue : BoundaryChain.integral Complex.reCLM (fun z ↦ |z.re - 1 / 2|) V.boundary +
      BoundaryChain.integral Complex.imCLM Complex.re V.boundary = 1 := by
    simpa [V] using hb.2.2
  simp only [sub_zero] at hg
  exact ⟨hg.1, hg.2.1, hg.2.2.1, hvalue, hg.2.2.2.symm.trans hvalue⟩

/-- The first coefficient in the preceding Green example fails to be differentiable at an
interior point, so the example does not arise from the full `C¹` theorem. -/
theorem not_differentiableAt_abs_re_midpoint :
    ¬ DifferentiableAt ℝ (fun z : ℂ ↦ |z.re - 1 / 2|) ⟨1 / 2, 1 / 2⟩ := by
  intro h
  have hl : DifferentiableAt ℝ (fun t : ℝ ↦ (t : ℂ) + ⟨1 / 2, 1 / 2⟩) 0 :=
    Complex.ofRealCLM.differentiableAt.add_const _
  have h' : DifferentiableAt ℝ (fun z : ℂ ↦ |z.re - 1 / 2|)
      ((0 : ℂ) + ⟨1 / 2, 1 / 2⟩) := by simpa using h
  apply not_differentiableAt_abs_zero
  simpa only [Function.comp_def, Complex.add_re, Complex.ofReal_re, add_sub_cancel_right] using
    h'.comp 0 hl

end TauCeti.Green.Examples
