/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Recovering a function from one of its exponentials

`Real.exp` is a smooth bijection onto `(0, ∞)` whose inverse `Real.log` is smooth there, so a
real-valued function `g` is exactly as regular as any single exponential `t ↦ e^{c g(t)}` built
from it with `c ≠ 0`.  Mathlib supplies the easy direction (`ContDiffOn.exp`, `Continuous.exp`);
this file records the converse, which recovers `g` as `c⁻¹ log (e^{c g})`.

## Main declarations

* `TauCeti.contDiffOn_of_contDiffOn_exp_const_mul`: smoothness of `g` on a set follows from
  smoothness of `t ↦ e^{c g(t)}` there, for a single `c ≠ 0`.
* `TauCeti.continuousOn_of_continuousOn_exp_const_mul`: the same for continuity.
-/

public section

namespace TauCeti

/-- A real-valued function is smooth on a set as soon as one of its exponentials
`t ↦ e^{c g(t)}`, `c ≠ 0`, is: the exponential is positive, so composing with `Real.log` stays
inside the domain of smoothness of the logarithm, and `Real.log_exp` recovers `g` on the nose. -/
theorem contDiffOn_of_contDiffOn_exp_const_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : WithTop ℕ∞} {c : ℝ} (hc : c ≠ 0) {g : E → ℝ} {s : Set E}
    (h : ContDiffOn ℝ n (fun t => Real.exp (c * g t)) s) : ContDiffOn ℝ n g s := by
  have hlog : ContDiffOn ℝ n (fun t => c⁻¹ * Real.log (Real.exp (c * g t))) s :=
    (h.log fun t _ => (Real.exp_pos _).ne').const_smul c⁻¹
  refine hlog.congr fun t _ => ?_
  simp only [Real.log_exp]
  field_simp

/-- A real-valued function is continuous on a set as soon as one of its exponentials
`t ↦ e^{c g(t)}`, `c ≠ 0`, is. -/
theorem continuousOn_of_continuousOn_exp_const_mul {α : Type*} [TopologicalSpace α] {c : ℝ}
    (hc : c ≠ 0) {g : α → ℝ} {s : Set α}
    (h : ContinuousOn (fun t => Real.exp (c * g t)) s) : ContinuousOn g s := by
  have hlog : ContinuousOn (fun t => c⁻¹ * Real.log (Real.exp (c * g t))) s :=
    continuousOn_const.mul (h.log fun t _ => (Real.exp_pos _).ne')
  refine hlog.congr fun t _ => ?_
  simp only [Real.log_exp]
  field_simp

end TauCeti
