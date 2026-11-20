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
from it with `c ≠ 0`.  Mathlib supplies the easy direction (`ContDiffOn.exp`,
`ContinuousOn.rexp`); the converse recovers `g` as `c⁻¹ log (e^{c g})`.  This file packages both
directions as equivalences.

## Main declarations

* `TauCeti.contDiffOn_exp_const_mul_iff`: for a single `c ≠ 0`, `t ↦ e^{c g(t)}` is smooth on a
  set exactly when `g` is.
* `TauCeti.continuousOn_exp_const_mul_iff`: the same for continuity.
-/

public section

namespace TauCeti

/-- For `c ≠ 0`, the exponential `t ↦ e^{c g(t)}` of a real-valued function is smooth on a set
exactly when `g` is.  The converse direction composes with `Real.log`: the exponential is
positive, so this stays inside the domain of smoothness of the logarithm, and `Real.log_exp`
recovers `g` on the nose. -/
theorem contDiffOn_exp_const_mul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {c : ℝ} (hc : c ≠ 0) {g : E → ℝ} {s : Set E} :
    ContDiffOn ℝ n (fun t => Real.exp (c * g t)) s ↔ ContDiffOn ℝ n g s := by
  refine ⟨fun h => ?_, fun h => (contDiffOn_const.mul h).exp⟩
  have hlog : ContDiffOn ℝ n (fun t => c⁻¹ * Real.log (Real.exp (c * g t))) s :=
    (h.log fun t _ => (Real.exp_pos _).ne').const_smul c⁻¹
  exact hlog.congr fun t _ => by simp only [Real.log_exp, inv_mul_cancel_left₀ hc]

/-- For `c ≠ 0`, the exponential `t ↦ e^{c g(t)}` of a real-valued function is continuous on a
set exactly when `g` is. -/
theorem continuousOn_exp_const_mul_iff {α : Type*} [TopologicalSpace α] {c : ℝ} (hc : c ≠ 0)
    {g : α → ℝ} {s : Set α} :
    ContinuousOn (fun t => Real.exp (c * g t)) s ↔ ContinuousOn g s := by
  refine ⟨fun h => ?_, fun h => (continuousOn_const.mul h).rexp⟩
  have hlog : ContinuousOn (fun t => c⁻¹ * Real.log (Real.exp (c * g t))) s :=
    continuousOn_const.mul (h.log fun t _ => (Real.exp_pos _).ne')
  exact hlog.congr fun t _ => by simp only [Real.log_exp, inv_mul_cancel_left₀ hc]

end TauCeti
