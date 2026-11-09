/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differentiable maps with constant derivative in one direction

If a differentiable map `f` has the same derivative `w` in the direction `v` at every point,
then it moves along every line `t ↦ p + t • v` by the affine amount `t • w`.
-/

public section

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A differentiable map whose derivative in the direction `v` is `w` at every point satisfies
`f (p + t • v) = f p + t • w`. -/
theorem apply_add_smul_eq_of_fderiv_apply_eq {f : E → F} (hf : Differentiable ℝ f) {v : E} {w : F}
    (hd : ∀ q, fderiv ℝ f q v = w) (p : E) (t : ℝ) : f (p + t • v) = f p + t • w := by
  have hl (s : ℝ) : HasDerivAt (fun s : ℝ => f (p + s • v) - s • w) 0 s := by
    have hc : HasDerivAt (fun s : ℝ => p + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add p
    have := ((hf (p + s • v)).hasFDerivAt.comp_hasDerivAt s hc).sub
      ((hasDerivAt_id s).smul_const w)
    simp only [hd, id_eq, one_smul, sub_self] at this
    exact this
  have h := is_const_of_deriv_eq_zero (fun s => (hl s).differentiableAt)
    (fun s => (hl s).deriv) t 0
  simp only [zero_smul, add_zero, sub_zero] at h
  rw [sub_eq_iff_eq_add] at h
  exact h

end TauCeti
