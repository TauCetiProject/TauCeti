/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.RCLike.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differentiable maps with constant derivative in one direction

If a differentiable map `f` has the same derivative `w` in the direction `v` at every point,
then it moves along every line `t ↦ p + t • v` by the affine amount `t • w`; this holds over
`ℝ` and `ℂ` (any `RCLike` field). For a function of one variable, taking `v = 1` says that a
function whose `deriv` is constant is affine. Dually, a map which is even along a real line has
zero derivative in that direction.
-/

public section

namespace TauCeti

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A differentiable map whose derivative in the direction `v` is `w` at every point satisfies
`f (p + t • v) = f p + t • w`. -/
theorem apply_add_smul_eq_of_fderiv_apply_eq {f : E → F} (hf : Differentiable 𝕜 f) {v : E} {w : F}
    (hd : ∀ q, fderiv 𝕜 f q v = w) (p : E) (t : 𝕜) : f (p + t • v) = f p + t • w := by
  have hl (s : 𝕜) : HasDerivAt (fun s : 𝕜 => f (p + s • v) - s • w) 0 s := by
    have hc : HasDerivAt (fun s : 𝕜 => p + s • v) v s := by
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

end RCLike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of a function in a direction along which it is even vanishes: the function
`t ↦ f (x + t • v)` has the same value at `t` and `-t`. If `f` is not differentiable at `x`, then
`fderiv` is zero by convention. -/
theorem fderiv_apply_eq_zero_of_apply_add_smul_neg {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → G} {x : E} (v : E)
    (h : ∀ t : ℝ, f (x + t • v) = f (x + (-t) • v)) : fderiv ℝ f x v = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have h1 : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have h2 := (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)).deriv
    have h3 := deriv_comp_neg (f := fun s : ℝ ↦ f (x + s • v)) (x := (0 : ℝ))
    simp only [neg_zero, ← h] at h3
    simp only [Function.comp_def] at h2
    rw [← h2]
    -- `d = -d` in a real vector space forces `d = 0`.
    have h4 : (2 : ℝ) • deriv (fun s : ℝ ↦ f (x + s • v)) 0 = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h3]
      exact neg_add_cancel _
    exact (smul_eq_zero.1 h4).resolve_left two_ne_zero
  · rw [fderiv_zero_of_not_differentiableAt hd]
    simp

end TauCeti
