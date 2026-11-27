/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Truncated weights and their logarithmic gradients

For a nonnegative real weight `W` on a real normed space and `ε ≥ 0`, the truncation
`W / (1 + ε W)` is as smooth as `W` (`ContDiff.div_one_add_mul`). If `W` is positive and
differentiable at `z` with logarithmic gradient at most `g`, that is `‖dW z‖ ≤ g W z`, then its
truncation has logarithmic gradient at most `g` too (`norm_fderiv_div_one_add_mul_le`). A
logarithmic gradient at most `g ≤ |c|` gives the squared bound `‖dV z‖² ≤ c² V(z)²`
(`norm_fderiv_sq_le_of_norm_fderiv_le`), the form that enters weighted `L²` energy estimates.

The scalar bounds `0 ≤ w / (1 + ε w) ≤ min w (1 / ε)` are `TauCeti.div_one_add_mul_nonneg`,
`TauCeti.div_one_add_mul_le_self` and `TauCeti.div_one_add_mul_le_one_div`, in
`TauCeti.Algebra.Order.Field.Basic`.

## Main results

* `ContDiff.div_one_add_mul`: the truncation of a nonnegative `Cⁿ` weight is `Cⁿ`.
* `TauCeti.norm_fderiv_div_one_add_mul_le`: truncation keeps a bound on the logarithmic gradient.
* `TauCeti.norm_fderiv_sq_le_of_norm_fderiv_le`: a logarithmic gradient bound `g ≤ |c|` gives
  `‖dV z‖² ≤ c² V(z)²`.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonnegative weight whose logarithmic gradient at `z` is at most `g ≤ |c|` satisfies
`‖dV z‖² ≤ c² V(z)²`. For the radial exponential weight, `g = |c| ‖z‖ / √(b + ‖z‖²)`
(`norm_div_sqrt_add_norm_sq_le_one`). -/
theorem norm_fderiv_sq_le_of_norm_fderiv_le {V : E → ℝ} {z : E} {c g : ℝ}
    (hg : g ≤ |c|) (hV : 0 ≤ V z) (hdV : ‖fderiv ℝ V z‖ ≤ g * V z) :
    ‖fderiv ℝ V z‖ ^ 2 ≤ c ^ 2 * V z ^ 2 := by
  have h := hdV.trans (mul_le_mul_of_nonneg_right hg hV)
  simpa only [mul_pow, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The truncation `W / (1 + ε W)`, `ε ≥ 0`, of a nonnegative `Cⁿ` weight `W` is `Cⁿ`. -/
theorem _root_.ContDiff.div_one_add_mul {W : E → ℝ} {n : WithTop ℕ∞}
    (hW : ContDiff ℝ n W) (hW₀ : ∀ z, 0 ≤ W z) {ε : ℝ} (hε : 0 ≤ ε) :
    ContDiff ℝ n fun z ↦ W z / (1 + ε * W z) :=
  hW.div (contDiff_const.add (contDiff_const.mul hW)) fun z ↦ by have := hW₀ z; positivity

/-- **Truncation keeps a bound on the logarithmic gradient.** If a positive weight `W`,
differentiable at `z`, satisfies `‖dW z‖ ≤ g W z`, then so does its truncation `W / (1 + ε W)`,
`ε ≥ 0`: `‖d(W / (1 + ε W)) z‖ ≤ g W z / (1 + ε W z)`. -/
theorem norm_fderiv_div_one_add_mul_le {W : E → ℝ} {z : E}
    (hW : DifferentiableAt ℝ W z) (hW₀ : 0 < W z) {ε : ℝ} (hε : 0 ≤ ε) {g : ℝ}
    (hdW : ‖fderiv ℝ W z‖ ≤ g * W z) :
    ‖fderiv ℝ (fun t ↦ W t / (1 + ε * W t)) z‖ ≤ g * (W z / (1 + ε * W z)) := by
  have hd : 0 < 1 + ε * W z := by positivity
  have hg : 0 ≤ g := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hdW) hW₀
  -- `W / (1 + ε W)` is `W` composed with `s ↦ s / (1 + ε s)`, of derivative `1 / (1 + ε s)²`.
  have hs : HasDerivAt (fun s : ℝ ↦ s / (1 + ε * s)) (1 / (1 + ε * W z) ^ 2) (W z) := by
    have h := (hasDerivAt_id' (W z)).div (((hasDerivAt_id' (W z)).const_mul ε).const_add 1)
      hd.ne'
    convert h using 1
    field_simp
    ring
  have hVd : HasFDerivAt (fun t ↦ W t / (1 + ε * W t))
      ((1 / (1 + ε * W z) ^ 2) • fderiv ℝ W z) z := hs.comp_hasFDerivAt z hW.hasFDerivAt
  rw [hVd.fderiv, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc 1 / (1 + ε * W z) ^ 2 * ‖fderiv ℝ W z‖ ≤ 1 / (1 + ε * W z) ^ 2 * (g * W z) := by gcongr
    _ = g * (W z / (1 + ε * W z)) * (1 / (1 + ε * W z)) := by field_simp
    _ ≤ g * (W z / (1 + ε * W z)) := by
      refine mul_le_of_le_one_right (by positivity) ?_
      rw [div_le_one hd]
      nlinarith [mul_nonneg hε hW₀.le]

end TauCeti
