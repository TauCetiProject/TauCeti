/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Lipschitz smoothness

A function `f : E → F` between normed vector spaces over a nontrivially normed field `𝕜` is
**`K`-smooth** if it is Fréchet differentiable and its first-order Taylor remainder is bounded
quadratically:

`‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2`.

For a real function this gives the two quadratic bounds
`f x + fderiv ℝ f x (y - x) - K / 2 * dist x y ^ 2 ≤ f y ≤
f x + fderiv ℝ f x (y - x) + K / 2 * dist x y ^ 2`, and on a Hilbert space the derivative term is
`⟪∇ f x, y - x⟫`.

This file is vendored from Christoph Spiegel's Mathlib pull request
[mathlib4#39574](https://github.com/leanprover-community/mathlib4/pull/39574), with its names and
field names, restricted to the global notion.

## Main declarations

* `LipschitzSmoothWith`: `K`-smoothness of a function between normed spaces.
* `LipschitzSmoothWith.fderiv_descent_le`, `LipschitzSmoothWith.fderiv_descent_ge`: the quadratic
  upper and lower bounds for a real function.
* `lipschitzSmoothWith_iff_inner_gradient`: the gradient form of the definition on a Hilbert space.
-/

public section

section Definitions

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜) in
/-- A function `f : E → F` is **`K`-smooth** if it is Fréchet differentiable and its
first-order Taylor remainder is bounded by `K / 2 * dist x y ^ 2` for all `x` and `y`. The factor
`1 / 2` is the normalization of the real case: for a function between real normed spaces, a
`K`-Lipschitz derivative gives a remainder of at most `K / 2 * dist x y ^ 2`. -/
structure LipschitzSmoothWith (K : NNReal) (f : E → F) : Prop where
  differentiable : Differentiable 𝕜 f
  fderiv_norm_le : ∀ x y,
    ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2

/-- Construct Lipschitz smoothness using a specified Fréchet derivative. -/
theorem LipschitzSmoothWith.of_hasFDerivAt {K : NNReal} {f : E → F}
    {f' : E → E →L[𝕜] F} (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hbound : ∀ x y, ‖f y - f x - f' x (y - x)‖ ≤ K / 2 * dist x y ^ 2) :
    LipschitzSmoothWith 𝕜 K f :=
  ⟨fun x ↦ (hf x).differentiableAt, fun x y ↦ by
    rw [(hf x).fderiv]
    exact hbound x y⟩

end Definitions

namespace LipschitzSmoothWith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : NNReal} {f : E → ℝ}

/-- The quadratic upper bound on `f y`, traditionally called the *descent lemma*. -/
theorem fderiv_descent_le (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    f y ≤ f x + fderiv ℝ f x (y - x) + K / 2 * dist x y ^ 2 := by
  linarith [(abs_le.mp (h.fderiv_norm_le x y)).2]

/-- The quadratic lower bound on `f y`, sometimes referred to as the *ascent lemma*. -/
theorem fderiv_descent_ge (h : LipschitzSmoothWith ℝ K f) (x y : E) :
    f x + fderiv ℝ f x (y - x) - K / 2 * dist x y ^ 2 ≤ f y := by
  linarith [(abs_le.mp (h.fderiv_norm_le x y)).1]

end LipschitzSmoothWith

section Gradient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ}

open scoped Gradient RealInnerProductSpace

/-- On a Hilbert space, `K`-smoothness of a real function is differentiability together with the
bound `‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2`. -/
theorem lipschitzSmoothWith_iff_inner_gradient :
    LipschitzSmoothWith ℝ K f ↔ Differentiable ℝ f ∧
      ∀ x y : F, ‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  constructor <;>
    exact fun ⟨hf, hbound⟩ ↦ ⟨hf, by
      simpa only [inner_gradient_left, dist_eq_norm'] using hbound⟩

end Gradient
