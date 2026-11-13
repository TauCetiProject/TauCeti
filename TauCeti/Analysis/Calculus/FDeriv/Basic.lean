/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Differentiability criteria

The derivative `fderiv 𝕜 f` is totalized: it is `0` where `f` is not differentiable. So a
nonzero derivative certifies differentiability, as `differentiableAt_of_deriv_ne_zero` does for
functions of one variable. Likewise, two differentiable independent linear combinations of two
scalar functions recover both functions as differentiable.

## Main results

* `TauCeti.differentiableAt_of_fderiv_ne_zero`: a function is differentiable wherever its
  derivative does not vanish.
* `TauCeti.differentiableAt_and_of_differentiableAt_comb`: if two combinations `a F + b G` and
  `c F + d G` with `a d - b c ≠ 0` are differentiable at a point, so are `F` and `G`.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E}

/-- A function is differentiable wherever its totalized derivative does not vanish. -/
theorem differentiableAt_of_fderiv_ne_zero (h : fderiv 𝕜 f x ≠ 0) : DifferentiableAt 𝕜 f x := by
  by_contra hnd
  exact h (fderiv_zero_of_not_differentiableAt hnd)

/-- If two combinations `a F + b G` and `c F + d G` with `a d - b c ≠ 0` are differentiable at a
point, then so are `F` and `G`: they are recovered by inverting the coefficient matrix. -/
theorem differentiableAt_and_of_differentiableAt_comb {F G : E → 𝕜} {a b c d : 𝕜}
    (hdet : a * d - b * c ≠ 0) (hA : DifferentiableAt 𝕜 (fun y ↦ a * F y + b * G y) x)
    (hB : DifferentiableAt 𝕜 (fun y ↦ c * F y + d * G y) x) :
    DifferentiableAt 𝕜 F x ∧ DifferentiableAt 𝕜 G x := by
  have hi : (a * d - b * c) * (a * d - b * c)⁻¹ = 1 := mul_inv_cancel₀ hdet
  constructor
  · have : F = fun y ↦ (d / (a * d - b * c)) * (a * F y + b * G y) +
        (-b / (a * d - b * c)) * (c * F y + d * G y) := by
      funext y
      simp only [div_eq_mul_inv]
      linear_combination (-(F y)) * hi
    rw [this]
    exact (hA.const_mul _).add (hB.const_mul _)
  · have : G = fun y ↦ (-c / (a * d - b * c)) * (a * F y + b * G y) +
        (a / (a * d - b * c)) * (c * F y + d * G y) := by
      funext y
      simp only [div_eq_mul_inv]
      linear_combination (-(G y)) * hi
    rw [this]
    exact (hA.const_mul _).add (hB.const_mul _)

end TauCeti
