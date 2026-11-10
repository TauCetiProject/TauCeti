/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Vanishing derivative of a function constant on two rays

A function from `ℝ` to a normed space that is constant on `(-∞, a]` and on `[b, ∞)` has vanishing
(total) derivative at every point outside `(a, b)`, with no regularity assumption.

## Main results

* `TauCeti.deriv_eq_zero_of_not_mem_Ioo`: a function `ℝ → E` constant on `(-∞, a]` and on `[b, ∞)`
  has zero derivative outside `(a, b)`.
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function `ℝ → E` that is constant on `(-∞, a]` and on `[b, ∞)` has vanishing derivative
outside `(a, b)`. This is a statement about Lean's total `deriv`, which is zero wherever the
function is not differentiable; it does not assert that the function is differentiable at the
endpoints `a` and `b`. -/
theorem deriv_eq_zero_of_not_mem_Ioo {μ : ℝ → E} {a b : ℝ} {c : E}
    (hlow : ∀ r ≤ a, μ r = μ a) (hhigh : ∀ r, b ≤ r → μ r = c) :
    ∀ r ∉ Ioo a b, deriv μ r = 0 := by
  intro r hr
  rcases not_and_or.1 (by simpa only [mem_Ioo] using hr) with h | h
  · have hr' : r ≤ a := not_lt.1 h
    exact ((hasDerivWithinAt_const r (Iic a) (μ a)).congr (fun x hx ↦ hlow x hx)
      (hlow r hr')).deriv_eq_zero (uniqueDiffOn_Iic a r hr')
  · have hr' : b ≤ r := not_lt.1 h
    exact ((hasDerivWithinAt_const r (Ici b) c).congr (fun x hx ↦ hhigh x hx)
      (hhigh r hr')).deriv_eq_zero (uniqueDiffOn_Ici b r hr')

end TauCeti
