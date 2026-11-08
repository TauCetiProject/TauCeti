/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Vanishing derivative of a function constant on two rays

A real function that is constant on `(-∞, a]` and on `[b, ∞)` has vanishing derivative at every
point outside `(a, b)`, with no regularity assumption.

## Main results

* `TauCeti.deriv_eq_zero_of_not_mem_Ioo`: a function constant on `(-∞, a]` and on `[b, ∞)` has
  zero derivative outside `(a, b)`.
-/

public section

open Set

namespace TauCeti

/-- A function that is constant on `(-∞, a]` and on `[b, ∞)` has vanishing derivative outside
`(a, b)`, with no regularity assumption. At a point of either closed ray the derivative
along that ray is zero, and Mathlib's `HasDerivWithinAt.deriv_eq_zero` turns this into the
vanishing of `deriv`. -/
theorem deriv_eq_zero_of_not_mem_Ioo {μ : ℝ → ℝ} {a b c : ℝ}
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
