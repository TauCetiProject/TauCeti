/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Orders of vanishing of products

If the derivatives of order less than `a` of `f` and those of order less than `b` of `g` vanish at
`x`, then the derivatives of order less than `a + b` of the product `f * g` vanish at `x`: orders
of vanishing add under multiplication. This follows from the Leibniz bound
`norm_iteratedFDeriv_mul_le`, since every term of the Leibniz expansion of a derivative of order
`n < a + b` contains a derivative of `f` of order less than `a` or one of `g` of order less than
`b`.

This is the analytic half of the description of the powers of the vanishing ideal of a point by
vanishing derivatives.
-/

public section

namespace TauCeti

variable {𝕜 E A : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedRing A] [NormedAlgebra 𝕜 A]

/-- **Orders of vanishing add.** If the derivatives of `f` of order less than `a` and those of
`g` of order less than `b` vanish at `x`, then the derivative of order `n < a + b` of `f * g`
vanishes at `x`. -/
theorem iteratedFDeriv_mul_eq_zero_of_lt_add {f g : E → A} {n a b : ℕ} (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) {x : E} (hfa : ∀ i < a, iteratedFDeriv 𝕜 i f x = 0)
    (hgb : ∀ i < b, iteratedFDeriv 𝕜 i g x = 0) (hn : n < a + b) :
    iteratedFDeriv 𝕜 n (fun y ↦ f y * g y) x = 0 := by
  refine norm_le_zero_iff.1 ((norm_iteratedFDeriv_mul_le hf hg x le_rfl).trans
    (Finset.sum_nonpos fun i hi ↦ ?_))
  rw [Finset.mem_range] at hi
  rcases lt_or_ge i a with hia | hia
  · simp [hfa i hia]
  · simp [hgb (n - i) (by omega)]

end TauCeti
