/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Deriv

/-!
# Derivatives of functions that are odd or even near a point

The derivative of a function that is odd near `x` takes the same value at `-x` and `x`, and the
derivative of a function that is even near `x` takes opposite values there. Consequently the
second derivative at `0` of a function that is odd near `0` vanishes, provided the codomain has no
`2`-torsion. A real function that is odd near `0` and has positive third derivative is therefore
strictly convex to the right of `0`, since its second derivative increases from the value `0`.

## Main results

* `TauCeti.deriv_neg_eq_of_eventually_odd`: `f'(-x) = f'(x)` for `f` odd near `x`.
* `TauCeti.deriv_neg_eq_neg_of_eventually_even`: `f'(-x) = -f'(x)` for `f` even near `x`.
* `TauCeti.iteratedDeriv_two_eq_zero_of_eventually_odd`: `f''(0) = 0` for `f` odd near `0`.
* `TauCeti.strictConvexOn_Icc_of_eventually_odd`: a real function odd near `0` with positive third
  derivative is strictly convex on `[0, δ]`.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : 𝕜 → F}

/-- If `f` is odd near `x`, then `f'(-x) = f'(x)`. -/
theorem deriv_neg_eq_of_eventually_odd {x : 𝕜} (h : ∀ᶠ y in 𝓝 x, f (-y) = -f y) :
    deriv f (-x) = deriv f x := by
  have h' : f =ᶠ[𝓝 x] fun y => -f (-y) := h.mono fun y hy => by beta_reduce; rw [hy, neg_neg]
  rw [h'.deriv_eq, deriv.fun_neg, deriv_comp_neg, neg_neg]

/-- If `f` is even near `x`, then `f'(-x) = -f'(x)`. -/
theorem deriv_neg_eq_neg_of_eventually_even {x : 𝕜} (h : ∀ᶠ y in 𝓝 x, f (-y) = f y) :
    deriv f (-x) = -deriv f x := by
  have h' : f =ᶠ[𝓝 x] fun y => f (-y) := h.mono fun y hy => hy.symm
  rw [h'.deriv_eq, deriv_comp_neg, neg_neg]

/-- The second derivative at `0` of a function that is odd near `0` vanishes. -/
theorem iteratedDeriv_two_eq_zero_of_eventually_odd [IsAddTorsionFree F]
    (h : ∀ᶠ y in 𝓝 0, f (-y) = -f y) : iteratedDeriv 2 f 0 = 0 := by
  have h₁ : ∀ᶠ y in 𝓝 (0 : 𝕜), deriv f (-y) = deriv f y :=
    h.eventually_nhds.mono fun y hy => deriv_neg_eq_of_eventually_odd hy
  have h₂ := deriv_neg_eq_neg_of_eventually_even h₁
  rw [neg_zero] at h₂
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact self_eq_neg.1 h₂

/-- A function that is odd near `0`, whose second derivative is continuous on `[0, δ]` and whose
third derivative is positive on `(0, δ)`, is strictly convex on `[0, δ]`. -/
theorem strictConvexOn_Icc_of_eventually_odd {g : ℝ → ℝ} {δ : ℝ} (hc : ContinuousOn g (Icc 0 δ))
    (hodd : ∀ᶠ y in 𝓝 0, g (-y) = -g y) (hc2 : ContinuousOn (deriv^[2] g) (Icc 0 δ))
    (h3 : ∀ x ∈ Ioo 0 δ, 0 < deriv^[3] g x) : StrictConvexOn ℝ (Icc 0 δ) g := by
  have h2zero : deriv^[2] g 0 = 0 := by
    rw [← iteratedDeriv_eq_iterate]
    exact iteratedDeriv_two_eq_zero_of_eventually_odd hodd
  have hmono : StrictMonoOn (deriv^[2] g) (Icc 0 δ) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hc2 fun y hy => ?_
    rw [interior_Icc] at hy
    rw [← Function.iterate_succ_apply' deriv]
    exact h3 y hy
  refine strictConvexOn_of_deriv2_pos (convex_Icc _ _) hc fun y hy => ?_
  rw [interior_Icc] at hy
  rw [← h2zero]
  exact hmono (left_mem_Icc.2 (hy.1.trans hy.2).le) (Ioo_subset_Icc_self hy) hy.1

end TauCeti
