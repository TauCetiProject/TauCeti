/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Power growth from a differential inequality

The inequality `α f(t) ≤ t f'(t)` makes `f(t) / t^α` nondecreasing on positive
intervals. It gives power bounds at smaller radii from data at a larger radius,
including when `f` vanishes. No division by `f` or positivity assumption on `f` is needed.

The proof uses Mathlib's derivative criterion for monotonicity and real-power calculus.
-/

public section

open Set

namespace TauCeti

/-- An Euler differential inequality makes the power-normalized function nondecreasing
on any convex set of positive real numbers. -/
theorem monotoneOn_div_rpow_of_mul_le_mul_deriv {f f' : ℝ → ℝ} {s : Set ℝ} {α : ℝ}
    (hs : Convex ℝ s) (hpos : ∀ t ∈ s, 0 < t)
    (hf : ∀ t ∈ s, HasDerivAt f (f' t) t)
    (hle : ∀ t ∈ s, α * f t ≤ t * f' t) :
    MonotoneOn (fun t ↦ f t / t ^ α) s := by
  have hd (t : ℝ) (ht : t ∈ s) :=
    (hf t ht).div (Real.hasDerivAt_rpow_const (Or.inl (hpos t ht).ne'))
      (Real.rpow_pos_of_pos (hpos t ht) α).ne'
  apply monotoneOn_of_deriv_nonneg hs
    (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [(hd t (interior_subset ht)).deriv]
  apply div_nonneg _ (sq_nonneg _)
  rw [Real.rpow_sub_one (hpos t (interior_subset ht)).ne']
  have h := hle t (interior_subset ht)
  have hp := Real.rpow_pos_of_pos (hpos t (interior_subset ht)) α
  have htpos := hpos t (interior_subset ht)
  convert div_nonneg (mul_nonneg (sub_nonneg.mpr h) hp.le) htpos.le using 1
  field_simp

end TauCeti

end
