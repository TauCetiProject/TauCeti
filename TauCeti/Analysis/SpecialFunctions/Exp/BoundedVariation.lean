/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.BoundedVariation
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Bounded variation of two-sided exponential weights

For `δ ≥ 0`, the two-sided exponential `x ↦ exp (-(δ |x|))` increases on `(-∞, 0]` and decreases
on `[0, ∞)`, with values in `(0, 1]`, so it has bounded variation on `ℝ`. Multiplying by it lowers
an exponential weight: if `x ↦ f x * exp (b |x|)` has bounded variation on `ℝ`, then so does
`x ↦ f x * exp (a |x|)` for every `a ≤ b`. The integrable counterpart of the second statement is
`TauCeti.integrable_mul_exp_mul_abs_of_le`.

## Main results

* `TauCeti.boundedVariationOn_exp_neg_mul_abs`: `x ↦ exp (-(δ |x|))` has bounded variation on `ℝ`
  for `δ ≥ 0`.
* `TauCeti.boundedVariationOn_mul_exp_mul_abs_of_le`: lowering the exponential weight of a function
  of bounded variation on `ℝ` preserves bounded variation.
-/

public section

open Set

namespace TauCeti

/-- For `δ ≥ 0`, the two-sided exponential `x ↦ exp (-(δ |x|))` has bounded variation on `ℝ`: it
increases on `(-∞, 0]` and decreases on `[0, ∞)`, with values in `(0, 1]`. -/
theorem boundedVariationOn_exp_neg_mul_abs {δ : ℝ} (hδ : 0 ≤ δ) :
    BoundedVariationOn (fun x : ℝ ↦ Real.exp (-(δ * |x|))) univ := by
  set g : ℝ → ℝ := fun x ↦ Real.exp (-(δ * |x|))
  have hbound (x : ℝ) : |g x| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hδ (abs_nonneg x)))
  have hleft : BoundedVariationOn g (Iic 0) := by
    refine MonotoneOn.boundedVariationOn (fun x hx y hy hxy ↦ ?_) fun x _ ↦ hbound x
    simp only [g, Real.exp_le_exp, neg_le_neg_iff]
    rw [abs_of_nonpos hx, abs_of_nonpos hy]
    nlinarith
  have hright : BoundedVariationOn (-g) (Ici 0) := by
    refine MonotoneOn.boundedVariationOn (fun x hx y hy hxy ↦ ?_) fun x _ ↦ by
      simpa using hbound x
    simp only [g, Pi.neg_apply, neg_le_neg_iff, Real.exp_le_exp]
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    nlinarith
  have h := eVariationOn.union g (isGreatest_Iic (a := (0 : ℝ))) isLeast_Ici
  rw [Iic_union_Ici] at h
  rw [BoundedVariationOn, h]
  exact ENNReal.add_ne_top.2 ⟨hleft, by simpa [BoundedVariationOn] using hright⟩

/-- Lowering an exponential weight preserves bounded variation on `ℝ`: if `x ↦ f x * exp (b |x|)`
has bounded variation, then so does `x ↦ f x * exp (a |x|)` for `a ≤ b`, the product of the first
function with `x ↦ exp (-((b - a) |x|))`. -/
theorem boundedVariationOn_mul_exp_mul_abs_of_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn (fun x ↦ f x * Real.exp (b * |x|)) univ) :
    BoundedVariationOn (fun x ↦ f x * Real.exp (a * |x|)) univ := by
  have heq : (fun x ↦ f x * Real.exp (a * |x|)) =
      fun x ↦ f x * Real.exp (b * |x|) * Real.exp (-((b - a) * |x|)) := by
    ext x
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  rw [heq]
  exact hf.fun_mul (boundedVariationOn_exp_neg_mul_abs (sub_nonneg.2 hab))

end TauCeti
