/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder continuity of interval integrals

A common Hölder bound for an interval-integrable family passes to its integral, multiplied
by the length of the interval. In particular, averaging over the unit interval preserves
the Hölder constant. This is used for the entries of segment-averaged inverse matrices.

The argument is adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).
-/

public section

open Set MeasureTheory
open scoped NNReal

namespace TauCeti

/-- Integrating a uniformly Hölder family over an interval multiplies its Hölder constant
by the interval length. -/
theorem holderWith_intervalIntegral {X Y : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (q : ℝ → X → Y) (C r : ℝ≥0) {a b : ℝ}
    (hq : ∀ x, IntervalIntegrable (fun t => q t x) volume a b)
    (hh : ∀ t ∈ uIoc a b, HolderWith C r (q t)) :
    HolderWith (‖b - a‖₊ * C) r (fun x => ∫ t in a..b, q t x) := by
  refine holderOnWith_univ.1 (HolderOnWith.of_dist_le ?_)
  intro x _ y _
  rw [dist_eq_norm, ← intervalIntegral.integral_sub (hq x) (hq y)]
  have hbound : ∀ t ∈ uIoc a b, ‖q t x - q t y‖ ≤ (C : ℝ) * dist x y ^ (r : ℝ) :=
    fun t ht => by simpa only [dist_eq_norm] using (hh t ht).dist_le x y
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  refine h.trans_eq ?_
  simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
  ring

end TauCeti
