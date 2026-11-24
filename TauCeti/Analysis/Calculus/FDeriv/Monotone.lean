/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Tactic.GCongr

/-!
# Derivatives of monotone functions on ordered spaces

A monotone real function on an ordered real normed space has a monotone derivative wherever it is
differentiable: along a nonnegative direction `v` the function `t ↦ f (x + t • v)` is monotone, so
its derivative `f' v` at `0` is nonnegative. This is the several-variable form of Mathlib's
`HasDerivAt.nonneg_of_monotone`.

## Main results

* `HasFDerivAt.monotone_of_monotone`: the derivative of a monotone function is monotone.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
  [IsOrderedAddMonoid F] [PosSMulMono ℝ F] {f : F → ℝ} {f' : F →L[ℝ] ℝ} {x : F}

/-- The derivative of a monotone real function on an ordered real normed space is monotone. -/
theorem HasFDerivAt.monotone_of_monotone (hd : HasFDerivAt f f' x) (hf : Monotone f) :
    Monotone f' := by
  refine (monotone_iff_map_nonneg f').2 fun v hv ↦ ?_
  -- `HasLineDerivAt` is by definition the derivative of `t ↦ f (x + t • v)` at `0`.
  exact HasDerivAt.nonneg_of_monotone (hd.hasLineDerivAt v) fun s t hst ↦
    hf (by gcongr)
