/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Smooth bump functions as test functions

A smooth bump function `β : ContDiffBump c` on a real normed space is smooth, with support the
closed ball `closedBall c β.rOut`. When this ball lies in an open set `Ω`, the bump function, with
real or complex values, is a test function on `Ω`. Such test functions are the standard cutoffs
equal to `1` near a point.

## Main declarations

* `ContDiffBump.toTestFunction`: the bump function as a test function on `Ω`, with values
  `ContDiffBump.toTestFunction_apply` and support `ContDiffBump.tsupport_toTestFunction`.
-/

@[expose] public section

noncomputable section

open Metric TopologicalSpace
open scoped Distributions

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [HasContDiffBump E] {c : E}
  (𝕜 : Type*) [RCLike 𝕜] {Ω : Opens E}

/-- A smooth bump function whose closed outer ball lies in the open set `Ω`, as a test function on
`Ω` with values in `𝕜 = ℝ` or `ℂ`. -/
def toTestFunction (β : ContDiffBump c) (hβ : closedBall c β.rOut ⊆ Ω) : 𝓓(Ω, 𝕜) where
  toFun x := β x
  contDiff' := by
    simpa only [RCLike.ofRealCLM_apply, Function.comp_def] using
      (RCLike.ofRealCLM (K := 𝕜)).contDiff.comp β.contDiff
  hasCompactSupport' := β.hasCompactSupport.comp_left RCLike.ofReal_zero
  tsupport_subset' := (tsupport_comp_subset RCLike.ofReal_zero _).trans (β.tsupport_eq ▸ hβ)

@[simp]
theorem toTestFunction_apply (β : ContDiffBump c) (hβ : closedBall c β.rOut ⊆ Ω) (x : E) :
    β.toTestFunction 𝕜 hβ x = β x :=
  rfl

/-- The support of a bump function viewed as a test function is its closed outer ball. -/
theorem tsupport_toTestFunction (β : ContDiffBump c) (hβ : closedBall c β.rOut ⊆ Ω) :
    tsupport (β.toTestFunction 𝕜 hβ) = closedBall c β.rOut := by
  rw [← β.tsupport_eq, show ⇑(β.toTestFunction 𝕜 hβ) = (fun r : ℝ ↦ (r : 𝕜)) ∘ β from
    funext (toTestFunction_apply 𝕜 β hβ)]
  exact tsupport_comp_eq (fun {_} ↦ RCLike.ofReal_eq_zero) _

end ContDiffBump
