/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Geometry.Symplectic.AlmostComplex

/-!
# The twisted differential of a real function

Given an almost complex structure `J` on a finite-dimensional real normed space, the twisted
differential of a real function `f` is the one-form `d^c_J f = -(1/2) df ∘ J`.

## Main definitions

* `TauCeti.twistedDifferential J f`: the one-form `d^c_J f = -(1/2) df ∘ J`.
-/

public section

noncomputable section

open ContinuousAlternatingMap

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (J : AlmostComplexStructure E)

/-- The twisted differential `d^c_J f = -(1/2) df ∘ J` of a real function `f`. -/
def twistedDifferential (f : E → ℝ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ofSubsingletonLIE (0 : Fin 1)
    ((-2⁻¹ : ℝ) • (fderiv ℝ f x).comp (LinearMap.toContinuousLinearMap J.toLinearMap))

/-- The twisted differential evaluated on a vector. -/
@[simp]
theorem twistedDifferential_apply (f : E → ℝ) (x : E) (v : Fin 1 → E) :
    twistedDifferential J f x v = -2⁻¹ * fderiv ℝ f x (J (v 0)) := by
  simp [twistedDifferential]

end TauCeti
