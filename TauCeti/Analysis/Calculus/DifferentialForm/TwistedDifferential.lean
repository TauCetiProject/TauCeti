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

* `TauCeti.AlmostComplexStructure.twistedDifferential J f`: the one-form `d^c_J f = -(1/2) df ∘ J`.

## Main results

* `TauCeti.AlmostComplexStructure.twistedDifferential_comp`: the chain rule
  `d^c_J (H ∘ f) = H'(f) • d^c_J f`.
* `TauCeti.AlmostComplexStructure.twistedDifferential_add`,
  `TauCeti.AlmostComplexStructure.twistedDifferential_const_smul`: linearity.
-/

public section

noncomputable section

open ContinuousAlternatingMap

namespace TauCeti.AlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (J : AlmostComplexStructure E)

/-- The twisted differential `d^c_J f = -(1/2) df ∘ J` of a real function `f`. -/
def twistedDifferential (f : E → ℝ) (x : E) : E [⋀^Fin 1]→L[ℝ] ℝ :=
  ofSubsingletonLIE (0 : Fin 1)
    ((-2⁻¹ : ℝ) • (fderiv ℝ f x).comp (LinearMap.toContinuousLinearMap J.toLinearMap))

/-- The twisted differential evaluated on a vector. -/
@[simp]
theorem twistedDifferential_apply (f : E → ℝ) (x : E) (v : Fin 1 → E) :
    J.twistedDifferential f x v = -2⁻¹ * fderiv ℝ f x (J (v 0)) := by
  simp [twistedDifferential]

/-- **Chain rule for the twisted differential.** If `H` has derivative `h'` at `f x`, then
`d^c_J (H ∘ f) = h' • d^c_J f` at `x`. -/
theorem twistedDifferential_comp {H : ℝ → ℝ} {h' : ℝ} {f : E → ℝ} {x : E}
    (hH : HasDerivAt H h' (f x)) (hf : DifferentiableAt ℝ f x) :
    J.twistedDifferential (H ∘ f) x = h' • J.twistedDifferential f x := by
  ext v
  simp [(hH.comp_hasFDerivAt x hf.hasFDerivAt).fderiv]
  ring

/-- The twisted differential is additive on functions differentiable at the point. -/
theorem twistedDifferential_add {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    J.twistedDifferential (f + g) x = J.twistedDifferential f x + J.twistedDifferential g x := by
  ext v
  simp [fderiv_add hf hg]
  ring

/-- The twisted differential commutes with scalar multiplication. -/
theorem twistedDifferential_const_smul (c : ℝ) (f : E → ℝ) (x : E) :
    J.twistedDifferential (c • f) x = c • J.twistedDifferential f x := by
  ext v
  simp [fderiv_const_smul_field]
  ring

end TauCeti.AlmostComplexStructure
