/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Pointwise almost complex structures on `Lp` spaces

A continuous real-linear endomorphism `J` of a normed space `E` with `J (J v) = -v` acts
pointwise on every `Lp E p μ`, and this action is again an almost complex structure. This is the
complex structure of the `L²` targets of linearized Cauchy–Riemann and vortex operators, see
McDuff–Salamon, *J-holomorphic Curves and Symplectic Topology*, §A.2.

## Main declarations

* `TauCeti.AlmostComplexStructure.compLp`: the almost complex structure of `Lp E p μ` acting by
  `J` pointwise.
* `TauCeti.AlmostComplexStructure.compLp_apply`, `TauCeti.AlmostComplexStructure.coeFn_compLp`:
  it is `ContinuousLinearMap.compLp J`, so its classes are almost everywhere `J` of the values.
-/

public noncomputable section

open MeasureTheory

namespace TauCeti.AlmostComplexStructure

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous real-linear `J` with `J (J v) = -v`, acting pointwise on `Lp E p μ`, as an almost
complex structure. -/
def compLp (J : E →L[ℝ] E) (hJ : ∀ v, J (J v) = -v) (p : ENNReal)
    (μ : Measure α) : AlmostComplexStructure (Lp E p μ) where
  toLinearMap := J.compLpₗ p μ
  square_neg := LinearMap.ext fun g ↦ Lp.ext <| by
    filter_upwards [J.coeFn_compLp (J.compLp g), J.coeFn_compLp g, Lp.coeFn_neg g]
      with z h₁ h₂ h₃
    simpa [h₁, h₂, hJ] using h₃.symm

/-- The pointwise almost complex structure of `Lp E p μ` is `J` composed with the classes. -/
@[simp]
theorem compLp_apply (J : E →L[ℝ] E) (hJ : ∀ v, J (J v) = -v) (p : ENNReal)
    (μ : Measure α) (g : Lp E p μ) : compLp J hJ p μ g = J.compLp g :=
  (rfl)

/-- The pointwise almost complex structure of `Lp E p μ` acts by `J` almost everywhere. -/
theorem coeFn_compLp (J : E →L[ℝ] E) (hJ : ∀ v, J (J v) = -v) (p : ENNReal)
    (μ : Measure α) (g : Lp E p μ) : compLp J hJ p μ g =ᵐ[μ] fun z ↦ J (g z) := by
  rw [compLp_apply]
  exact J.coeFn_compLp g

end TauCeti.AlmostComplexStructure
