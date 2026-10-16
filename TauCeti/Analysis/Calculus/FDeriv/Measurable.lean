/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Joint measurability of the applied derivative

Mathlib proves that the derivative `fderiv 𝕜 f` of an arbitrary function is measurable
(`measurable_fderiv`), and that so is `x ↦ fderiv 𝕜 f x y` for a fixed vector `y`
(`measurable_fderiv_apply_const`). This file adds the joint statement in the point and the
vector, so that `fun_prop` can prove the measurability of expressions such as
`x ↦ fderiv 𝕜 f x (g x)` for a measurable `g`.

## Main results

* `TauCeti.measurable_fderiv_apply`: the map `(x, y) ↦ fderiv 𝕜 f x y` is measurable.
-/

public section

open MeasureTheory

namespace TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [MeasurableSpace F]
  [BorelSpace F]

/-- The derivative of an arbitrary function, applied to a vector, is jointly measurable in the
point and the vector. No differentiability is assumed, the derivative being `0` where `f` is not
differentiable. -/
@[fun_prop]
theorem measurable_fderiv_apply (f : E → F) : Measurable fun p : E × E ↦ fderiv 𝕜 f p.1 p.2 := by
  borelize (E →L[𝕜] F)
  exact (continuous_fst.clm_apply continuous_snd).measurable2
    ((measurable_fderiv 𝕜 f).comp measurable_fst) measurable_snd

end TauCeti
