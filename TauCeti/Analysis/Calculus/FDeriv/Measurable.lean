/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Calculus.FDeriv.Basic

/-!
# Joint measurability of the applied derivative

Mathlib proves that the derivative `fderiv 𝕜 f` of an arbitrary function is measurable
(`measurable_fderiv`), and that so is `x ↦ fderiv 𝕜 f x y` for a fixed vector `y`
(`measurable_fderiv_apply_const`). This file adds the joint statement in the point and the
vector, so that `fun_prop` can prove the measurability of expressions such as
`x ↦ fderiv 𝕜 f x (g x)` for a measurable `g`. It composes `measurable_fderiv` with the joint
measurability of evaluation, `ContinuousLinearMap.measurable_apply₂`, under the same
second-countability assumption.

An arbitrary function is continuous on its regular set `{x | fderiv 𝕜 f x ≠ 0}`, which is
measurable, so the regular part of the preimage of a measurable set is measurable.

## Main results

* `TauCeti.measurable_fderiv_apply`: the map `(x, y) ↦ fderiv 𝕜 f x y` is measurable.
* `TauCeti.measurableSet_preimage_inter_setOf_fderiv_ne_zero`: the regular part
  `f⁻¹(I) ∩ {Df ≠ 0}` of the preimage of a measurable set is measurable.
-/

public section

open MeasureTheory

namespace TauCeti

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [MeasurableSpace E] [OpensMeasurableSpace E] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopologyEither (E →L[𝕜] F) E]

/-- The derivative of an arbitrary function, applied to a vector, is jointly measurable in the
point and the vector. No differentiability is assumed, the derivative being `0` where `f` is not
differentiable. -/
@[fun_prop]
theorem measurable_fderiv_apply (f : E → F) : Measurable fun p : E × E ↦ fderiv 𝕜 f p.1 p.2 := by
  borelize (E →L[𝕜] F)
  exact ContinuousLinearMap.measurable_apply₂.comp ((measurable_fderiv 𝕜 f).prodMap measurable_id)

variable {𝕜}

omit [SecondCountableTopologyEither (E →L[𝕜] F) E] in
/-- The regular part `f⁻¹(I) ∩ {Df ≠ 0}` of the preimage of a measurable set is measurable, for
every function `f`: the function is continuous on its regular set, which is measurable. -/
theorem measurableSet_preimage_inter_setOf_fderiv_ne_zero {f : E → F} {I : Set F}
    (hI : MeasurableSet I) : MeasurableSet (f ⁻¹' I ∩ {x | fderiv 𝕜 f x ≠ 0}) := by
  classical
  have hR : MeasurableSet {x | fderiv 𝕜 f x ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv 𝕜 f)
  have hk : Measurable ({x | fderiv 𝕜 f x ≠ 0}.piecewise f 0) :=
    ContinuousOn.measurable_piecewise
      (fun x hx ↦ (differentiableAt_of_fderiv_ne_zero hx).continuousAt.continuousWithinAt)
      continuousOn_const hR
  convert (hk hI).inter hR using 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, and_congr_left_iff]
  intro hx
  rw [Set.piecewise_eq_of_mem _ _ _ hx]

end TauCeti
