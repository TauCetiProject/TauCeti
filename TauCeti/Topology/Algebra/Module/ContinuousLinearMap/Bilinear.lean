/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Flipping jointly continuous bilinear maps

A curried continuous linear map between topological modules need not be jointly continuous.
Given joint continuity, `ContinuousLinearMap.flipOfContinuous` exchanges its arguments without
requiring norms on the modules.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]

/-- Exchange the arguments of a jointly continuous bilinear map on topological modules. -/
def flipOfContinuous (μ : E →L[𝕜] F →L[𝕜] G)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) : F →L[𝕜] E →L[𝕜] G := by
  let B : F →ₗ[𝕜] E →L[𝕜] G :=
    { toFun y :=
        { toFun x := μ x y
          map_add' := by intro x z; simp
          map_smul' := by intro c x; simp
          cont := hμ.comp (continuous_id.prodMk continuous_const) }
      map_add' := by
        intro y z
        ext x
        exact (μ x).map_add y z
      map_smul' := by
        intro c y
        ext x
        exact (μ x).map_smul c y }
  exact
    { toLinearMap := B
      cont := continuous_of_continuous_uncurry B <| by
        exact hμ.comp continuous_swap }

/-- The flipped pairing evaluates the original pairing in reverse order. -/
@[simp]
theorem flipOfContinuous_apply (μ : E →L[𝕜] F →L[𝕜] G)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) (y : F) (x : E) :
    μ.flipOfContinuous hμ y x = μ x y := by
  rfl

/-- Exchanging the arguments preserves joint continuity. -/
theorem continuous_uncurry_flipOfContinuous (μ : E →L[𝕜] F →L[𝕜] G)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y)) :
    Continuous (Function.uncurry fun y x ↦ μ.flipOfContinuous hμ y x) := by
  simpa only [Function.uncurry_def, Function.comp_def, Prod.swap, flipOfContinuous_apply]
    using hμ.comp continuous_swap

end ContinuousLinearMap
