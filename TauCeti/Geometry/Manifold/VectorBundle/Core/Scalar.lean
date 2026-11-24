/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Vector-bundle cores with fibre the scalar field

A Mathlib `VectorBundleCore 𝕜 B 𝕜 ι` with model fibre `𝕜` is a line bundle presented by
transition functions, with no separate line-bundle carrier. Each coordinate change is
multiplication by a scalar, its value at `1`. So the transition cocycle of such a core is a family
of scalar functions, and the core is `C^n` exactly when these scalar functions are `C^n` on the
overlaps (`VectorBundleCore.isContMDiff_iff_contMDiffOn_coordChange_one`). Over a complex model
`𝓘(ℂ, EB)` with `n = ∞` or `n = ω`, this says that a line bundle glued from scalar transition
functions is holomorphic exactly when its transition functions are holomorphic.

## Main results

* `VectorBundleCore.isContMDiff_iff_contMDiffOn_coordChange_one`: the `C^n` criterion for the
  scalar transition functions.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace VectorBundleCore

variable {𝕜 B EB HB ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup EB]
  [NormedSpace 𝕜 EB] [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {n : ℕ∞ω} (Z : VectorBundleCore 𝕜 B 𝕜 ι)

/-- A core with model fibre `𝕜` is `C^n` exactly when its scalar transition functions
`x ↦ Z.coordChange i j x 1` are `C^n` on the overlaps of the base sets. -/
theorem isContMDiff_iff_contMDiffOn_coordChange_one :
    Z.IsContMDiff IB n ↔ ∀ i j, ContMDiffOn IB 𝓘(𝕜) n (fun x ↦ Z.coordChange i j x 1)
      (Z.baseSet i ∩ Z.baseSet j) := by
  refine ⟨fun h i j ↦ ?_, fun h ↦ ⟨fun i j ↦ ?_⟩⟩
  · exact (ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).contMDiff.comp_contMDiffOn
      (Z.contMDiffOn_coordChange IB i j)
  · exact ((ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] 𝕜 →L[𝕜] 𝕜).contMDiff.comp_contMDiffOn
      (h i j)).congr fun x _ ↦ by ext; simp

end VectorBundleCore
