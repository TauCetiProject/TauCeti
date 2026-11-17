/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Products of covector fields with sections

For a field of covectors `α` on a vector bundle `V` and a section `β` of a vector bundle `W`, the
product `(α.smulRight β) v = α v • β` is a field of linear maps from `V` to `W`. It is as regular
as `α` and `β` (`ContMDiffAt.clm_bundle_smulRight`): in bundle coordinates it is the image of the
pair of coordinates under the fixed continuous bilinear map `ContinuousLinearMap.smulRightL`.

When `β` is a second covector field on `V`, this is the bilinear form `(v, w) ↦ α v * β w`. Such
products, together with sums and multiples by functions, build fields of bilinear forms, for
instance metrics, out of covector fields such as differentials of functions.
-/

public section

open Bundle
open scoped ContDiff Manifold

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {W : B → Type*}
  [∀ b, AddCommGroup (W b)] [∀ b, Module 𝕜 (W b)] [∀ b, TopologicalSpace (W b)]
  [∀ b, IsTopologicalAddGroup (W b)] [∀ b, ContinuousSMul 𝕜 (W b)]
  [TopologicalSpace (TotalSpace F' W)] [FiberBundle F' W] [VectorBundle 𝕜 F' W]
  {n : WithTop ℕ∞} {α : ∀ b, V b →L[𝕜] 𝕜} {β : ∀ b, W b} {x : B}

/-- **The product of a covector field and a section is as regular as its factors**: if `α` is
`C^n` at `x` as a section of the dual bundle of `V` and `β` is a `C^n` section of `W` at `x`, then
`y ↦ (α y).smulRight (β y)`, the linear map `v ↦ α y v • β y`, is `C^n` at `x` as a section of the
bundle of linear maps from `V` to `W`. -/
theorem ContMDiffAt.clm_bundle_smulRight
    (hα : ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun z ↦ V z →L[𝕜] 𝕜) y (α y)) x)
    (hβ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F')) n (fun y ↦ TotalSpace.mk' F' (E := W) y (β y)) x) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] F')) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F')
        (E := fun z ↦ V z →L[𝕜] W z) y ((α y).smulRight (β y))) x := by
  rw [contMDiffAt_section_iff] at hα hβ ⊢
  -- Cache operator norms before composing the curried multiplication map.
  let _ : NormedAddCommGroup (F →L[𝕜] 𝕜) := inferInstance
  let _ : NormedSpace 𝕜 (F →L[𝕜] 𝕜) := inferInstance
  let _ : NormedAddCommGroup (F →L[𝕜] F') := inferInstance
  let _ : NormedSpace 𝕜 (F →L[𝕜] F') := inferInstance
  have hp := ((ContinuousLinearMap.smulRightL 𝕜 F F').contDiff.comp_contMDiffAt
    hα).clm_apply hβ
  refine hp.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F V x),
    (trivializationAt F' W x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F' W x)] with y hy hy'
  ext u
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, hy, hy']
