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
as `α` and `β` (`ContMDiffWithinAt.clm_bundle_smulRight`), along any base map: in bundle
coordinates it is the image of the pair of coordinates under the fixed continuous bilinear map
`StrongDual.smulRightL`.

When `β` is a second covector field on `V`, this is the bilinear form `(v, w) ↦ α v * β w`. Such
products, together with sums and multiples by functions, build fields of bilinear forms, for
instance metrics, out of covector fields such as differentials of functions. The coefficients of
such combinations are often values `α v` of a covector field on a section, which are as regular
as `α` and `v` (`ContMDiffWithinAt.clm_bundle_apply_scalar`).
-/

public section

open Bundle
open scoped ContDiff Manifold

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {W : B → Type*}
  [∀ b, AddCommGroup (W b)] [∀ b, Module 𝕜 (W b)] [∀ b, TopologicalSpace (W b)]
  [∀ b, IsTopologicalAddGroup (W b)] [∀ b, ContinuousSMul 𝕜 (W b)]
  [TopologicalSpace (TotalSpace F' W)] [FiberBundle F' W] [VectorBundle 𝕜 F' W]
  {n : WithTop ℕ∞} {b : M → B} {α : ∀ m, V (b m) →L[𝕜] 𝕜} {β : ∀ m, W (b m)}
  {v : ∀ m, V (b m)} {s : Set M} {x : M}

/-- **The value of a covector field on a section is as regular as its factors**: if `α` is
`C^n` within `s` at `x` as a field in the dual bundle of `V` and `v` is a `C^n` field in `V`, both
along a base map `b`, then the function `m ↦ α m (v m)` is `C^n` within `s` at `x`. -/
theorem ContMDiffWithinAt.clm_bundle_apply_scalar
    (hα : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun m ↦ TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun z ↦ V z →L[𝕜] 𝕜) (b m) (α m)) s x)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n (fun m ↦ TotalSpace.mk' F (b m) (v m)) s x) :
    ContMDiffWithinAt IM 𝓘(𝕜) n (fun m ↦ α m (v m)) s x :=
  (contMDiffWithinAt_totalSpace_iff.mp
    (hα.clm_bundle_apply (F₂ := 𝕜) (E₂ := Bundle.Trivial B 𝕜) hv)).2

/-- **The value of a covector field on a section is as regular as its factors**: if `α` is
`C^n` at `x` as a field in the dual bundle of `V` and `v` is a `C^n` field in `V`, both along a
base map `b`, then the function `m ↦ α m (v m)` is `C^n` at `x`. -/
theorem ContMDiffAt.clm_bundle_apply_scalar
    (hα : ContMDiffAt IM (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun m ↦ TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun z ↦ V z →L[𝕜] 𝕜) (b m) (α m)) x)
    (hv : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n (fun m ↦ TotalSpace.mk' F (b m) (v m)) x) :
    ContMDiffAt IM 𝓘(𝕜) n (fun m ↦ α m (v m)) x :=
  ContMDiffWithinAt.clm_bundle_apply_scalar hα hv

/-- **The product of a covector field and a section is as regular as its factors**: if `α` is
`C^n` within `s` at `x` as a field in the dual bundle of `V` and `β` is a `C^n` field in `W`, both
along a base map `b`, then `m ↦ (α m).smulRight (β m)`, the linear map `v ↦ α m v • β m`, is `C^n`
within `s` at `x` as a field in the bundle of linear maps from `V` to `W`. -/
theorem ContMDiffWithinAt.clm_bundle_smulRight
    (hα : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun m ↦ TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun z ↦ V z →L[𝕜] 𝕜) (b m) (α m)) s x)
    (hβ : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F')) n
      (fun m ↦ TotalSpace.mk' F' (E := W) (b m) (β m)) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F →L[𝕜] F')) n
      (fun m ↦ TotalSpace.mk' (F →L[𝕜] F')
        (E := fun z ↦ V z →L[𝕜] W z) (b m) ((α m).smulRight (β m))) s x := by
  rw [contMDiffWithinAt_hom_bundle] at hα ⊢
  have hβ' := (contMDiffWithinAt_totalSpace_iff.mp hβ).2
  refine ⟨hα.1, ?_⟩
  -- Cache operator norms before composing the curried multiplication map.
  let _ : NormedAddCommGroup (F →L[𝕜] 𝕜) := inferInstance
  let _ : NormedSpace 𝕜 (F →L[𝕜] 𝕜) := inferInstance
  let _ : NormedAddCommGroup (F →L[𝕜] F') := inferInstance
  let _ : NormedSpace 𝕜 (F →L[𝕜] F') := inferInstance
  have hp := ((StrongDual.smulRightL 𝕜 F F').contDiff.comp_contMDiffWithinAt
    hα.2).clm_apply hβ'
  refine hp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hα.1.continuousWithinAt.preimage_mem_nhdsWithin
      ((trivializationAt F' W (b x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F' W (b x)))] with y hy
    -- Expose preimage membership so the coordinate evaluation lemma can consume it directly.
    change b y ∈ (trivializationAt F' W (b x)).baseSet at hy
    ext u
    simp [ContinuousLinearMap.inCoordinates, Trivialization.coe_linearMapAt_of_mem _ hy]
  · ext u
    simp [ContinuousLinearMap.inCoordinates, Trivialization.coe_linearMapAt_of_mem _
      (FiberBundle.mem_baseSet_trivializationAt F' W (b x))]

/-- **The product of a covector field and a section is as regular as its factors**: if `α` is
`C^n` at `x` as a field in the dual bundle of `V` and `β` is a `C^n` field in `W`, both along a
base map `b`, then `m ↦ (α m).smulRight (β m)`, the linear map `v ↦ α m v • β m`, is `C^n` at `x`
as a field in the bundle of linear maps from `V` to `W`. -/
theorem ContMDiffAt.clm_bundle_smulRight
    (hα : ContMDiffAt IM (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun m ↦ TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun z ↦ V z →L[𝕜] 𝕜) (b m) (α m)) x)
    (hβ : ContMDiffAt IM (IB.prod 𝓘(𝕜, F')) n
      (fun m ↦ TotalSpace.mk' F' (E := W) (b m) (β m)) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F →L[𝕜] F')) n
      (fun m ↦ TotalSpace.mk' (F →L[𝕜] F')
        (E := fun z ↦ V z →L[𝕜] W z) (b m) ((α m).smulRight (β m))) x :=
  ContMDiffWithinAt.clm_bundle_smulRight hα hβ
