/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.WithGradient
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Products of covector fields

For two fields of covectors `α` and `β` on a vector bundle `V`, the product
`(α.smulRight β) v w = α v * β w` is a field of bilinear forms on `V`. It is as regular as `α`
and `β` (`ContMDiffAt.clm_bundle_smulRight`): in bundle coordinates it is the image of the pair
of coordinate covectors under the fixed continuous bilinear map
`ContinuousLinearMap.smulRightL`. Such products, together with sums and multiples by functions,
build fields of bilinear forms, for instance metrics, out of covector fields such as differentials
of functions.

In particular, for a field of real bilinear forms `g`, a covector field `α` and a vector field `v`,
the field `(g y).withGradient (α y) (v y)` (`ContinuousLinearMap.withGradient`), which makes `v` the
gradient of `α`, is as regular as `g`, `α` and `v` wherever `α v ≠ 0`
(`ContMDiffAt.clm_bundle_withGradient`).
-/

public section

open Bundle
open scoped ContDiff Manifold

section SmulRight

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module 𝕜 (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : WithTop ℕ∞} {α β : ∀ b, V b →L[𝕜] 𝕜} {x : B}

/-- **The product of two covector fields is as regular as its factors**: if `α` and `β` are `C^n`
at `x` as sections of the dual bundle of `V`, then `y ↦ (α y).smulRight (β y)`, the bilinear form
`(v, w) ↦ α y v * β y w`, is `C^n` at `x` as a section of the bundle of bilinear forms on `V`. -/
theorem ContMDiffAt.clm_bundle_smulRight
    (hα : ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun z ↦ V z →L[𝕜] 𝕜) y (α y)) x)
    (hβ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun z ↦ V z →L[𝕜] 𝕜) y (β y)) x) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] 𝕜)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] 𝕜)
        (E := fun z ↦ V z →L[𝕜] V z →L[𝕜] 𝕜) y ((α y).smulRight (β y))) x := by
  rw [contMDiffAt_section_iff] at hα hβ ⊢
  -- Cache operator norms before composing the curried multiplication map.
  let _ : NormedAddCommGroup (F →L[𝕜] 𝕜) := inferInstance
  let _ : NormedSpace 𝕜 (F →L[𝕜] 𝕜) := inferInstance
  let _ : NormedAddCommGroup (F →L[𝕜] F →L[𝕜] 𝕜) := inferInstance
  let _ : NormedSpace 𝕜 (F →L[𝕜] F →L[𝕜] 𝕜) := inferInstance
  have hp := ((ContinuousLinearMap.smulRightL 𝕜 F (F →L[𝕜] 𝕜)).contDiff.comp_contMDiffAt
    hα).clm_apply hβ
  refine hp.congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F V x)] with y hy
  ext u w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, hy]

end SmulRight

section WithGradient

variable {B EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : B → Type*}
  [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} {g : ∀ b, V b →L[ℝ] V b →L[ℝ] ℝ} {α : ∀ b, V b →L[ℝ] ℝ} {v : ∀ b, V b}
  {x : B}

/-- **Prescribing the gradient of a covector field preserves regularity**: if a field of bilinear
forms `g`, a covector field `α` and a vector field `v` are `C^n` at `x` and `α x (v x) ≠ 0`, then
the field `y ↦ (g y).withGradient (α y) (v y)`, which makes `v` the gradient of `α`, is `C^n` at
`x`. -/
theorem ContMDiffAt.clm_bundle_withGradient
    (hg : ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun z ↦ V z →L[ℝ] V z →L[ℝ] ℝ) y (g y)) x)
    (hα : ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun z ↦ V z →L[ℝ] ℝ) y (α y)) x)
    (hv : ContMDiffAt IB (IB.prod 𝓘(ℝ, F)) n (fun y ↦ TotalSpace.mk' F (E := V) y (v y)) x)
    (hx : α x (v x) ≠ 0) :
    ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun z ↦ V z →L[ℝ] V z →L[ℝ] ℝ) y ((g y).withGradient (α y) (v y))) x := by
  -- The covector field `g v` and the functions `α v` and `g (v, v)`.
  have hgv : ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := fun z ↦ V z →L[ℝ] ℝ) y (g y (v y))) x :=
    hg.clm_bundle_apply hv
  have hαv : ContMDiffAt IB 𝓘(ℝ) n (fun y ↦ α y (v y)) x := by
    have h := hα.clm_bundle_apply (F₂ := ℝ) (E₂ := Bundle.Trivial B ℝ) hv
    simp only [contMDiffAt_totalSpace_iff] at h
    exact h.2
  have hgvv : ContMDiffAt IB 𝓘(ℝ) n (fun y ↦ g y (v y) (v y)) x := by
    have h := hgv.clm_bundle_apply (F₂ := ℝ) (E₂ := Bundle.Trivial B ℝ) hv
    simp only [contMDiffAt_totalSpace_iff] at h
    exact h.2
  -- `withGradient` is a combination of these with coefficients `C^n` where `α v ≠ 0`.
  have h := (hg.sub_section ((hαv.inv₀ hx).smul_section
    ((hα.clm_bundle_smulRight hgv).add_section (hgv.clm_bundle_smulRight hα)))).add_section
    (((hαv.inv₀ hx).add (hgvv.div₀ (hαv.pow 2) (pow_ne_zero 2 hx))).smul_section
      (hα.clm_bundle_smulRight hα))
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ ?_)
  dsimp only
  rw [ContinuousLinearMap.withGradient_def]
  -- The right side evaluates at `z` the same combination of sections and functions.
  rfl

end WithGradient
