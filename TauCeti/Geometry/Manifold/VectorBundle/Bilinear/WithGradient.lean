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
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight

/-!
# Regularity of fields of bilinear forms with a prescribed gradient

For a field of real bilinear forms `g`, a covector field `α` and a vector field `v` on a vector
bundle, the field `(g y).withGradient (α y) (v y)` (`ContinuousLinearMap.withGradient`), which makes
`v` the gradient of `α`, is as regular as `g`, `α` and `v` wherever `α v ≠ 0`
(`ContMDiffAt.clm_bundle_withGradient`): it is a combination of `g` and of products of the
covectors `α` and `g v` (`ContMDiffAt.clm_bundle_smulRight`), with coefficients which are
functions of `α v` and `g (v, v)`.
-/

public section

open Bundle
open scoped ContDiff Manifold

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
  have hαv : ContMDiffAt IB 𝓘(ℝ) n (fun y ↦ α y (v y)) x := hα.clm_bundle_apply_scalar hv
  have hgvv : ContMDiffAt IB 𝓘(ℝ) n (fun y ↦ g y (v y) (v y)) x :=
    hgv.clm_bundle_apply_scalar hv
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
