/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.Negative.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Holomorphic.PointTwist.RealSmooth

/-!
# The inclusion of a negative point twist, for real-smooth bundles

Let `E → X` be a complex vector bundle over a Riemann surface whose underlying real bundle is
`C^n`. Its negative point twist `E(-x)` is then a real-`C^n` bundle
(`TauCeti.signedPointTwistCore.contMDiffVectorBundle_real`). The inclusion `pointTwistDiv` of
`E(-x)` into `E`, multiplication by the canonical section of `𝒪(x)`, sends real-`C^n` sections of
`E(-x)` to real-`C^n` sections of `E`
(`TauCeti.contMDiff_negPointTwist_pointTwistDiv_section_real`).
In every chart it is the scalar `pointTwistFactor x false b`, which is holomorphic and hence real
`C^n`. This is the real counterpart of `TauCeti.contMDiff_negPointTwist_pointTwistDiv_section`.

## Main results

* `TauCeti.contMDiffAt_negPointTwist_pointTwistDiv_section_real` and
  `TauCeti.contMDiff_negPointTwist_pointTwistDiv_section_real`: the inclusion of `E(-x)` into `E`
  preserves real-`C^n` sections.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10.
-/

public section

noncomputable section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {n : ℕ∞ω}
  [IsManifold 𝓘(ℂ) n X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  {E : X → Type*} [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)] [∀ z, Module ℝ (E z)]
  [∀ z, IsScalarTower ℝ ℂ (E z)] [∀ z, TopologicalSpace (E z)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℂ F E]

local instance instVectorBundleRealNegPointTwistRealSmooth : VectorBundle ℝ F E :=
  VectorBundle.restrictScalars ℝ ℂ F E

local instance instVectorBundleRealNegPointTwistCoreRealSmooth (x : X) :
    VectorBundle ℝ F (negPointTwistCore F E x).Fiber :=
  VectorBundle.restrictScalars ℝ ℂ F _

variable [ContMDiffVectorBundle n F E 𝓘(ℝ, ℂ)]

/-- The inclusion of the negative point twist into `E` sends a section that is real `C^n` at `z₀`
to a section of `E` that is real `C^n` at `z₀`. -/
theorem contMDiffAt_negPointTwist_pointTwistDiv_section_real {x z₀ : X}
    {τ : ∀ z, (negPointTwistCore F E x).Fiber z}
    (hτ : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) n (fun z ↦ TotalSpace.mk' F z (τ z)) z₀) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) n
      (fun z ↦ TotalSpace.mk' F z (pointTwistDiv F E x z (τ z))) z₀ := by
  classical
  have hz₀ := (negPointTwistCore F E x).mem_baseSet_at z₀
  rw [signedPointTwistCore_indexAt] at hz₀
  rw [(trivializationAt F (negPointTwistCore F E x).Fiber z₀).contMDiffAt_section_iff
    (mem_baseSet_trivializationAt F _ z₀), signedPointTwistCore_trivializationAt] at hτ
  refine ((trivializationAt F E z₀).contMDiffAt_section_iff
    (mem_baseSet_trivializationAt F E z₀)).2 ?_
  -- The scalar `pointTwistFactor x false b` is holomorphic, hence real `C^n`.
  have hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n (pointTwistFactor x false (decide (z₀ = x))) z₀ := by
    simpa only [modelWithCornersSelf_restrictScalars] using
      ((contMDiffOn_pointTwistFactor_false x _).contMDiffAt
        ((isOpen_pointTwistBaseSet x _).mem_nhds
          (mem_pointTwistBaseSet_decide x z₀))).restrictScalars ℝ
  have hm := ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F).contMDiff.contMDiffAt.comp z₀
    hf).clm_apply hτ
  refine hm.congr_of_eventuallyEq ?_
  filter_upwards [((negPointTwistCore F E x).isOpen_baseSet _).mem_nhds hz₀] with z hz
  rw [Function.comp_apply, ContinuousLinearMap.lsmul_apply]
  exact trivializationAt_pointTwistDiv_negPointTwistCore hz (τ z)

/-- The inclusion of the negative point twist into `E` sends real-`C^n` sections to real-`C^n`
sections. -/
theorem contMDiff_negPointTwist_pointTwistDiv_section_real {x : X}
    {τ : ∀ z, (negPointTwistCore F E x).Fiber z}
    (hτ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) n fun z ↦ TotalSpace.mk' F z (τ z)) :
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) n
      fun z ↦ TotalSpace.mk' F z (pointTwistDiv F E x z (τ z)) :=
  fun z₀ ↦ contMDiffAt_negPointTwist_pointTwistDiv_section_real (hτ z₀)

end TauCeti
