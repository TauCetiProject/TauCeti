/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Topology.VectorBundle.Pullback.Basic

/-!
# Pulling back local frames

A local frame of a vector bundle over `U` pulls back to a local frame over the preimage of `U`.
The sections are evaluated at the image point, with values in the native pullback bundle. This
uses the same fibre coordinates in the original and pulled-back trivializations, so the
regularity assertion only needs smoothness of the base map on that preimage.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

variable {𝕜 E E' H H' M M' F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
  {n : ℕ∞ω} {ι : Type*} {s : ι → ∀ x, V x} {U : Set M}
  {K : Type*} [FunLike K M' M] [ContinuousMapClass K M' M]

/-- Evaluating a `C^n` local frame at the image points of a continuous map gives a `C^n` local
frame of the pullback bundle over the preimage of its domain, if the map is `C^n` there. -/
theorem IsLocalFrameOn.pullback (hs : IsLocalFrameOn I F n s U) (f : K)
    (hf : ContMDiffOn I' I n f (f ⁻¹' U)) :
    IsLocalFrameOn I' F n (V := (f : M' → M) *ᵖ V) (fun i x ↦ s i (f x)) (f ⁻¹' U) where
  linearIndependent hx := hs.linearIndependent hx
  generating hx := hs.generating hx
  contMDiffOn i := by
    intro x hx
    have hσ := (hs.contMDiffOn i).comp hf (mapsTo_preimage f U) x hx
    -- The pullback chart at `x` uses the same fibre coordinate as the original chart at `f x`.
    refine Bundle.contMDiffWithinAt_totalSpace_iff.2 ⟨contMDiffWithinAt_id, ?_⟩
    simpa only [trivializationAt, FiberBundle.pullback_trivializationAt',
      Trivialization.pullback_apply, Pullback.lift_mk, Function.comp_apply]
      using (Bundle.contMDiffWithinAt_totalSpace_iff.mp hσ).2
