/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight

/-!
# Products of metric-dual covectors

The product of the metric duals of two regular sections is a regular section of the
native bundle of continuous bilinear forms. In particular, a smooth orthonormal frame
induces smooth covariant two-tensor fields without choosing new bundle coordinates.
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [IsContMDiffRiemannianBundle I n F V]

/-- The product `⟪σ, ·⟫ ⟪τ, ·⟫` of metric-dual covectors is as regular as its two sections
and the metric, as a section of the native bilinear-form bundle. -/
theorem ContMDiffAt.innerSL_smulRight_bundle {σ τ : Π x, V x} {x : M}
    (hσ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n (T% σ) x)
    (hτ : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n (T% τ) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun z ↦ V z →L[ℝ] V z →L[ℝ] ℝ) y
        ((innerSL ℝ (σ y)).smulRight (innerSL ℝ (τ y)))) x := by
  obtain ⟨g, hg, heq⟩ :=
    IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := n) (F := F) (E := V)
  have hdual {s : Π y, V y}
      (hs : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n (T% s) x) :
      ContMDiffAt I (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
        (fun y ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
          (E := fun z ↦ V z →L[ℝ] ℝ) y (innerSL ℝ (s y))) x := by
    have hmetric (y : M) : g y = innerSL ℝ := by
      ext u w
      exact (heq y u w).symm
    simpa only [hmetric] using ContMDiffAt.clm_bundle_apply (hg x) hs
  exact (hdual hσ).clm_bundle_smulRight (hdual hτ)
