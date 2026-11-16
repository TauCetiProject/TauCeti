/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Dual

/-!
# Rank-one maps out of a Riemannian bundle

The rank-one map `v ↦ ⟪τ, v⟫ • σ` depends smoothly on fields `τ` in a
Riemannian bundle `V` and `σ` in an arbitrary normed vector bundle `W`, along the same base
map, as a field in the Hom bundle from `V` to `W`. Neither bundle needs finite rank.
Taking `W = V`, this provides smooth matrix units from orthonormal local frames, with the
native Hom-bundle topology.

The construction is Mathlib's `InnerProductSpace.rankOne`; smoothness follows by
metric duality and the coordinate criterion for smooth Hom-bundle fields.
-/

public section

open Bundle InnerProductSpace
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [fiberNorm : ∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [hmetric : IsContMDiffRiemannianBundle I n F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [targetNorm : ∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [TopologicalSpace B] [ChartedSpace HB B]
  {b : B → M} {σ : Π y : B, W (b y)} {τ : Π y : B, V (b y)} {s : Set B} {x : B}

/-- Rank-one maps `v ↦ ⟪τ, v⟫ • σ` formed from `C^n` fields in `W` and the Riemannian
bundle `V` along a common base map form a `C^n` Hom-bundle field within the same set.
No finite-dimensionality or smooth-transition assumption is needed. -/
theorem ContMDiffWithinAt.rankOne_bundle
    (hσ : ContMDiffWithinAt IB (I.prod 𝓘(ℝ, F')) n
      (fun y ↦ TotalSpace.mk' F' (b y) (σ y)) s x)
    (hτ : ContMDiffWithinAt IB (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (τ y)) s x) :
    ContMDiffWithinAt IB (I.prod 𝓘(ℝ, F →L[ℝ] F')) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F') (E := fun y ↦ V y →L[ℝ] W y) (b y)
        (rankOne ℝ (σ y) (τ y))) s x := by
  -- Form the metric-dual covector, then tensor it with the target field in coordinates.
  have hb := (contMDiffWithinAt_totalSpace_iff.mp hτ).1
  have hdual := hτ.innerSL_bundle
  have hdual' := (contMDiffWithinAt_hom_bundle _).mp hdual
  have hσ' := (contMDiffWithinAt_totalSpace_iff.mp hσ).2
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨hb, ?_⟩
  have hp := ((ContinuousLinearMap.smulRightL ℝ F F').contDiff.comp_contMDiffWithinAt
    hdual'.2).clm_apply hσ'
  refine hp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hb.continuousWithinAt.preimage_mem_nhdsWithin
      ((trivializationAt F' W (b x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F' W (b x)))] with y hy
    -- Expose preimage membership so the coordinate evaluation lemma can consume it directly.
    change b y ∈ (trivializationAt F' W (b x)).baseSet at hy
    ext v
    simp [ContinuousLinearMap.inCoordinates, rankOne_apply,
      Trivialization.coe_linearMapAt_of_mem _ hy]
  · ext v
    simp [ContinuousLinearMap.inCoordinates, rankOne_apply,
      Trivialization.coe_linearMapAt_of_mem _
        (FiberBundle.mem_baseSet_trivializationAt F' W (b x))]

/-- Rank-one maps formed from `C^n` fields along a common base map form a `C^n`
Hom-bundle field at the same point. -/
theorem ContMDiffAt.rankOne_bundle
    (hσ : ContMDiffAt IB (I.prod 𝓘(ℝ, F')) n
      (fun y ↦ TotalSpace.mk' F' (b y) (σ y)) x)
    (hτ : ContMDiffAt IB (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (τ y)) x) :
    ContMDiffAt IB (I.prod 𝓘(ℝ, F →L[ℝ] F')) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F') (E := fun y ↦ V y →L[ℝ] W y) (b y)
        (rankOne ℝ (σ y) (τ y))) x :=
  ContMDiffWithinAt.rankOne_bundle hσ hτ

/-- Rank-one maps formed from `C^n` fields along a common base map form a `C^n`
Hom-bundle field on the same set. -/
theorem ContMDiffOn.rankOne_bundle
    (hσ : ContMDiffOn IB (I.prod 𝓘(ℝ, F')) n
      (fun y ↦ TotalSpace.mk' F' (b y) (σ y)) s)
    (hτ : ContMDiffOn IB (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (τ y)) s) :
    ContMDiffOn IB (I.prod 𝓘(ℝ, F →L[ℝ] F')) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F') (E := fun y ↦ V y →L[ℝ] W y) (b y)
        (rankOne ℝ (σ y) (τ y))) s :=
  fun x hx ↦ (hσ x hx).rankOne_bundle (hτ x hx)

/-- Rank-one maps formed from `C^n` fields along a common base map form a `C^n`
Hom-bundle field. -/
theorem ContMDiff.rankOne_bundle
    (hσ : ContMDiff IB (I.prod 𝓘(ℝ, F')) n
      (fun y ↦ TotalSpace.mk' F' (b y) (σ y)))
    (hτ : ContMDiff IB (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (τ y))) :
    ContMDiff IB (I.prod 𝓘(ℝ, F →L[ℝ] F')) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F') (E := fun y ↦ V y →L[ℝ] W y) (b y)
        (rankOne ℝ (σ y) (τ y))) :=
  fun x ↦ (hσ x).rankOne_bundle (hτ x)

end
