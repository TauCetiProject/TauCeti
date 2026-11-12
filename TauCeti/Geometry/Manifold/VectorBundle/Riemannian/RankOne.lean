/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Rank-one maps out of a Riemannian bundle

The rank-one map `v ↦ ⟪τ, v⟫ • σ` depends smoothly on fields `τ` in a
Riemannian bundle `V` and `σ` in an arbitrary normed vector bundle `W`, along the same base
map, as a field in the Hom bundle from `V` to `W`. Neither bundle needs finite rank.
Taking `W = V`, this provides smooth matrix units from orthonormal local frames, with the
native Hom-bundle topology.

The construction is Mathlib's `InnerProductSpace.rankOne`; smoothness uses the
bundle inner product and the total-space criterion for smooth homomorphisms.
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
  {b : B → M} {σ : Π y : B, W (b y)} {τ : Π y : B, V (b y)} {x : B}

/-- Rank-one maps `v ↦ ⟪τ, v⟫ • σ` formed from `C^n` fields in `W` and the Riemannian
bundle `V` along a common base map form a `C^n` Hom-bundle field at the same point.
No finite-dimensionality or smooth-transition assumption is needed. -/
theorem ContMDiffAt.rankOne_bundle
    (hσ : ContMDiffAt IB (I.prod 𝓘(ℝ, F')) n
      (fun y ↦ TotalSpace.mk' F' (b y) (σ y)) x)
    (hτ : ContMDiffAt IB (I.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (b y) (τ y)) x) :
    ContMDiffAt IB (I.prod 𝓘(ℝ, F →L[ℝ] F')) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F') (E := fun y ↦ V y →L[ℝ] W y) (b y)
        (rankOne ℝ (σ y) (τ y))) x := by
  -- First form the metric-dual covector, then tensor it with the target field in coordinates.
  obtain ⟨g, hg, heq⟩ := hmetric.exists_contMDiff
  have hb := (contMDiffAt_totalSpace_iff.mp hτ).1
  have hdual : ContMDiffAt IB (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun z ↦ V z →L[ℝ] ℝ) (b y) (innerSL ℝ (τ y))) x := by
    have hmetric_eq (y : M) : g y = innerSL ℝ := by
      ext u w
      exact (heq y u w).symm
    have h := ContMDiffAt.clm_bundle_apply (ϕ := fun y ↦ g (b y))
      (F₂ := F →L[ℝ] ℝ) (E₂ := fun z ↦ V z →L[ℝ] ℝ)
      ((hg (b x)).comp x hb) hτ
    simpa only [Function.comp_def, hmetric_eq] using h
  have hdual' := (contMDiffAt_hom_bundle _).mp hdual
  have hσ' := (contMDiffAt_totalSpace_iff.mp hσ).2
  rw [contMDiffAt_hom_bundle]
  refine ⟨hb, ?_⟩
  have hp := ((ContinuousLinearMap.smulRightL ℝ F F').contDiff.comp_contMDiffAt
    hdual'.2).clm_apply hσ'
  refine hp.congr_of_eventuallyEq ?_
  filter_upwards [hb.continuousAt.preimage_mem_nhds
    ((trivializationAt F' W (b x)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F' W (b x)))] with y hy
  -- Expose preimage membership so the coordinate evaluation lemma can consume it directly.
  change b y ∈ (trivializationAt F' W (b x)).baseSet at hy
  ext v
  simp [ContinuousLinearMap.inCoordinates, rankOne_apply,
    Trivialization.coe_linearMapAt_of_mem _ hy]

end
