/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Pulling back a smooth bundle metric by a fibre isomorphism

A smooth field of continuous linear equivalences pulls back a smooth real bundle metric.
The source and target retain their original fibre topologies. The bounded-unit-set condition
is transported using the continuous inverse, without any finite-dimensionality assumption.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013), Chapter 13.
-/

public noncomputable section

open Bundle Bornology
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {X H B F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V W : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]
  {n : ℕ∞ω}

/-- Pull back a smooth metric by a smooth field of continuous linear fibre equivalences.
The inverse preserves the bounded-unit-set condition, so the original topology is retained. -/
def pullbackBundleEquiv (g : ContMDiffRiemannianMetric IB n G W)
    (A : ∀ x, V x ≃L[ℝ] W x)
    (hA : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] G)) n
      (fun x ↦ (⟨x, (A x).toContinuousLinearMap⟩ :
        TotalSpace (F →L[ℝ] G) (fun y ↦ V y →L[ℝ] W y)))) :
    ContMDiffRiemannianMetric IB n F V := by
  let : ∀ x, IsNormableSpace ℝ (V x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt ℝ F V x).isNormableSpace
  let : ∀ x, IsNormableSpace ℝ (W x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt ℝ G W x).isNormableSpace
  refine
    { inner := fun x ↦ (g.inner x).bilinearComp (A x).toContinuousLinearMap
        (A x).toContinuousLinearMap
      symm := fun x v w ↦ g.symm x (A x v) (A x w)
      pos := fun x v hv ↦ g.pos x (A x v) (by
        simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using hv)
      isVonNBounded := fun x ↦ ?_
      contMDiff := ?_ }
  · refine ((g.isVonNBounded x).image (A x).symm.toContinuousLinearMap).subset ?_
    intro v hv
    exact ⟨A x v, hv, (A x).symm_apply_apply v⟩
  · intro x
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    let a (y : B) := ContinuousLinearMap.inCoordinates F V G W x y x y
      (A y).toContinuousLinearMap
    let q (y : B) := ContinuousLinearMap.inCoordinates G W (G →L[ℝ] ℝ)
      (fun z ↦ W z →L[ℝ] ℝ) x y x y (g.inner y)
    have ha : ContMDiffAt IB 𝓘(ℝ, F →L[ℝ] G) n a x :=
      ((contMDiffAt_hom_bundle _).mp (hA x)).2
    have hq : ContMDiffAt IB 𝓘(ℝ, G →L[ℝ] G →L[ℝ] ℝ) n q x :=
      ((contMDiffAt_hom_bundle _).mp (g.contMDiff x)).2
    have hc := (ha.clm_precomp (F₃ := ℝ)).clm_comp (hq.clm_comp ha)
    apply hc.congr_of_eventuallyEq
    filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F V x),
      (trivializationAt G W x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt G W x)] with y hyV hyW
    dsimp only [a, q]
    ext v w
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
    rw [inCoordinates_apply_eq₂ hyV hyV (by simp),
      inCoordinates_apply_eq₂ hyW hyW (by simp)]
    simp [ContinuousLinearMap.inCoordinates, hyV, hyW]

/-- Evaluation of the pulled-back metric uses the original metric on the images. -/
@[simp]
theorem pullbackBundleEquiv_inner (g : ContMDiffRiemannianMetric IB n G W)
    (A : ∀ x, V x ≃L[ℝ] W x)
    (hA : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] G)) n
      (fun x ↦ (⟨x, (A x).toContinuousLinearMap⟩ :
        TotalSpace (F →L[ℝ] G) (fun y ↦ V y →L[ℝ] W y))))
    (x : B) (v w : V x) :
    (g.pullbackBundleEquiv A hA).inner x v w = g.inner x (A x v) (A x w) := by
  simp only [pullbackBundleEquiv, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe]

end Bundle.ContMDiffRiemannianMetric
