/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Defs
import TauCeti.Topology.FiberBundle.Trivialization
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Smooth determinants of bundle endomorphisms

The fibrewise determinant of a `C^n` section of `End(V)` along `b : M → B` is a `C^n` scalar
function (`ContMDiffWithinAt.clm_bundle_det` and its variants). In finite rank, an endomorphism
family induces a `C^n` automorphism of `TotalSpace F V` iff its total-space map is `C^n` and its
determinant vanishes nowhere (`TauCeti.exists_bundleDiffeomorph_iff_contMDiff_and_det_ne_zero`).

## References
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
-/

public section

noncomputable section

open Bundle FiberBundle Set
open scoped Manifold Bundle ContDiff Topology

section EndomorphismDet

variable {𝕜 EB EM HB HM B M F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [TopologicalSpace HB] [TopologicalSpace HM] {IB : ModelWithCorners 𝕜 EB HB}
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace B] [ChartedSpace HB B] [TopologicalSpace M]
  [ChartedSpace HM M] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V] {n : ℕ∞ω}

section

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  {b : M → B} {φ : ∀ y, V (b y) →L[𝕜] V (b y)} {s : Set M} {x : M}

/-- The fibrewise determinant of an endomorphism-bundle section `C^n` within `s` at `x` is a `C^n`
scalar function within `s` at `x`. Over infinite-dimensional fibres, `det` is `1`. -/
theorem ContMDiffWithinAt.clm_bundle_det (hφ : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F →L[𝕜] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F) (E := fun z ↦ V z →L[𝕜] V z) (b y) (φ y)) s x) :
    ContMDiffWithinAt IM 𝓘(𝕜) n (fun y ↦ (φ y).det) s x := by
  rw [contMDiffWithinAt_hom_bundle] at hφ
  have hdet := (ContinuousLinearMap.contDiff_det (𝕜 := 𝕜) (E := F) (r := n)).contMDiff
    |>.contMDiffAt.comp_contMDiffWithinAt x hφ.2
  have heq : (fun y ↦ (φ y).det) =ᶠ[𝓝[insert x s] x]
      fun y ↦ (ContinuousLinearMap.inCoordinates F V F V (b x) (b y) (b x) (b y) (φ y)).det := by
    filter_upwards [hφ.1.insert.continuousWithinAt.eventually_mem_baseSet_trivializationAt F V]
      with y hy
    rw [ContinuousLinearMap.inCoordinates_eq hy hy]
    exact (LinearMap.det_conj (φ y : V (b y) →ₗ[𝕜] V (b y))
      ((trivializationAt F V (b x)).continuousLinearEquivAt 𝕜 (b y) hy).toLinearEquiv).symm
  exact hdet.congr_of_eventuallyEq_insert heq

/-- The fibrewise determinant of an endomorphism-bundle section `C^n` at `x` is `C^n` at `x`. -/
theorem ContMDiffAt.clm_bundle_det (hφ : ContMDiffAt IM (IB.prod 𝓘(𝕜, F →L[𝕜] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F) (E := fun z ↦ V z →L[𝕜] V z) (b y) (φ y)) x) :
    ContMDiffAt IM 𝓘(𝕜) n (fun y ↦ (φ y).det) x := ContMDiffWithinAt.clm_bundle_det hφ

/-- The fibrewise determinant of an endomorphism-bundle section `C^n` on `s` is `C^n` on `s`. -/
theorem ContMDiffOn.clm_bundle_det (hφ : ContMDiffOn IM (IB.prod 𝓘(𝕜, F →L[𝕜] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F) (E := fun z ↦ V z →L[𝕜] V z) (b y) (φ y)) s) :
    ContMDiffOn IM 𝓘(𝕜) n (fun y ↦ (φ y).det) s := fun y hy ↦ (hφ y hy).clm_bundle_det

/-- The fibrewise determinant of a `C^n` endomorphism-bundle section is `C^n`. -/
theorem ContMDiff.clm_bundle_det (hφ : ContMDiff IM (IB.prod 𝓘(𝕜, F →L[𝕜] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F) (E := fun z ↦ V z →L[𝕜] V z) (b y) (φ y))) :
    ContMDiff IM 𝓘(𝕜) n (fun y ↦ (φ y).det) := fun y ↦ (hφ y).clm_bundle_det

end

namespace TauCeti

variable [FiniteDimensional 𝕜 F]

/-- For a finite-rank vector bundle, a family of fibrewise endomorphisms with `C^n` total-space map
has `C^n` scalar determinant. -/
theorem contMDiff_det_of_totalSpaceMap (ψ : ∀ x, V x →L[𝕜] V x)
    (hψ : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F p.proj (ψ p.proj p.snd))) :
    ContMDiff IB 𝓘(𝕜) n (fun x ↦ (ψ x).det) := by
  have : ∀ x, IsTopologicalAddGroup (V x) := VectorBundle.isTopologicalAddGroup 𝕜 F V
  have : ∀ x, ContinuousSMul 𝕜 (V x) := VectorBundle.continuousSMul 𝕜 F V
  exact ((contMDiff_hom_bundle_iff (IB := IB) ψ).2 hψ).clm_bundle_det

/-- For a finite-rank vector bundle, a family of fibrewise endomorphisms is realized by a `C^n`
automorphism of `TotalSpace F V` covering the identity iff its total-space map is `C^n` and its
fibrewise determinant vanishes nowhere. -/
theorem exists_bundleDiffeomorph_iff_contMDiff_and_det_ne_zero (ψ : ∀ x, V x →L[𝕜] V x) :
    (∃ Φ : TotalSpace F V ≃ₘ^n⟮IB.prod 𝓘(𝕜, F), IB.prod 𝓘(𝕜, F)⟯ TotalSpace F V,
        ⇑Φ = fun p ↦ TotalSpace.mk' F p.proj (ψ p.proj p.snd)) ↔
      ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
          (fun p : TotalSpace F V ↦ TotalSpace.mk' F p.proj (ψ p.proj p.snd)) ∧
        ∀ x, (ψ x).det ≠ 0 := by
  rw [exists_bundleDiffeomorph_iff]
  refine and_congr_right fun _ ↦ forall_congr' fun x ↦ ?_
  let _ : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  rw [← isUnit_iff_ne_zero, ← LinearMap.isUnit_iff_isUnit_det (ψ x : V x →ₗ[𝕜] V x),
    Module.End.isUnit_iff, ContinuousLinearMap.coe_coe]

end TauCeti

end EndomorphismDet
