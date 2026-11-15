/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
public import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic

/-!
# Smooth determinants of bundle endomorphisms and pullback of alternating forms

Reading an endomorphism of a vector-bundle fibre in any local trivialization conjugates it by the
fibre equivalence of that trivialization, so its scalar determinant `ContinuousLinearMap.det`
agrees locally with the determinant of its coordinate operator. Combining this invariance with
`ContinuousLinearMap.contDiff_det` shows that the fibrewise determinant of a `C^n` section of
`End(V)` along `b : M → B` is a `C^n` scalar function (`ContMDiffWithinAt.clm_bundle_det` and its
variants), over any complete nontrivially normed field and without finite-dimensionality or bundle
chart-transition smoothness assumptions. When the model fibre is finite-dimensional, an
endomorphism family induces a `C^n` bundle automorphism of `TotalSpace F V` if and only if it is
`C^n` and its determinant vanishes nowhere (`TauCeti.exists_bundleDiffeomorph_iff_det_ne_zero`).

For bundles of continuous alternating maps, fibrewise domain pullback
`ContinuousAlternatingMap.compContinuousLinearMap` along a `C^n` Hom-bundle section preserves `C^n`
regularity of alternating-map sections (`ContMDiffWithinAt.continuousAlternatingMap_comp_clm`), with
the arity-factorial condition required only at the analytic order `ω`. In top degree
(`Fintype.card ι = Module.finrank 𝕜 F`), pulling back any scalar-valued top-degree form along an
endomorphism multiplies it by the endomorphism's determinant
(`TauCeti.bundleTopForm_compContinuousLinearMap_eq_det_smul`).

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 14 (Differential Forms).
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Section 2.2.
-/

public section

noncomputable section

open Bundle FiberBundle Set
open scoped Manifold Bundle ContDiff Topology

section EndomorphismDet

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EB EM : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HB HM : Type*} [TopologicalSpace HB] [TopologicalSpace HM]
  {IB : ModelWithCorners 𝕜 EB HB} {IM : ModelWithCorners 𝕜 EM HM}
  {B M : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace M] [ChartedSpace HM M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {b : M → B} {φ : ∀ y, V (b y) →L[𝕜] V (b y)} {s : Set M} {x : M} {n : ℕ∞ω}

/-- The fibrewise determinant of an endomorphism-bundle section `C^n` within `s` at `x` is a `C^n`
scalar function within `s` at `x`. Over infinite-dimensional fibres, `ContinuousLinearMap.det` is
identically `1` by convention. -/
theorem ContMDiffWithinAt.clm_bundle_det
    (hφ : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F →L[𝕜] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F) (E := fun z ↦ V z →L[𝕜] V z) (b y) (φ y)) s x) :
    ContMDiffWithinAt IM 𝓘(𝕜) n (fun y ↦ (φ y).det) s x := by
  rw [contMDiffWithinAt_hom_bundle] at hφ
  have hnear := hφ.1.insert.continuousWithinAt.preimage_mem_nhdsWithin
    ((trivializationAt F V (b x)).open_baseSet.mem_nhds (mem_baseSet_trivializationAt' (b x)))
  have hdet := (ContinuousLinearMap.contDiff_det (𝕜 := 𝕜) (E := F) (r := n)).contMDiff
    |>.contMDiffAt.comp_contMDiffWithinAt x hφ.2
  have heq : (fun y ↦ (φ y).det) =ᶠ[𝓝[insert x s] x]
      fun y ↦ (ContinuousLinearMap.inCoordinates F V F V (b x) (b y) (b x) (b y) (φ y)).det := by
    filter_upwards [hnear] with y hy
    let e := (trivializationAt F V (b x)).continuousLinearEquivAt 𝕜 (b y) hy
    rw [ContinuousLinearMap.inCoordinates_eq hy hy]
    exact (LinearMap.det_conj (φ y : V (b y) →ₗ[𝕜] V (b y)) e.toLinearEquiv).symm
  exact hdet.congr_of_eventuallyEq (heq.filter_mono (nhdsWithin_mono _ (subset_insert x s)))
    (heq.self_of_nhdsWithin (mem_insert x s))

/-- The fibrewise determinant of an endomorphism-bundle section `C^n` at `x` is `C^n` at `x`. -/
theorem ContMDiffAt.clm_bundle_det
    (hφ : ContMDiffAt IM (IB.prod 𝓘(𝕜, F →L[𝕜] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F) (E := fun z ↦ V z →L[𝕜] V z) (b y) (φ y)) x) :
    ContMDiffAt IM 𝓘(𝕜) n (fun y ↦ (φ y).det) x :=
  ContMDiffWithinAt.clm_bundle_det hφ

/-- The fibrewise determinant of an endomorphism-bundle section `C^n` on `s` is `C^n` on `s`. -/
theorem ContMDiffOn.clm_bundle_det
    (hφ : ContMDiffOn IM (IB.prod 𝓘(𝕜, F →L[𝕜] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F) (E := fun z ↦ V z →L[𝕜] V z) (b y) (φ y)) s) :
    ContMDiffOn IM 𝓘(𝕜) n (fun y ↦ (φ y).det) s :=
  fun y hy ↦ (hφ y hy).clm_bundle_det

/-- The fibrewise determinant of a `C^n` endomorphism-bundle section is `C^n`. -/
theorem ContMDiff.clm_bundle_det
    (hφ : ContMDiff IM (IB.prod 𝓘(𝕜, F →L[𝕜] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[𝕜] F) (E := fun z ↦ V z →L[𝕜] V z) (b y) (φ y))) :
    ContMDiff IM 𝓘(𝕜) n (fun y ↦ (φ y).det) :=
  fun y ↦ (hφ y).clm_bundle_det

namespace TauCeti

variable [FiniteDimensional 𝕜 F]

/-- For a finite-rank vector bundle, a family of fibrewise endomorphisms with `C^n` total-space map
has `C^n` scalar determinant. -/
theorem contMDiff_det_of_totalSpaceMap (ψ : ∀ x, V x →L[𝕜] V x)
    (hψ : ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F p.proj (ψ p.proj p.2))) :
    ContMDiff IB 𝓘(𝕜) n (fun x ↦ (ψ x).det) :=
  ((contMDiff_hom_bundle_iff (IB := IB) ψ).2 hψ).clm_bundle_det

/-- For a finite-rank vector bundle, a family of fibrewise endomorphisms is realized by a `C^n`
automorphism of `TotalSpace F V` covering the identity if and only if its total-space map is `C^n`
and its fibrewise determinant vanishes nowhere. -/
theorem exists_bundleDiffeomorph_iff_det_ne_zero (ψ : ∀ x, V x →L[𝕜] V x) :
    (∃ Φ : TotalSpace F V ≃ₘ^n⟮IB.prod 𝓘(𝕜, F), IB.prod 𝓘(𝕜, F)⟯ TotalSpace F V,
        ⇑Φ = fun p ↦ TotalSpace.mk' F p.proj (ψ p.proj p.2)) ↔
      ContMDiff (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) n
          (fun p : TotalSpace F V ↦ TotalSpace.mk' F p.proj (ψ p.proj p.2)) ∧
        ∀ x, (ψ x).det ≠ 0 := by
  rw [exists_bundleDiffeomorph_iff]
  refine and_congr_right fun _ ↦ forall_congr' fun x ↦ ?_
  let _ : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  rw [ContinuousLinearMap.det, ← isUnit_iff_ne_zero,
    ← LinearMap.isUnit_iff_isUnit_det (ψ x : V x →ₗ[𝕜] V x), Module.End.isUnit_iff]
  rfl

end TauCeti

end EndomorphismDet

section AlternatingPullback

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  {EB EM : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HB HM : Type*} [TopologicalSpace HB] [TopologicalSpace HM]
  {IB : ModelWithCorners 𝕜 EB HB} {IM : ModelWithCorners 𝕜 EM HM}
  {B M : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace M] [ChartedSpace HM M]
  {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {V₁ V₂ V₃ : B → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module 𝕜 (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul 𝕜 (V₃ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [TopologicalSpace (TotalSpace F₃ V₃)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  [FiberBundle F₃ V₃] [VectorBundle 𝕜 F₃ V₃]
  {b : M → B} {α : ∀ y, V₂ (b y) [⋀^ι]→L[𝕜] V₃ (b y)} {A : ∀ y, V₁ (b y) →L[𝕜] V₂ (b y)}
  {s : Set M} {x : M} {n : ℕ∞ω}

/-- Pulling back a `C^n` section of an alternating-map bundle along a `C^n` Hom-bundle section over
the same base map `b` preserves `C^n` regularity within `s` at `x`. Only the analytic order `ω`
carries the arity-factorial condition. -/
theorem ContMDiffWithinAt.continuousAlternatingMap_comp_clm
    (hα : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₂ [⋀^ι]→L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₂ [⋀^ι]→L[𝕜] F₃)
        (E := fun z ↦ V₂ z [⋀^ι]→L[𝕜] V₃ z) (b y) (α y)) s x)
    (hA : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun z ↦ V₁ z →L[𝕜] V₂ z) (b y) (A y)) s x)
    (hn : n = ω → ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
      intro h; first | exact NeZero.ne _ | cases h) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₃)
        (E := fun z ↦ V₁ z [⋀^ι]→L[𝕜] V₃ z) (b y) ((α y).compContinuousLinearMap (A y))) s x := by
  let _ : NormedAddCommGroup ((F₂ [⋀^ι]→L[𝕜] F₃) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₃) := inferInstance
  let _ : NormedSpace 𝕜 ((F₂ [⋀^ι]→L[𝕜] F₃) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₃) := inferInstance
  rw [contMDiffWithinAt_continuousAlternatingMap_bundle] at hα ⊢
  rw [contMDiffWithinAt_hom_bundle] at hA
  refine ⟨hA.1, ?_⟩
  have hnear := hA.1.insert.continuousWithinAt.preimage_mem_nhdsWithin
    ((trivializationAt F₂ V₂ (b x)).open_baseSet.mem_nhds (mem_baseSet_trivializationAt' (b x)))
  have hpull := (ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := 𝕜) (E := F₁) (F := F₂) (G := F₃) (ι := ι) n hn).contMDiff.contMDiffAt
    |>.comp_contMDiffWithinAt x hA.2 |>.clm_apply hα.2
  have heq : (fun y ↦ ContinuousAlternatingMap.inCoordinates F₁ F₃ (b x) (b y) (b x) (b y)
      ((α y).compContinuousLinearMap (A y))) =ᶠ[𝓝[insert x s] x]
      fun y ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM
        (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ (b x) (b y) (b x) (b y) (A y))
        (ContinuousAlternatingMap.inCoordinates F₂ F₃ (b x) (b y) (b x) (b y) (α y)) := by
    filter_upwards [hnear] with y hy
    exact ContinuousAlternatingMap.inCoordinates_compContinuousLinearMap (α y) (A y) hy
  exact hpull.congr_of_eventuallyEq (heq.filter_mono (nhdsWithin_mono _ (subset_insert x s)))
    (heq.self_of_nhdsWithin (mem_insert x s))

/-- Pulling back a `C^n` section of an alternating-map bundle along a `C^n` Hom-bundle section at
`x` is `C^n` at `x`. -/
theorem ContMDiffAt.continuousAlternatingMap_comp_clm
    (hα : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₂ [⋀^ι]→L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₂ [⋀^ι]→L[𝕜] F₃)
        (E := fun z ↦ V₂ z [⋀^ι]→L[𝕜] V₃ z) (b y) (α y)) x)
    (hA : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun z ↦ V₁ z →L[𝕜] V₂ z) (b y) (A y)) x)
    (hn : n = ω → ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
      intro h; first | exact NeZero.ne _ | cases h) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₃)
        (E := fun z ↦ V₁ z [⋀^ι]→L[𝕜] V₃ z) (b y) ((α y).compContinuousLinearMap (A y))) x :=
  ContMDiffWithinAt.continuousAlternatingMap_comp_clm hα hA hn

/-- Pulling back a `C^n` section of an alternating-map bundle along a `C^n` Hom-bundle section on
`s` is `C^n` on `s`. -/
theorem ContMDiffOn.continuousAlternatingMap_comp_clm
    (hα : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₂ [⋀^ι]→L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₂ [⋀^ι]→L[𝕜] F₃)
        (E := fun z ↦ V₂ z [⋀^ι]→L[𝕜] V₃ z) (b y) (α y)) s)
    (hA : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun z ↦ V₁ z →L[𝕜] V₂ z) (b y) (A y)) s)
    (hn : n = ω → ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
      intro h; first | exact NeZero.ne _ | cases h) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₃)
        (E := fun z ↦ V₁ z [⋀^ι]→L[𝕜] V₃ z) (b y) ((α y).compContinuousLinearMap (A y))) s :=
  fun y hy ↦ (hα y hy).continuousAlternatingMap_comp_clm (hA y hy) hn

/-- Pulling back a `C^n` section of an alternating-map bundle along a `C^n` Hom-bundle section is
`C^n`. -/
theorem ContMDiff.continuousAlternatingMap_comp_clm
    (hα : ContMDiff IM (IB.prod 𝓘(𝕜, F₂ [⋀^ι]→L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₂ [⋀^ι]→L[𝕜] F₃)
        (E := fun z ↦ V₂ z [⋀^ι]→L[𝕜] V₃ z) (b y) (α y)))
    (hA : ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun z ↦ V₁ z →L[𝕜] V₂ z) (b y) (A y)))
    (hn : n = ω → ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
      intro h; first | exact NeZero.ne _ | cases h) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F₁ [⋀^ι]→L[𝕜] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ [⋀^ι]→L[𝕜] F₃)
        (E := fun z ↦ V₁ z [⋀^ι]→L[𝕜] V₃ z) (b y) ((α y).compContinuousLinearMap (A y))) :=
  fun y ↦ (hα y).continuousAlternatingMap_comp_clm (hA y) hn

end AlternatingPullback

namespace TauCeti

section TopFormBundle

variable {𝕜 ι B F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- On a finite-rank vector bundle `V` of model rank `Fintype.card ι`, pulling back any scalar
top-degree alternating form in the fibre `V x [⋀^ι]→L[𝕜] 𝕜` along a continuous linear endomorphism
`A : V x →L[𝕜] V x` multiplies the form by `A.det`. -/
theorem bundleTopForm_compContinuousLinearMap_eq_det_smul
    (h : Fintype.card ι = Module.finrank 𝕜 F) {x : B}
    (α : V x [⋀^ι]→L[𝕜] 𝕜) (A : V x →L[𝕜] V x) :
    α.compContinuousLinearMap A = A.det • α := by
  let _ : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  let e := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x (mem_baseSet_trivializationAt F V x)
  exact α.compContinuousLinearMap_eq_det_smul (h.trans e.toLinearEquiv.symm.finrank_eq) A

end TopFormBundle

end TauCeti
