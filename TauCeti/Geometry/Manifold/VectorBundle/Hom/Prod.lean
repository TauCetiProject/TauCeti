/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Smooth Hom-bundle sections into a direct sum

Let `E₁ → B` be a vector bundle and `E₂ ×ᵇ E₃ → B` a fibrewise product. The fibrewise `prod`
`x ↦ (ϕ x).prod (ψ x)` of two `C^n` sections of the bundles of linear maps `E₁ → E₂` and
`E₁ → E₃` is a `C^n` section of the bundle of linear maps `E₁ → E₂ ×ᵇ E₃`
(`ContMDiffWithinAt.clm_bundle_prod`). Read in the trivializations, the section is the `prod` of
the readings of its components (`ContinuousLinearMap.inCoordinates_prod`).

## Main results

* `ContMDiffWithinAt.clm_bundle_prod`, `ContMDiffOn.clm_bundle_prod`: the fibrewise `prod` of
  two `C^n` Hom-bundle sections is `C^n`.
-/

public section

open Bundle Set
open scoped Manifold Topology

section Smooth

variable {𝕜 B F₁ F₂ F₃ M : Type*} {n : WithTop ℕ∞} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [∀ x, TopologicalSpace (E₃ x)] [TopologicalSpace (TotalSpace F₃ E₃)]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  {b : M → B} {ϕ : ∀ m, E₁ (b m) →L[𝕜] E₂ (b m)} {ψ : ∀ m, E₁ (b m) →L[𝕜] E₃ (b m)}
  {s : Set M} {x₀ : M}

/-- The fibrewise `prod` of two `C^n` Hom-bundle sections is a `C^n` section of the Hom bundle into
the fibrewise product. -/
theorem ContMDiffWithinAt.clm_bundle_prod
    (hϕ : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) (b m) (ϕ m)) s x₀)
    (hψ : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃) (E := fun x ↦ E₁ x →L[𝕜] E₃ x) (b m) (ψ m)) s x₀) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ × F₃)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ × F₃) (E := fun x ↦ E₁ x →L[𝕜] (E₂ ×ᵇ E₃) x) (b m)
        ((ϕ m).prod (ψ m))) s x₀ := by
  rw [contMDiffWithinAt_hom_bundle] at hϕ hψ ⊢
  refine ⟨hϕ.1, ?_⟩
  have hb : ∀ᶠ m in 𝓝[s] x₀, b m ∈ (trivializationAt F₂ E₂ (b x₀)).baseSet ∧
      b m ∈ (trivializationAt F₃ E₃ (b x₀)).baseSet :=
    hϕ.1.continuousWithinAt.eventually
      (((trivializationAt F₂ E₂ (b x₀)).open_baseSet.inter
        (trivializationAt F₃ E₃ (b x₀)).open_baseSet).mem_nhds
          ⟨mem_baseSet_trivializationAt F₂ E₂ (b x₀), mem_baseSet_trivializationAt F₃ E₃ (b x₀)⟩)
  refine (((ContinuousLinearMap.prodₗᵢ 𝕜).toContinuousLinearEquiv.contDiff
    (n := n)).comp_contMDiffWithinAt (hϕ.2.prodMk_space hψ.2)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hb] with m hm
    exact ContinuousLinearMap.inCoordinates_prod hm.1 hm.2 _ _
  · exact ContinuousLinearMap.inCoordinates_prod (mem_baseSet_trivializationAt F₂ E₂ (b x₀))
      (mem_baseSet_trivializationAt F₃ E₃ (b x₀)) _ _

/-- The fibrewise `prod` of two `C^n` Hom-bundle sections is a `C^n` section of the Hom bundle into
the fibrewise product. -/
theorem ContMDiffOn.clm_bundle_prod
    (hϕ : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) (b m) (ϕ m)) s)
    (hψ : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃) (E := fun x ↦ E₁ x →L[𝕜] E₃ x) (b m) (ψ m)) s) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂ × F₃)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ × F₃) (E := fun x ↦ E₁ x →L[𝕜] (E₂ ×ᵇ E₃) x) (b m)
        ((ϕ m).prod (ψ m))) s :=
  fun x hx ↦ (hϕ x hx).clm_bundle_prod (hψ x hx)

end Smooth
