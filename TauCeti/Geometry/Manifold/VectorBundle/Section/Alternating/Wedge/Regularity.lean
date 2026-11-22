/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap.Wedge

/-!
# Smoothness and regularity of paired wedges of alternating bundle sections

Regularity preservation (`ContMDiffWithinAt.pairedWedge_section`, `ContMDiffAt.pairedWedge_section`,
`ContMDiffOn.pairedWedge_section`, `ContMDiff.pairedWedge_section`) for fibrewise paired wedges
along a `C^n` bilinear bundle pairing.
-/

public section
noncomputable section

open Bundle Filter Set
open scoped Bundle ContDiff Manifold Topology
section PairedWedgeRegularity
open ContinuousAlternatingMap (pairedWedge pairedWedgeCLM inCoordinates)
variable {E H M FW F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup FW]
  [NormedSpace ℝ FW] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂]
  [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] {W V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)] {k l : ℕ} {n : ℕ∞ω}
  {u : Set M} {x : M}

/-- Regularity within a set at a point of a fibrewise paired wedge on `W`. -/
theorem _root_.ContMDiffWithinAt.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)) u x)
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁) y (φ y)) u x)
    (hψ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) u x) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃) y
        (pairedWedge (μ y) (hμ y) (φ y) (ψ y))) u x := by
  rw [contMDiffWithinAt_hom_bundle] at hpair
  rw [contMDiffWithinAt_continuousAlternatingMap_bundle] at hφ hψ ⊢; refine ⟨hφ.1, ?_⟩
  have h := (((pairedWedgeCLM (E := FW) (k := k) (l := l)).contDiff.comp_contMDiffWithinAt
    hpair.2).clm_apply hφ.2).clm_apply hψ.2
  have heq : (fun y ↦ inCoordinates FW F₃ x y x y (pairedWedge (μ y) (hμ y) (φ y) (ψ y))) =ᶠ[𝓝 x]
      fun y ↦ pairedWedgeCLM (ContinuousLinearMap.inCoordinates F₁ V₁
        (F₂ →L[ℝ] F₃) (fun z ↦ V₂ z →L[ℝ] V₃ z) x y x y (μ y))
        (inCoordinates FW F₁ x y x y (φ y)) (inCoordinates FW F₂ x y x y (ψ y)) := by
    filter_upwards
      [(trivializationAt F₁ V₁ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₁ V₁ x),
       (trivializationAt F₂ V₂ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₂ V₂ x),
       (trivializationAt F₃ V₃ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₃ V₃ x)] with y h₁ h₂ h₃ using
      TauCeti.inCoordinates_pairedWedge (μ y) (hμ y) (φ y) (ψ y) h₁ h₂ h₃
  exact h.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

/-- Pointwise regularity of a fibrewise paired wedge on `W`. -/
theorem _root_.ContMDiffAt.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)) x)
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁) y (φ y)) x)
    (hψ : ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃) y (pairedWedge (μ y) (hμ y) (φ y) (ψ y))) x :=
  ContMDiffWithinAt.pairedWedge_section hμ hpair hφ hψ

/-- Regularity on a set of a fibrewise paired wedge on `W`. -/
theorem _root_.ContMDiffOn.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffOn I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)) u)
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁) y (φ y)) u)
    (hψ : ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃) y (pairedWedge (μ y) (hμ y) (φ y) (ψ y))) u :=
  fun y hy ↦ ContMDiffWithinAt.pairedWedge_section hμ (hpair y hy) (hφ y hy) (hψ y hy)

/-- Global regularity of a fibrewise paired wedge on `W`. -/
theorem _root_.ContMDiff.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)))
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁) y (φ y)))
    (hψ : ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂) y (ψ y))) :
    ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃) y (pairedWedge (μ y) (hμ y) (φ y) (ψ y))) :=
  fun y ↦ ContMDiffAt.pairedWedge_section hμ (hpair y) (hφ y) (hψ y)
end PairedWedgeRegularity
