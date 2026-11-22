/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Topology.VectorBundle.ContinuousAlternatingMap.Wedge

/-!
# Wedge products of alternating bundle sections

Smooth/regularity preservation for paired wedges (`ContMDiffWithinAt.pairedWedge_section`,
`ContMDiffAt.pairedWedge_section`, `ContMDiffOn.pairedWedge_section`,
`ContMDiff.pairedWedge_section`), the `C^n(M, ℝ)`-bilinear paired wedge
`ContMDiffSection.pairedWedge`, and the scalar wedge product `ContMDiffSection.wedge` with its
graded commutativity, associativity, degree-zero, and interior-antiderivation laws.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer (2013), Chs. 12, 14.
* The paired-wedge coordinate and regularity design follows
  `TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Bundle` (`inCoordinates_bundleWedgeWith`,
  `ContMDiffWithinAt.bundleWedgeWith_form`), built on `ContinuousAlternatingMap.pairedWedge` /
  `ContinuousAlternatingMap.pairedWedgeCLM` and Yury Kudryashov's `DeRhamCohomology` project.
-/

public section
noncomputable section

open Bundle Filter Set
open scoped Bundle ContDiff Manifold Topology

section PairedWedgeRegularity
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
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]
  {k l : ℕ} {n : ℕ∞ω} {u : Set M} {x : M}

/-- Regularity within a set at a point of a fibrewise paired wedge on `W`. -/
theorem _root_.ContMDiffWithinAt.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) (E := fun z ↦ V₁ z →L[ℝ] V₂ z →L[ℝ] V₃ z) y (μ y)) u x)
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁) (E := fun z ↦ W z [⋀^Fin k]→L[ℝ] V₁ z) y (φ y)) u x)
    (hψ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂) (E := fun z ↦ W z [⋀^Fin l]→L[ℝ] V₂ z) y (ψ y)) u x) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃) (E := fun z ↦ W z [⋀^Fin (k + l)]→L[ℝ] V₃ z) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) u x := by
  rw [contMDiffWithinAt_hom_bundle] at hpair
  rw [contMDiffWithinAt_continuousAlternatingMap_bundle] at hφ hψ ⊢
  refine ⟨hφ.1, ?_⟩
  have h := (((ContinuousAlternatingMap.pairedWedgeCLM (E := FW) (k := k) (l := l)).contDiff
    |>.comp_contMDiffWithinAt hpair.2).clm_apply hφ.2).clm_apply hψ.2
  have heq : (fun y ↦ ContinuousAlternatingMap.inCoordinates FW F₃ x y x y
      (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) =ᶠ[𝓝 x] fun y ↦
      ContinuousAlternatingMap.pairedWedgeCLM
        (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[ℝ] F₃) (fun z ↦ V₂ z →L[ℝ] V₃ z)
          x y x y (μ y))
        (ContinuousAlternatingMap.inCoordinates FW F₁ x y x y (φ y))
        (ContinuousAlternatingMap.inCoordinates FW F₂ x y x y (ψ y)) := by
    filter_upwards [(trivializationAt F₁ V₁ x).open_baseSet.mem_nhds
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
    (hpair : ContMDiffAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) (E := fun z ↦ V₁ z →L[ℝ] V₂ z →L[ℝ] V₃ z) y (μ y)) x)
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁) (E := fun z ↦ W z [⋀^Fin k]→L[ℝ] V₁ z) y (φ y)) x)
    (hψ : ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂) (E := fun z ↦ W z [⋀^Fin l]→L[ℝ] V₂ z) y (ψ y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃) (E := fun z ↦ W z [⋀^Fin (k + l)]→L[ℝ] V₃ z) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) x :=
  ContMDiffWithinAt.pairedWedge_section hμ hpair hφ hψ

/-- Regularity on a set of a fibrewise paired wedge on `W`. -/
theorem _root_.ContMDiffOn.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffOn I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) (E := fun z ↦ V₁ z →L[ℝ] V₂ z →L[ℝ] V₃ z) y (μ y)) u)
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁) (E := fun z ↦ W z [⋀^Fin k]→L[ℝ] V₁ z) y (φ y)) u)
    (hψ : ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂) (E := fun z ↦ W z [⋀^Fin l]→L[ℝ] V₂ z) y (ψ y)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃) (E := fun z ↦ W z [⋀^Fin (k + l)]→L[ℝ] V₃ z) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) u :=
  fun y hy ↦ ContMDiffWithinAt.pairedWedge_section hμ (hpair y hy) (hφ y hy) (hψ y hy)

/-- Global regularity of a fibrewise paired wedge on `W`. -/
theorem _root_.ContMDiff.pairedWedge_section {μ : ∀ y, V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) (E := fun z ↦ V₁ z →L[ℝ] V₂ z →L[ℝ] V₃ z) y (μ y)))
    {φ : ∀ y, W y [⋀^Fin k]→L[ℝ] V₁ y} {ψ : ∀ y, W y [⋀^Fin l]→L[ℝ] V₂ y}
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin k]→L[ℝ] F₁)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin k]→L[ℝ] F₁) (E := fun z ↦ W z [⋀^Fin k]→L[ℝ] V₁ z) y (φ y)))
    (hψ : ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin l]→L[ℝ] F₂)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin l]→L[ℝ] F₂) (E := fun z ↦ W z [⋀^Fin l]→L[ℝ] V₂ z) y (ψ y))) :
    ContMDiff I (I.prod 𝓘(ℝ, FW [⋀^Fin (k + l)]→L[ℝ] F₃)) n (fun y ↦
      TotalSpace.mk' (FW [⋀^Fin (k + l)]→L[ℝ] F₃) (E := fun z ↦ W z [⋀^Fin (k + l)]→L[ℝ] V₃ z) y
        (ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y))) :=
  fun y ↦ ContMDiffAt.pairedWedge_section hμ (hpair y) (hφ y) (hψ y)

/-- Fibrewise paired wedge on sections of `Alt^•(W, Vᵢ)` along a `C^n` pairing section `μ`. -/
def _root_.ContMDiffSection.pairedWedge
    (μ : Cₛ^n⟮I; F₁ →L[ℝ] F₂ →L[ℝ] F₃, fun x ↦ V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x⟯)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b)) :
    Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] F₁, fun x ↦ W x [⋀^Fin k]→L[ℝ] V₁ x⟯ →ₗ[C^n⟮I, M; ℝ⟯]
      Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] F₂, fun x ↦ W x [⋀^Fin l]→L[ℝ] V₂ x⟯ →ₗ[C^n⟮I, M; ℝ⟯]
        Cₛ^n⟮I; FW [⋀^Fin (k + l)]→L[ℝ] F₃, fun x ↦ W x [⋀^Fin (k + l)]→L[ℝ] V₃ x⟯ :=
  LinearMap.mk₂ C^n⟮I, M; ℝ⟯
    (fun φ ψ ↦ ⟨fun y ↦ ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y),
      μ.contMDiff.pairedWedge_section hμ φ.contMDiff ψ.contMDiff⟩)
    (fun _ _ _ ↦ by ext y v; simp) (fun _ _ _ ↦ by ext y v; simp)
    (fun _ _ _ ↦ by ext y v; simp) (fun _ _ _ ↦ by ext y v; simp)

@[simp] theorem _root_.ContMDiffSection.pairedWedge_apply
    (μ : Cₛ^n⟮I; F₁ →L[ℝ] F₂ →L[ℝ] F₃, fun x ↦ V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x⟯)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] F₁, fun x ↦ W x [⋀^Fin k]→L[ℝ] V₁ x⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] F₂, fun x ↦ W x [⋀^Fin l]→L[ℝ] V₂ x⟯) (y : M) :
    ContMDiffSection.pairedWedge μ hμ φ ψ y =
      ContinuousAlternatingMap.pairedWedge (μ y) (hμ y) (φ y) (ψ y) := by
  simp [ContMDiffSection.pairedWedge]
end PairedWedgeRegularity

namespace ContMDiffSection

section Wedge
variable {E H M FW : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup FW] [NormedSpace ℝ FW] {W : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W] {n : ℕ∞ω}

/-- `C^n(M, ℝ)`-bilinear scalar wedge product on alternating bundle sections valued in `ℝ`. -/
def wedge {k l : ℕ} :
    Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯ →ₗ[C^n⟮I, M; ℝ⟯]
      Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯ →ₗ[C^n⟮I, M; ℝ⟯]
        Cₛ^n⟮I; FW [⋀^Fin (k + l)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + l)]→L[ℝ] ℝ⟯ :=
  pairedWedge (F₁ := ℝ) (F₂ := ℝ) (F₃ := ℝ) (V₁ := Bundle.Trivial M ℝ) (V₂ := Bundle.Trivial M ℝ)
    (V₃ := Bundle.Trivial M ℝ) ⟨fun _ ↦ ContinuousLinearMap.mul ℝ ℝ,
      TauCeti.contMDiff_const_bundlePairing (ContinuousLinearMap.mul ℝ ℝ)⟩
    (fun _ ↦ (ContinuousLinearMap.mul ℝ ℝ).continuous₂)

theorem wedge_apply' {k l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯) (y : M) :
    wedge φ ψ y = ContinuousAlternatingMap.pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ y) (ψ y) := by simp [wedge]

theorem wedge_apply {k l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + l) → W y) :
    wedge φ ψ y v = (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
      ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
        (φ y (fun i ↦ v (σ (Fin.castAdd l i))) * ψ y (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  rw [wedge_apply', ContinuousAlternatingMap.pairedWedge_apply]; simp

@[simp] theorem wedge_apply_one_one
    (φ ψ : Cₛ^n⟮I; FW [⋀^Fin 1]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 1]→L[ℝ] ℝ⟯) (y : M) (v w : W y) :
    wedge φ ψ y ![v, w] = φ y ![v] * ψ y ![w] - φ y ![w] * ψ y ![v] := by rw [wedge_apply']; simp

@[simp] theorem wedge_apply_zero_left {l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (0 + l) → W y) :
    wedge φ ψ y v = φ y 0 * ψ y (v ∘ Fin.cast (Nat.zero_add l).symm) := by rw [wedge_apply']; simp

/-- Pointwise graded commutativity of the scalar wedge product:
`(φ ∧ ψ)_y = (-1)^(k * l) (ψ ∧ φ)_y` after reindexing. -/
theorem wedge_comm_apply {k l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + l) → W y) :
    wedge φ ψ y v = (-1 : ℝ) ^ (k * l) • wedge ψ φ y (v ∘ Fin.cast (Nat.add_comm l k)) := by
  rw [wedge_apply', wedge_apply']; exact ContinuousAlternatingMap.pairedWedge_comm
    (ContinuousLinearMap.mul ℝ ℝ).continuous₂ mul_comm (φ y) (ψ y) v

@[simp] theorem wedge_apply_zero_right {k : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + 0) → W y) :
    wedge φ ψ y v = φ y (v ∘ Fin.cast (Nat.add_zero k).symm) * ψ y 0 := by rw [wedge_apply']; simp

/-- Pointwise associativity of the scalar wedge product: `(φ ∧ ψ) ∧ χ = φ ∧ (ψ ∧ χ)`. -/
theorem wedge_assoc_apply {k l m : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯)
    (χ : Cₛ^n⟮I; FW [⋀^Fin m]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin m]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + l + m) → W y) :
    wedge (wedge φ ψ) χ y v =
      wedge φ (wedge ψ χ) y (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  let μ := (ContinuousLinearMap.mul ℝ ℝ).continuous₂
  simpa only [wedge_apply'] using ContinuousAlternatingMap.pairedWedge_assoc _ _ _ _
    μ μ μ μ mul_assoc (φ y) (ψ y) (χ y) v

/-- Graded antiderivation rule for `interior` across `wedge`. -/
theorem interior_wedge_apply {k l : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯)
    (y : M) (v : Fin (k + 1 + l) → W y) :
    interior (k := k + 1 + l) s (wedge φ ψ) y v =
      wedge (interior s φ) ψ y (v ∘ Fin.cast (show k + (l + 1) = k + 1 + l by omega)) +
        (-1 : ℝ) ^ (k + 1) • wedge φ (interior s ψ) y v := by
  simp only [interior_eq_curryLeftTopological, wedge_apply']
  exact ContinuousAlternatingMap.curryLeftTopological_pairedWedge
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂ (φ y) (ψ y) (s y) v

/-- Wedging on the left with a degree-`0` section scales by the underlying function. -/
theorem wedge_zero_left {l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 0]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    wedge φ ψ = LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯)
      (M := fun q : ℕ ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin q]→L[ℝ] ℝ⟯)
      (Nat.zero_add l).symm (trivialEquiv (alternatingIsEmptyEquiv φ) • ψ) := by
  ext x v; rw [wedge_apply_zero_left, alternating_cast_apply, smul_apply]; simp

/-- Wedging on the right with a degree-`0` section scales by the underlying function. -/
theorem wedge_zero_right {k : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin 0]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin 0]→L[ℝ] ℝ⟯) :
    wedge φ ψ = LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯)
      (M := fun q : ℕ ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin q]→L[ℝ] ℝ⟯)
      (Nat.add_zero k).symm (trivialEquiv (alternatingIsEmptyEquiv ψ) • φ) := by
  ext x v; rw [wedge_apply_zero_right, alternating_cast_apply, smul_apply]; simp [mul_comm]

/-- Graded commutativity of the scalar wedge product as an identity of sections. -/
theorem wedge_comm {k l : ℕ}
    (φ : Cₛ^n⟮I; FW [⋀^Fin k]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin k]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin l]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin l]→L[ℝ] ℝ⟯) :
    wedge φ ψ = (-1 : ℝ) ^ (k * l) • LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯)
      (M := fun q : ℕ ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin q]→L[ℝ] ℝ⟯)
      (Nat.add_comm l k) (wedge ψ φ) := by
  ext x v; rw [wedge_comm_apply, coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    alternating_cast_apply]

/-- Bundled graded antiderivation rule for `interior` across `wedge`. -/
theorem interior_wedge {k l : ℕ} (s : Cₛ^n⟮I; FW, W⟯)
    (φ : Cₛ^n⟮I; FW [⋀^Fin (k + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (k + 1)]→L[ℝ] ℝ⟯)
    (ψ : Cₛ^n⟮I; FW [⋀^Fin (l + 1)]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin (l + 1)]→L[ℝ] ℝ⟯) :
    interior (k := k + 1 + l) s (wedge φ ψ) =
      LinearEquiv.cast (R := C^n⟮I, M; ℝ⟯)
        (M := fun q : ℕ ↦ Cₛ^n⟮I; FW [⋀^Fin q]→L[ℝ] ℝ, fun x ↦ W x [⋀^Fin q]→L[ℝ] ℝ⟯)
        (show k + (l + 1) = k + 1 + l by omega) (wedge (interior s φ) ψ) +
        (-1 : ℝ) ^ (k + 1) • wedge φ (interior s ψ) := by
  ext x v; rw [interior_wedge_apply, coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    alternating_cast_apply, coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply]
end Wedge

end ContMDiffSection
