/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Smooth paired wedges with bundle coefficients

A smooth fibrewise bilinear pairing sends two smooth bundle-valued differential forms to a
smooth form in its target bundle. The pairing may vary with the base point, and none of the
value bundles needs a global trivialization or a norm on its individual fibres.

`ContMDiffWithinAt.bundleWedgeWith_form` gives the relative regularity statement, including
boundary and corner points. `SmoothBundleForm.wedgeWith` packages the smooth product as a
bilinear map. In bundle coordinates the product is the continuous trilinear paired wedge on
the model fibres, applied to the coordinates of the pairing and of the two forms.

The wedge normalization and bundle-valued construction follow John M. Lee,
*Introduction to Smooth Manifolds*, second edition, Chapter 14, and the paired-wedge design
of Yury Kudryashov's `DeRhamCohomology`.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]
  [IsManifold I 1 M] {k l : ℕ} {n : WithTop ℕ∞} {s : Set M} {x : M}

/-- In valid coefficient trivializations, coordinates of a bundle wedge are the paired wedge
of the coordinates, with the pairing itself also expressed in coordinates. -/
theorem inCoordinates_bundleWedgeWith
    (μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l) (x₀ y : M)
    (h₁ : y ∈ (trivializationAt F₁ V₁ x₀).baseSet)
    (h₂ : y ∈ (trivializationAt F₂ V₂ x₀).baseSet)
    (h₃ : y ∈ (trivializationAt F₃ V₃ x₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates E F₃ x₀ y x₀ y (bundleWedgeWith μ hμ φ ψ y) =
      ContinuousAlternatingMap.pairedWedgeCLM
        (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[ℝ] F₃)
          (fun z ↦ V₂ z →L[ℝ] V₃ z) x₀ y x₀ y (μ y))
        (ContinuousAlternatingMap.inCoordinates E F₁ x₀ y x₀ y (φ y))
        (ContinuousAlternatingMap.inCoordinates E F₂ x₀ y x₀ y (ψ y)) := by
  ext v
  simp only [ContinuousAlternatingMap.pairedWedgeCLM_apply,
    ContinuousAlternatingMap.inCoordinates, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
    bundleWedgeWith_apply', ContinuousAlternatingMap.pairedWedge_apply,
    map_smul, map_sum]
  congr 2
  funext σ
  rw [ContinuousLinearMap.map_smul_of_tower, inCoordinates_apply_eq₂ h₁ h₂ h₃]
  simp only [Trivialization.continuousLinearMapAt_apply,
    Trivialization.symm_linearMapAt _ h₁, Trivialization.symm_linearMapAt _ h₂,
    Function.comp_def]

variable [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]

/-- A smooth bundle pairing takes two `C^n` bundle-valued forms to a `C^n` form within an
arbitrary set. -/
theorem _root_.ContMDiffWithinAt.bundleWedgeWith_form
    {μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffWithinAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)) s x)
    {φ : RoughBundleForm I M V₁ k} {ψ : RoughBundleForm I M V₂ l}
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F₁) y (φ y)) s x)
    (hψ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) s x) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + l)]→L[ℝ] F₃) y
        (bundleWedgeWith μ hμ φ ψ y)) s x := by
  rw [contMDiffWithinAt_hom_bundle] at hpair
  rw [contMDiffWithinAt_continuousAlternatingMap_bundle] at hφ hψ ⊢
  refine ⟨hφ.1, ?_⟩
  have h := (((ContinuousAlternatingMap.pairedWedgeCLM
    (E := E) (k := k) (l := l)).contDiff.comp_contMDiffWithinAt hpair.2).clm_apply
      hφ.2).clm_apply hψ.2
  have heq : (fun y ↦ ContinuousAlternatingMap.inCoordinates E F₃ x y x y
      (bundleWedgeWith μ hμ φ ψ y)) =ᶠ[𝓝 x]
      (fun y ↦ ContinuousAlternatingMap.pairedWedgeCLM
        (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[ℝ] F₃)
          (fun z ↦ V₂ z →L[ℝ] V₃ z) x y x y (μ y))
        (ContinuousAlternatingMap.inCoordinates E F₁ x y x y (φ y))
        (ContinuousAlternatingMap.inCoordinates E F₂ x y x y (ψ y))) := by
    filter_upwards [(trivializationAt F₁ V₁ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₁ V₁ x),
      (trivializationAt F₂ V₂ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₂ V₂ x),
      (trivializationAt F₃ V₃ x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt F₃ V₃ x)] with y h₁ h₂ h₃
    exact inCoordinates_bundleWedgeWith μ hμ φ ψ x y h₁ h₂ h₃
  exact h.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

/-- A `C^n` bundle pairing takes `C^n` bundle-valued forms to a `C^n` form on a set. -/
theorem _root_.ContMDiffOn.bundleWedgeWith_form
    {μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffOn I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)) s)
    {φ : RoughBundleForm I M V₁ k} {ψ : RoughBundleForm I M V₂ l}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F₁) y (φ y)) s)
    (hψ : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + l)]→L[ℝ] F₃) y
        (bundleWedgeWith μ hμ φ ψ y)) s :=
  fun y hy ↦ ContMDiffWithinAt.bundleWedgeWith_form hμ (hpair y hy) (hφ y hy) (hψ y hy)

/-- Pointwise regularity of a bundle wedge follows from regularity of both forms and pairing. -/
theorem _root_.ContMDiffAt.bundleWedgeWith_form
    {μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiffAt I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)) x)
    {φ : RoughBundleForm I M V₁ k} {ψ : RoughBundleForm I M V₂ l}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F₁) y (φ y)) x)
    (hψ : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + l)]→L[ℝ] F₃) y
        (bundleWedgeWith μ hμ φ ψ y)) x :=
  ContMDiffWithinAt.bundleWedgeWith_form hμ hpair hφ hψ

/-- A `C^n` pairing preserves `C^n` bundle-valued forms. -/
theorem IsSmoothBundleForm.bundleWedgeWith
    {μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y}
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)))
    {φ : RoughBundleForm I M V₁ k} {ψ : RoughBundleForm I M V₂ l}
    (hφ : IsSmoothBundleForm I F₁ V₁ n φ) (hψ : IsSmoothBundleForm I F₂ V₂ n ψ) :
    IsSmoothBundleForm I F₃ V₃ n (bundleWedgeWith μ hμ φ ψ) := by
  rw [isSmoothBundleForm_def] at hφ hψ ⊢
  exact fun y ↦ ContMDiffAt.bundleWedgeWith_form hμ (hpair y) (hφ y) (hψ y)

namespace SmoothBundleForm

/-- The wedge induced by a smooth bundle pairing, as a bilinear map on smooth forms. -/
def wedgeWith (μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) ∞
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y))) :
    SmoothBundleForm I F₁ V₁ k →ₗ[ℝ] SmoothBundleForm I F₂ V₂ l →ₗ[ℝ]
      SmoothBundleForm I F₃ V₃ (k + l) :=
  LinearMap.mk₂ ℝ (fun φ ψ ↦ ⟨bundleWedgeWith μ hμ φ.1 ψ.1,
      mem_smoothBundleForms.mpr <| IsSmoothBundleForm.bundleWedgeWith hμ hpair
        (mem_smoothBundleForms.mp φ.2) (mem_smoothBundleForms.mp ψ.2)⟩)
    (fun φ φ' ψ ↦ Subtype.ext <| bundleWedgeWith_add_left μ hμ φ.1 φ'.1 ψ.1)
    (fun c φ ψ ↦ Subtype.ext <| bundleWedgeWith_smul_left μ hμ c φ.1 ψ.1)
    (fun φ ψ ψ' ↦ Subtype.ext <| bundleWedgeWith_add_right μ hμ φ.1 ψ.1 ψ'.1)
    (fun c φ ψ ↦ Subtype.ext <| bundleWedgeWith_smul_right μ hμ c φ.1 ψ.1)

/-- The smooth bundle wedge has the existing rough bundle wedge as its underlying form. -/
@[simp]
theorem coe_wedgeWith (μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) ∞
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)))
    (φ : SmoothBundleForm I F₁ V₁ k) (ψ : SmoothBundleForm I F₂ V₂ l) :
    (wedgeWith μ hμ hpair φ ψ : RoughBundleForm I M V₃ (k + l)) =
      bundleWedgeWith μ hμ φ.1 ψ.1 := by
  rw [wedgeWith, LinearMap.mk₂_apply]

/-- Evaluation of the smooth bundle wedge on a tangent tuple. -/
theorem wedgeWith_apply (μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) ∞
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)))
    (φ : SmoothBundleForm I F₁ V₁ k) (ψ : SmoothBundleForm I F₂ V₂ l)
    (y : M) (v : Fin (k + l) → TangentSpace I y) :
    (wedgeWith μ hμ hpair φ ψ).1 y v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          μ y (φ.1 y (fun i ↦ v (σ (Fin.castAdd l i))))
            (ψ.1 y (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  rw [coe_wedgeWith, bundleWedgeWith_apply]

end SmoothBundleForm

end TauCeti
