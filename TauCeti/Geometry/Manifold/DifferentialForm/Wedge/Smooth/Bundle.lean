/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Alternating

/-!
# Smooth paired wedges with bundle coefficients

A smooth fibrewise bilinear pairing sends two smooth bundle-valued differential forms to a
smooth form in its target bundle. The pairing may vary with the base point, and none of the
value bundles needs a global trivialization or a norm on its individual fibres.

`ContMDiffAt.pairedWedge_bundle` (from
`TauCeti.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap`) shows that a `C^n` bundle pairing
preserves `C^n` bundle-valued differential forms (`TauCeti.IsSmoothBundleForm.bundleWedgeWith`).
On smooth forms, `SmoothBundleForm.wedgeWith` packages the product directly from
`ContMDiffSection.wedgeWith` via `SmoothBundleForm.toContMDiffSectionEquiv`, with conversion
lemma `SmoothBundleForm.wedgeWith_toContMDiffSection`.

The wedge normalization and bundle-valued construction follow John M. Lee,
*Introduction to Smooth Manifolds*, second edition, Chapter 14, and the paired-wedge design
of Yury Kudryashov's `DeRhamCohomology`.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

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
  [IsManifold I 1 M] {k l : ℕ} {n : WithTop ℕ∞}
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]

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
  intro y
  simpa only [bundleWedgeWith_apply'] using
    ContMDiffAt.pairedWedge_bundle hμ (hpair y) (hφ y) (hψ y)

namespace SmoothBundleForm

/-- The wedge induced by a smooth bundle pairing, as a bilinear map on smooth forms, obtained from
`ContMDiffSection.wedgeWith`. -/
def wedgeWith (μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) ∞
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y))) :
    SmoothBundleForm I F₁ V₁ k →ₗ[ℝ] SmoothBundleForm I F₂ V₂ l →ₗ[ℝ]
      SmoothBundleForm I F₃ V₃ (k + l) :=
  LinearMap.mk₂ ℝ
    (fun φ ψ ↦ ofContMDiffSection
      (ContMDiffSection.wedgeWith μ hμ hpair φ.toContMDiffSection ψ.toContMDiffSection))
    (fun φ₁ φ₂ ψ ↦ toContMDiffSection_injective <| by simp)
    (fun c φ ψ ↦ toContMDiffSection_injective <| by simp)
    (fun φ ψ₁ ψ₂ ↦ toContMDiffSection_injective <| by simp)
    (fun c φ ψ ↦ toContMDiffSection_injective <| by simp)

/-- Converting the smooth bundle wedge of two forms to a section gives
`ContMDiffSection.wedgeWith` of their converted sections. -/
@[simp]
theorem wedgeWith_toContMDiffSection (μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) ∞
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)))
    (φ : SmoothBundleForm I F₁ V₁ k) (ψ : SmoothBundleForm I F₂ V₂ l) :
    (wedgeWith μ hμ hpair φ ψ).toContMDiffSection =
      ContMDiffSection.wedgeWith μ hμ hpair φ.toContMDiffSection ψ.toContMDiffSection := by
  rw [wedgeWith, LinearMap.mk₂_apply, toContMDiffSection_ofContMDiffSection]

/-- The smooth bundle wedge has the existing rough bundle wedge as its underlying form. -/
@[simp]
theorem coe_wedgeWith (μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) ∞
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)))
    (φ : SmoothBundleForm I F₁ V₁ k) (ψ : SmoothBundleForm I F₂ V₂ l) :
    (wedgeWith μ hμ hpair φ ψ : RoughBundleForm I M V₃ (k + l)) =
      bundleWedgeWith μ hμ φ.val ψ.val := by
  funext x
  have h := congr($(wedgeWith_toContMDiffSection μ hμ hpair φ ψ) x)
  simpa only [toContMDiffSection_apply, ContMDiffSection.wedgeWith_apply,
    bundleWedgeWith_apply'] using h

/-- Evaluation of the smooth bundle wedge on a tangent tuple. -/
theorem wedgeWith_apply (μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) ∞
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)))
    (φ : SmoothBundleForm I F₁ V₁ k) (ψ : SmoothBundleForm I F₂ V₂ l)
    (y : M) (v : Fin (k + l) → TangentSpace I y) :
    (wedgeWith μ hμ hpair φ ψ).val y v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          μ y (φ.val y (fun i ↦ v (σ (Fin.castAdd l i))))
            (ψ.val y (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  rw [coe_wedgeWith, bundleWedgeWith_apply]

/-- The smooth bundle wedge of two one-forms is the alternating two-term pairing. -/
theorem wedgeWith_apply_one_one
    (μ : (y : M) → V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y)
    (hμ : ∀ y, Continuous (Function.uncurry fun a b ↦ μ y a b))
    (hpair : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₃)) ∞
      (fun y ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₃) y (μ y)))
    (φ : SmoothBundleForm I F₁ V₁ 1) (ψ : SmoothBundleForm I F₂ V₂ 1)
    (y : M) (v w : TangentSpace I y) :
    (wedgeWith μ hμ hpair φ ψ).val y ![v, w] =
      μ y (φ.val y ![v]) (ψ.val y ![w]) - μ y (φ.val y ![w]) (ψ.val y ![v]) := by
  simpa only [coe_wedgeWith] using
    (bundleWedgeWith_apply_one_one μ hμ φ.val ψ.val y v w)

end SmoothBundleForm

end TauCeti
