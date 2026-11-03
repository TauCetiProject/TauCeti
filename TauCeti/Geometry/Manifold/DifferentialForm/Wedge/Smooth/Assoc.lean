/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Assoc
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# Associativity of smooth differential-form wedges

The scalar wedge on smooth forms is associative after the canonical reassociation of its finite
argument tuple.  This specializes rough-form associativity to the smooth scalar product and gives
its pointwise reassociation law for products used in de Rham cohomology.
The file also gives pointwise associativity for paired wedges of smooth bundle-valued forms when
the fibrewise pairings are smooth sections with matching composites, specializing
`bundleWedgeWith_assoc`.
-/

public section

namespace TauCeti

open Bundle
open scoped ContDiff Manifold

variable {E H M F₁ F₂ F₃ F₁₂ F₂₃ G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [IsManifold I 1 M]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  [NormedAddCommGroup F₁₂] [NormedSpace ℝ F₁₂]
  [NormedAddCommGroup F₂₃] [NormedSpace ℝ F₂₃]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k l m : ℕ}

section Bundle

variable {V₁ V₂ V₃ V₁₂ V₂₃ W : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [∀ x, AddCommGroup (V₁₂ x)] [∀ x, Module ℝ (V₁₂ x)] [∀ x, TopologicalSpace (V₁₂ x)]
  [∀ x, AddCommGroup (V₂₃ x)] [∀ x, Module ℝ (V₂₃ x)] [∀ x, TopologicalSpace (V₂₃ x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [TopologicalSpace (TotalSpace F₁₂ V₁₂)] [FiberBundle F₁₂ V₁₂] [VectorBundle ℝ F₁₂ V₁₂]
  [TopologicalSpace (TotalSpace F₂₃ V₂₃)] [FiberBundle F₂₃ V₂₃] [VectorBundle ℝ F₂₃ V₂₃]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]
  [∀ x, IsTopologicalAddGroup (V₁₂ x)] [∀ x, ContinuousSMul ℝ (V₁₂ x)]
  [∀ x, IsTopologicalAddGroup (V₂₃ x)] [∀ x, ContinuousSMul ℝ (V₂₃ x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [∀ x, IsTopologicalAddGroup (V₁ x)] [∀ x, ContinuousSMul ℝ (V₁ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]

namespace SmoothBundleForm

/-- Smooth bundle wedges are associative when the fibrewise coefficient pairings have equal
composites. Each pairing is required to be a smooth section of its hom bundle. -/
theorem wedgeWith_assoc_apply
    (μ₁₂ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₁₂ x)
    (μ₁₂₃ : (x : M) → V₁₂ x →L[ℝ] V₃ x →L[ℝ] W x)
    (μ₂₃ : (x : M) → V₂ x →L[ℝ] V₃ x →L[ℝ] V₂₃ x)
    (μ₁₂₃' : (x : M) → V₁ x →L[ℝ] V₂₃ x →L[ℝ] W x)
    (h₁₂ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ₁₂ x a b))
    (h₁₂₃ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ₁₂₃ x a b))
    (h₂₃ : ∀ x, Continuous (Function.uncurry fun a b ↦ μ₂₃ x a b))
    (h₁₂₃' : ∀ x, Continuous (Function.uncurry fun a b ↦ μ₁₂₃' x a b))
    (s₁₂ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂ →L[ℝ] F₁₂)) ∞
      (fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂ →L[ℝ] F₁₂) x (μ₁₂ x)))
    (s₁₂₃ : ContMDiff I (I.prod 𝓘(ℝ, F₁₂ →L[ℝ] F₃ →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (F₁₂ →L[ℝ] F₃ →L[ℝ] G) x (μ₁₂₃ x)))
    (s₂₃ : ContMDiff I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₃ →L[ℝ] F₂₃)) ∞
      (fun x ↦ TotalSpace.mk' (F₂ →L[ℝ] F₃ →L[ℝ] F₂₃) x (μ₂₃ x)))
    (s₁₂₃' : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂₃ →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (F₁ →L[ℝ] F₂₃ →L[ℝ] G) x (μ₁₂₃' x)))
    (h : ∀ x a b c, μ₁₂₃ x (μ₁₂ x a b) c = μ₁₂₃' x a (μ₂₃ x b c))
    (φ : SmoothBundleForm I F₁ V₁ k) (ψ : SmoothBundleForm I F₂ V₂ l)
    (χ : SmoothBundleForm I F₃ V₃ m) (x : M)
    (v : Fin (k + l + m) → TangentSpace I x) :
    (wedgeWith μ₁₂₃ h₁₂₃ s₁₂₃ (wedgeWith μ₁₂ h₁₂ s₁₂ φ ψ) χ).1 x v =
      (wedgeWith μ₁₂₃' h₁₂₃' s₁₂₃' φ (wedgeWith μ₂₃ h₂₃ s₂₃ ψ χ)).1 x
        (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  rw [coe_wedgeWith, coe_wedgeWith, coe_wedgeWith, coe_wedgeWith]
  exact bundleWedgeWith_assoc μ₁₂ μ₁₂₃ μ₂₃ μ₁₂₃' h₁₂ h₁₂₃ h₂₃ h₁₂₃' h φ.1 ψ.1 χ.1 x v

end SmoothBundleForm

end Bundle

namespace SmoothForm

/-- Smooth paired wedges are associative when the coefficient pairings have equal composites. -/
theorem wedgeWith_assoc_apply
    (μ₁₂ : F₁ →L[ℝ] F₂ →L[ℝ] F₁₂) (μ₁₂₃ : F₁₂ →L[ℝ] F₃ →L[ℝ] G)
    (μ₂₃ : F₂ →L[ℝ] F₃ →L[ℝ] F₂₃) (μ₁₂₃' : F₁ →L[ℝ] F₂₃ →L[ℝ] G)
    (h : ∀ a b c, μ₁₂₃ (μ₁₂ a b) c = μ₁₂₃' a (μ₂₃ b c))
    (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l)
    (χ : SmoothForm I M F₃ m) (x : M)
    (v : Fin (k + l + m) → TangentSpace I x) :
    (wedgeWith μ₁₂₃ (wedgeWith μ₁₂ φ ψ) χ).1 x v =
      (wedgeWith μ₁₂₃' φ (wedgeWith μ₂₃ ψ χ)).1 x
        (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  rw [coe_wedgeWith, coe_wedgeWith, coe_wedgeWith, coe_wedgeWith]
  exact RoughForm.wedgeWith_assoc μ₁₂ μ₁₂₃ μ₂₃ μ₁₂₃' h φ.1 ψ.1 χ.1 x v

/-- The scalar wedge of smooth forms is associative, with the tuple degree reassociated. -/
theorem wedge_assoc_apply (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l)
    (χ : SmoothForm I M ℝ m) (x : M) (v : Fin (k + l + m) → TangentSpace I x) :
    (wedge (wedge φ ψ) χ).1 x v =
      (wedge φ (wedge ψ χ)).1 x (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  simpa only [wedge_def] using
    wedgeWith_assoc_apply (μ₁₂ := ContinuousLinearMap.mul ℝ ℝ)
      (μ₁₂₃ := ContinuousLinearMap.mul ℝ ℝ)
      (μ₂₃ := ContinuousLinearMap.mul ℝ ℝ)
      (μ₁₂₃' := ContinuousLinearMap.mul ℝ ℝ)
      (fun a b c : ℝ ↦ mul_assoc a b c) φ ψ χ x v

end SmoothForm

end TauCeti
