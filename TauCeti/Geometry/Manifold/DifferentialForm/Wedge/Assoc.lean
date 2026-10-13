/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Assoc

/-!
# Associativity of wedge products of rough forms

Iterated paired wedges agree when their fibrewise coefficient pairings have equal composites.
This holds on any charted space, including manifolds with boundary or corners, without regularity
assumptions on the forms or pairings in the base variable. The tangent fibres and value fibres
need no chosen norm. Fixed-coefficient forms and the ordinary real-valued wedge are special cases.

These identities supply the algebraic associativity underlying products of smooth forms and
cohomology classes. Degrees are identified by the canonical reassociation of finite tuples.
The normalization follows John M. Lee, *Introduction to Smooth Manifolds*, second edition,
Chapter 14.
-/

public section

namespace TauCeti

open scoped Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H} {k l m : ℕ}

section Bundle

variable {V₁ V₂ V₃ V₁₂ V₂₃ W : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [∀ x, AddCommGroup (V₁₂ x)] [∀ x, Module ℝ (V₁₂ x)] [∀ x, TopologicalSpace (V₁₂ x)]
  [∀ x, IsTopologicalAddGroup (V₁₂ x)] [∀ x, ContinuousSMul ℝ (V₁₂ x)]
  [∀ x, AddCommGroup (V₂₃ x)] [∀ x, Module ℝ (V₂₃ x)] [∀ x, TopologicalSpace (V₂₃ x)]
  [∀ x, IsTopologicalAddGroup (V₂₃ x)] [∀ x, ContinuousSMul ℝ (V₂₃ x)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]

/-- The bundle-valued paired wedge is associative when the two fibrewise composites of its
pairings agree. No smoothness or trivialization of the value bundles is required. -/
theorem bundleWedgeWith_assoc
    (μ₁₂ : (x : M) → V₁ x →L[ℝ] V₂ x →L[ℝ] V₁₂ x)
    (μ₁₂₃ : (x : M) → V₁₂ x →L[ℝ] V₃ x →L[ℝ] W x)
    (μ₂₃ : (x : M) → V₂ x →L[ℝ] V₃ x →L[ℝ] V₂₃ x)
    (μ₁₂₃' : (x : M) → V₁ x →L[ℝ] V₂₃ x →L[ℝ] W x)
    (h₁₂ : ∀ x, Continuous (fun p : V₁ x × V₂ x ↦ μ₁₂ x p.1 p.2))
    (h₁₂₃ : ∀ x, Continuous (fun p : V₁₂ x × V₃ x ↦ μ₁₂₃ x p.1 p.2))
    (h₂₃ : ∀ x, Continuous (fun p : V₂ x × V₃ x ↦ μ₂₃ x p.1 p.2))
    (h₁₂₃' : ∀ x, Continuous (fun p : V₁ x × V₂₃ x ↦ μ₁₂₃' x p.1 p.2))
    (h : ∀ x a b c, μ₁₂₃ x (μ₁₂ x a b) c = μ₁₂₃' x a (μ₂₃ x b c))
    (φ : RoughBundleForm I M V₁ k) (ψ : RoughBundleForm I M V₂ l)
    (χ : RoughBundleForm I M V₃ m) (x : M)
    (v : Fin (k + l + m) → TangentSpace I x) :
    bundleWedgeWith μ₁₂₃ h₁₂₃ (bundleWedgeWith μ₁₂ h₁₂ φ ψ) χ x v =
      bundleWedgeWith μ₁₂₃' h₁₂₃' φ (bundleWedgeWith μ₂₃ h₂₃ ψ χ) x
        (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  simp only [bundleWedgeWith_apply']
  exact ContinuousAlternatingMap.pairedWedge_assoc (μ₁₂ x) (μ₁₂₃ x) (μ₂₃ x) (μ₁₂₃' x)
    (h₁₂ x) (h₁₂₃ x) (h₂₃ x) (h₁₂₃' x) (h x) (φ x) (ψ x) (χ x) v

end Bundle

namespace RoughForm

variable {F₁ F₂ F₃ F₁₂ F₂₃ G : Type*}
  [SeminormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [SeminormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [SeminormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  [SeminormedAddCommGroup F₁₂] [NormedSpace ℝ F₁₂]
  [SeminormedAddCommGroup F₂₃] [NormedSpace ℝ F₂₃]
  [SeminormedAddCommGroup G] [NormedSpace ℝ G]

/-- The fixed-coefficient paired wedge is associative for pairings with equal composites. -/
theorem wedgeWith_assoc (μ₁₂ : F₁ →L[ℝ] F₂ →L[ℝ] F₁₂) (μ₁₂₃ : F₁₂ →L[ℝ] F₃ →L[ℝ] G)
    (μ₂₃ : F₂ →L[ℝ] F₃ →L[ℝ] F₂₃) (μ₁₂₃' : F₁ →L[ℝ] F₂₃ →L[ℝ] G)
    (h : ∀ a b c, μ₁₂₃ (μ₁₂ a b) c = μ₁₂₃' a (μ₂₃ b c))
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) (χ : RoughForm I M F₃ m)
    (x : M) (v : Fin (k + l + m) → TangentSpace I x) :
    (φ.wedgeWith μ₁₂ ψ).wedgeWith μ₁₂₃ χ x v =
      φ.wedgeWith μ₁₂₃' (ψ.wedgeWith μ₂₃ χ) x
        (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  simp only [wedgeWith_apply']
  exact ContinuousAlternatingMap.pairedWedge_assoc μ₁₂ μ₁₂₃ μ₂₃ μ₁₂₃'
    μ₁₂.continuous₂ μ₁₂₃.continuous₂ μ₂₃.continuous₂ μ₁₂₃'.continuous₂ h (φ x) (ψ x) (χ x) v

/-- The real-valued rough-form wedge is associative, up to reassociation of its degree. -/
theorem wedge_assoc (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l)
    (χ : RoughForm I M ℝ m) (x : M) (v : Fin (k + l + m) → TangentSpace I x) :
    (φ.wedge ψ).wedge χ x v =
      φ.wedge (ψ.wedge χ) x (v ∘ Fin.cast (Nat.add_assoc k l m).symm) := by
  simp only [wedge_def]
  exact wedgeWith_assoc _ _ _ _ (fun a b c : ℝ ↦ mul_assoc a b c) φ ψ χ x v

end RoughForm

end TauCeti
