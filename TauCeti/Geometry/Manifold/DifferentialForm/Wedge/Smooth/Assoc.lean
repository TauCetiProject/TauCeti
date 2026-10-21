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
-/

public section

namespace TauCeti

open scoped Manifold

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
