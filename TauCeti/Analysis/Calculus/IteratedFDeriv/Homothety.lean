/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Iterated derivatives of a composition with a homothety

Precomposing a `C^k` function with the homothety `x ↦ c • (x - x₀) + x₀` of ratio `c` about `x₀`
multiplies its `k`-th iterated derivative by `c ^ k`, evaluated at the image point
(`TauCeti.iteratedFDeriv_comp_homothety`). This combines Mathlib's formulas for a translation,
`iteratedFDeriv_comp_sub'` and `iteratedFDeriv_comp_add_right'`, with the one for a scalar
dilation, `iteratedFDeriv_comp_const_smul`. Homotheties of ratio close to `1` about an interior
point shrink a compactly supported function into a smaller support while changing its
derivatives only slightly.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `k`-th iterated derivative of `f` precomposed with the homothety of ratio `c` about `x₀` is
`c ^ k` times the `k`-th iterated derivative of `f` at the image point. -/
theorem iteratedFDeriv_comp_homothety {f : E → F} {k : ℕ} (hf : ContDiff 𝕜 k f) (x₀ : E) (c : 𝕜) :
    iteratedFDeriv 𝕜 k (f ∘ AffineMap.homothety x₀ c) =
      fun x ↦ c ^ k • iteratedFDeriv 𝕜 k f (AffineMap.homothety x₀ c x) := by
  have h : f ∘ AffineMap.homothety x₀ c = fun x ↦ (fun z ↦ f (c • z + x₀)) (x - x₀) := by
    funext x
    simp [AffineMap.homothety_apply]
  rw [h, iteratedFDeriv_comp_sub' (f := fun z ↦ f (c • z + x₀)),
    iteratedFDeriv_comp_const_smul (f := fun y ↦ f (y + x₀)) c
      (hf.comp (contDiff_id.add contDiff_const)), iteratedFDeriv_comp_add_right']
  simp [AffineMap.homothety_apply]

end TauCeti
