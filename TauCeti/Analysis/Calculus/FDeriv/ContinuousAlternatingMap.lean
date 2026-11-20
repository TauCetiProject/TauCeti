/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

/-!
# Derivative of an alternating map applied to vectors, one of which vanishes

Let `f : E → F [⋀^ι]→L[𝕜] G` and `g : ι → E → F` be differentiable at `x`. Mathlib's
`fderiv_continuousAlternatingMap_apply_apply` expands the derivative of
`z ↦ f z (g · z)` at `x` by the Leibniz rule into one term differentiating `f` and one term for
each `g i`. If `g i₀ x = 0`, every term which still evaluates an alternating map on the vector
`g i₀ x` vanishes, and only the term differentiating `g i₀` survives
(`TauCeti.fderiv_continuousAlternatingMap_apply_apply_of_eq_zero`).

This is how, for a two-form `σ` and vector fields `X`, `Y` with `X x = 0`, the derivative of
`σ(X, Y)` at `x` is `σ_x(DX, Y)`: it computes the Hessian of a function at a critical point through
its Hamiltonian vector field.
-/

public section

open Function

namespace TauCeti

variable {𝕜 ι E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] [Finite ι] [DecidableEq ι]

/-- **Leibniz rule at a zero of one of the vectors.** If `g i₀` vanishes at `x`, the derivative at
`x` of `z ↦ f z (g · z)` only differentiates `g i₀`. -/
theorem fderiv_continuousAlternatingMap_apply_apply_of_eq_zero {f : E → F [⋀^ι]→L[𝕜] G}
    {g : ι → E → F} {x : E} {i₀ : ι} (hf : DifferentiableAt 𝕜 f x)
    (hg : ∀ i, DifferentiableAt 𝕜 (g i) x) (h₀ : g i₀ x = 0) (w : E) :
    fderiv 𝕜 (fun z ↦ f z (g · z)) x w = f x (update (g · x) i₀ (fderiv 𝕜 (g i₀) x w)) := by
  have := Fintype.ofFinite ι
  rw [fderiv_continuousAlternatingMap_apply_apply hf hg, (fderiv 𝕜 f x w).map_coord_zero i₀ h₀,
    zero_add, Finset.sum_eq_single i₀ (fun i _ hi ↦ (f x).map_coord_zero i₀ (by simp [hi.symm, h₀]))
    (by simp)]

end TauCeti
