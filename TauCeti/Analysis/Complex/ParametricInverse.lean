/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.ParametricInverse
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# The holomorphic implicit function theorem with a varying level

Let `f : E₁ × E₂ → F` be strictly differentiable at `u`, with invertible partial derivative in
the second variable, where `E₁` and `E₂` are finite-dimensional complex spaces. If `f` is complex
differentiable near `u`, then the map `HasStrictFDerivAt.localInverseOfProdDomain` of
`TauCeti.Analysis.Calculus.ParametricInverse`, which solves `f (z, v) = w` for `v` jointly in the
parameter `z` and the level `w`, is complex differentiable near `(u.1, f u)`. Holomorphy gives
analyticity (`DifferentiableOn.analyticAt_of_finiteDimensional`), so this follows from
`HasStrictFDerivAt.analyticAt_uncurry_localInverseOfProdDomain`.

## Main results

* `HasStrictFDerivAt.eventually_differentiableAt_uncurry_localInverseOfProdDomain`: the
  **holomorphic implicit function theorem with a varying level**.

## References

* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Prentice-Hall
  (1965), Chapter I (the holomorphic inverse and implicit function theorems).
-/

public section

open Filter Function
open scoped Topology

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
  [FiniteDimensional ℂ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [CompleteSpace E₂]
  [FiniteDimensional ℂ E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace HasStrictFDerivAt

variable {u : E₁ × E₂} {f : E₁ × E₂ → F} {f'u : E₁ × E₂ →L[ℂ] F}
  (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr ℂ E₁ E₂).IsInvertible)

/-- **The holomorphic implicit function theorem with a varying level.** If `f` is complex
differentiable on a neighbourhood of `u` in a finite-dimensional complex space, then
`localInverseOfProdDomain` is jointly complex differentiable in the parameter and the level at
every point of a neighbourhood of `(u.1, f u)`. -/
theorem eventually_differentiableAt_uncurry_localInverseOfProdDomain {s : Set (E₁ × E₂)}
    (hf : DifferentiableOn ℂ f s) (hs : s ∈ 𝓝 u) :
    ∀ᶠ p in 𝓝 (u.1, f u), DifferentiableAt ℂ (uncurry (dfu.localInverseOfProdDomain if₂u)) p :=
  (dfu.analyticAt_uncurry_localInverseOfProdDomain if₂u
    (hf.analyticAt_of_finiteDimensional hs)).eventually_analyticAt.mono
      fun _ h ↦ h.differentiableAt

end HasStrictFDerivAt

end
