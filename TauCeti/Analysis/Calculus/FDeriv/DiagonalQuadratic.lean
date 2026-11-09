/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# The derivative of a diagonal quadratic form

Over a nontrivially normed field `𝕜` in which `2 ≠ 0`, the diagonal quadratic form
`u ↦ c + (1/2) Σᵢ wᵢ uᵢ²` on `ι → 𝕜`, for a finite index type `ι`, has derivative
`v ↦ Σᵢ wᵢ uᵢ vᵢ` at `u`. Over `ℝ`, this is the normal form of a function at a nondegenerate
critical point given by the Morse lemma.

## Main results

* `TauCeti.hasFDerivAt_diagonalQuadratic`: the derivative of a diagonal quadratic form.
-/

public section

namespace TauCeti

/-- The diagonal quadratic form `u ↦ c + (1/2) Σᵢ wᵢ uᵢ²` has derivative `v ↦ Σᵢ wᵢ uᵢ vᵢ`. -/
theorem hasFDerivAt_diagonalQuadratic {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [NeZero (2 : 𝕜)]
    [Fintype ι] (c : 𝕜) (w u : ι → 𝕜) :
    HasFDerivAt (fun u : ι → 𝕜 ↦ c + (2 : 𝕜)⁻¹ * ∑ i, w i * u i ^ 2)
      (∑ i, (w i * u i) • ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i) u := by
  have hs : HasFDerivAt (fun v : ι → 𝕜 ↦ ∑ i, w i * v i ^ 2) _ u := .fun_sum fun i _ ↦
    ((hasFDerivAt_pow 2).comp u (hasFDerivAt_apply (𝕜 := 𝕜) i u)).const_mul (w i)
  convert (hs.const_mul (2 : 𝕜)⁻¹).const_add c using 1
  ext v
  simp [Finset.mul_sum, mul_left_comm (2 : 𝕜)⁻¹, mul_assoc, two_ne_zero]

end TauCeti
