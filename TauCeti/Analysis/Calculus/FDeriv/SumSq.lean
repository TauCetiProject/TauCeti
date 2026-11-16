/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Derivatives of functions whose squares sum to a constant

If real functions `χᵢ` are differentiable at `x` and `∑ᵢ χᵢ²` is constant near `x`, then
`∑ᵢ χᵢ(x) Dχᵢ(x) = ½ D(∑ᵢ χᵢ²)(x) = 0` (`TauCeti.sum_smul_fderiv_eq_zero_of_eventuallyEq`). This is
the identity behind the cancellation of the first-order terms for square partitions of unity
`∑ᵢ χᵢ² = 1`.
-/

public section

open scoped Topology

namespace TauCeti

/-- If the squares of real functions `χᵢ`, differentiable at `x`, sum to a constant near `x`, then
`∑ᵢ χᵢ(x) Dχᵢ(x) = 0`. -/
theorem sum_smul_fderiv_eq_zero_of_eventuallyEq {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Finset ι} {χ : ι → E → ℝ} {x : E}
    (hχ : ∀ i ∈ s, DifferentiableAt ℝ (χ i) x) {c : ℝ}
    (h : (fun y ↦ ∑ i ∈ s, χ i y ^ 2) =ᶠ[𝓝 x] fun _ ↦ c) :
    ∑ i ∈ s, χ i x • fderiv ℝ (χ i) x = 0 := by
  have hd : HasFDerivAt (fun y ↦ ∑ i ∈ s, χ i y ^ 2)
      (∑ i ∈ s, (2 : ℝ) • χ i x • fderiv ℝ (χ i) x) x :=
    HasFDerivAt.fun_sum fun i hi ↦ by
      simpa [smul_smul, mul_comm] using ((hχ i hi).hasFDerivAt.pow 2)
  have h0 := hd.unique ((hasFDerivAt_const c x).congr_of_eventuallyEq h)
  rw [← Finset.smul_sum] at h0
  exact (smul_eq_zero.1 h0).resolve_left two_ne_zero

end TauCeti
