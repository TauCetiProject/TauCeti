/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# The derivative of a diagonal quadratic form

The diagonal quadratic form `u ↦ c + (1/2) Σᵢ wᵢ uᵢ²` on `Fin n → ℝ` has derivative
`v ↦ Σᵢ wᵢ uᵢ vᵢ` at `u`. This is the normal form of a function at a nondegenerate critical point
given by the Morse lemma.

## Main results

* `TauCeti.hasFDerivAt_diagonalQuadratic`: the derivative of a diagonal quadratic form.
-/

public section

namespace TauCeti

/-- The diagonal quadratic form `u ↦ c + (1/2) Σᵢ wᵢ uᵢ²` has derivative `v ↦ Σᵢ wᵢ uᵢ vᵢ`. -/
theorem hasFDerivAt_diagonalQuadratic {n : ℕ} (c : ℝ) (w u : Fin n → ℝ) :
    HasFDerivAt (fun u : Fin n → ℝ ↦ c + (2 : ℝ)⁻¹ * ∑ i, w i * (u i * u i))
      (∑ i, (w i * u i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i) u := by
  have hp : ∀ i, HasFDerivAt (fun u : Fin n → ℝ ↦ u i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i) u :=
    fun i ↦ hasFDerivAt_apply i u
  have hs : HasFDerivAt (fun v : Fin n → ℝ ↦ ∑ i, w i * (v i * v i))
      (∑ i ∈ Finset.univ, w i • (u i • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin n ↦ ℝ) i + u i • ContinuousLinearMap.proj i)) u :=
    HasFDerivAt.fun_sum fun i _ ↦ ((hp i).mul (hp i)).const_mul (w i)
  have h := (hs.const_mul (2 : ℝ)⁻¹).const_add c
  convert h using 1
  ext v
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, add_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

end TauCeti
