/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Basic
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Oscillator

/-!
# Calculus of products of dilated Hermite functions

On `ℝ^ι`, the product `x ↦ ∏ᵢ ψ_{kᵢ}(cᵢ xᵢ)` of dilated Hermite functions is the multi-index
eigenfunction of the harmonic oscillator `∑ᵢ (-∂ᵢ² + cᵢ⁴ xᵢ²)`. This file records its smoothness
and its second partial derivatives, which follow coordinatewise from the one-dimensional oscillator
identity `TauCeti.deriv_deriv_hermiteFunction_comp_mul`.

## Main results

* `TauCeti.contDiff_prod_hermiteFunction_comp_mul`: the product is smooth.
* `TauCeti.fderiv_fderiv_prod_hermiteFunction_comp_mul_apply_single_single`: differentiating the
  product twice in `xᵢ` multiplies it by `cᵢ² ((cᵢ xᵢ)² - (2kᵢ + 1))`.
-/

public section

namespace TauCeti

open Function

variable {ι : Type*} [Fintype ι]

/-- A product of dilated Hermite functions `x ↦ ∏ᵢ ψ_{kᵢ}(cᵢ xᵢ)` is smooth. -/
theorem contDiff_prod_hermiteFunction_comp_mul (c : ι → ℝ) (k : ι → ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : ι → ℝ ↦ ∏ i, hermiteFunction (k i) (c i * x i)) :=
  contDiff_prod fun i _ ↦ (contDiff_hermiteFunction (k i)).of_le le_top |>.comp
    (contDiff_const.mul (contDiff_apply ℝ (fun _ : ι ↦ ℝ) i))

/-- The second partial derivatives of a product of dilated Hermite functions: differentiating
`x ↦ ∏ⱼ ψ_{kⱼ}(cⱼ xⱼ)` twice in `xᵢ` multiplies it by `cᵢ² ((cᵢ xᵢ)² - (2kᵢ + 1))`. -/
theorem fderiv_fderiv_prod_hermiteFunction_comp_mul_apply_single_single [DecidableEq ι]
    (c : ι → ℝ) (k : ι → ℕ) (x : ι → ℝ) (i : ι) :
    fderiv ℝ (fderiv ℝ fun x : ι → ℝ ↦ ∏ j, hermiteFunction (k j) (c j * x j)) x
        (Pi.single i 1) (Pi.single i 1) =
      c i ^ 2 * ((c i * x i) ^ 2 - (2 * k i + 1)) *
        ∏ j, hermiteFunction (k j) (c j * x j) := by
  rw [fderiv_fderiv_prod_comp_eval_apply_single_single
      (φ := fun j y ↦ hermiteFunction (k j) (c j * y))
      (fun j ↦ ((contDiff_hermiteFunction (k j)).of_le le_top |>.comp
        (contDiff_const.mul contDiff_id)).contDiffAt) i,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j ↦ hermiteFunction (k j) (c j * x j)) (Finset.mem_univ i),
    update_self, deriv_deriv_hermiteFunction_comp_mul, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun j hj ↦ by rw [update_of_ne (Finset.ne_of_mem_erase hj)]

end TauCeti
