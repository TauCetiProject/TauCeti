/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Fourier moments of a real measure wrapped onto the circle

For a real measure `μ` wrapped onto `AddCircle T` and translated by `m`, the integer Fourier
moments are `fourier n m` times the characteristic function of `μ` at the frequency
`2 * π * n / T` (`integral_fourier_map_add_coe`). This computes the Fourier moments of the
wrapped laws, such as the wrapped Cauchy and wrapped normal laws, from the characteristic
function of the underlying real law.
-/

public section

noncomputable section

open Real

namespace MeasureTheory

/-- The integer Fourier moments of a real measure `μ`, read modulo `T` and translated by `m`, are
the character `fourier n m` of the location `m` times the characteristic function of `μ` at the
frequency `2 * π * n / T`. -/
theorem integral_fourier_map_add_coe {T : ℝ} (μ : Measure ℝ) (m : AddCircle T) (n : ℤ) :
    ∫ θ, fourier n θ ∂μ.map (fun x : ℝ ↦ m + (x : AddCircle T)) =
      fourier n m * charFun μ (2 * π * n / T) := by
  rw [integral_map (by fun_prop) (by fun_prop), charFun_apply_real, ← integral_const_mul]
  congr 1; funext x
  rw [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, ← fourier_apply,
    ← fourier_apply, fourier_coe_apply]
  congr 2; push_cast; ring

end MeasureTheory
