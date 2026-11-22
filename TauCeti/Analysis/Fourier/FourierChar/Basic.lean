/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# The real additive character and distance to the integers

The additive character `Real.fourierChar` is the lift of `AddCircle.toCircle` from
`UnitAddCircle`. Integrating an integer-frequency character over any interval of length one
extracts the zero Fourier mode.
-/

public section

open scoped FourierTransform

namespace Real

/-- The standard character on `ℝ / ℤ`, pulled back to `ℝ`, is the real Fourier character. -/
@[simp]
theorem toCircle_coe_unitAddCircle (x : ℝ) : AddCircle.toCircle (x : UnitAddCircle) = 𝐞 x := by
  simp [AddCircle.toCircle_apply_mk, fourierChar_apply']

end Real

namespace Int

/-- A full unit interval integrates an integer-frequency character to zero, except at
frequency zero, where the integral is one. -/
theorem integral_fourierChar_intCast_mul (m : ℤ) (a : ℝ) :
    (∫ x in a..a + 1, (𝐞 ((m : ℝ) * x) : ℂ)) = if m = 0 then 1 else 0 := by
  have : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have h := congrFun (fourierCoeff_fourier (T := 1) m) 0
  rw [fourierCoeff_eq_intervalIntegral _ _ a] at h
  have hmode (x : ℝ) : fourier (T := 1) m (x : UnitAddCircle) = (𝐞 ((m : ℝ) * x) : ℂ) := by
    rw [fourier_apply, ← AddCircle.coe_zsmul, Real.toCircle_coe_unitAddCircle, zsmul_eq_mul]
  simpa [hmode, Pi.single_apply, eq_comm (a := (0 : ℤ))] using h

end Int
