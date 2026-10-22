/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Elementary interval integrals

Interval integrals of elementary functions in closed form, continuing Mathlib's
`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`.

## Main declarations

* `TauCeti.integral_one_div_sqrt_one_sub_sq`: `∫ x in a..b, 1 / √(1 - x²) = arcsin b - arcsin a`
  for `a, b ∈ (-1, 1)`.
* `TauCeti.integral_exp_int_mul_mul_I`: `∫ θ in -π..π, exp (k θ i)` is `2π` for the integer
  `k = 0` and `0` otherwise, the orthogonality of the Fourier characters on `[-π, π]`.
-/

public section

namespace TauCeti

/-- The integral of `1 / √(1 - x²)` is `arcsin`, between any two points of `(-1, 1)`. -/
theorem integral_one_div_sqrt_one_sub_sq {a b : ℝ} (ha : a ∈ Set.Ioo (-1) 1)
    (hb : b ∈ Set.Ioo (-1) 1) :
    ∫ x in a..b, 1 / Real.sqrt (1 - x ^ 2) = Real.arcsin b - Real.arcsin a := by
  have hIcc : Set.uIcc a b ⊆ Set.Ioo (-1) 1 := Set.ordConnected_Ioo.uIcc_subset ha hb
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx ↦ ?_) ?_
  · exact Real.hasDerivAt_arcsin (hIcc hx).1.ne' (hIcc hx).2.ne
  · refine ContinuousOn.intervalIntegrable (ContinuousOn.div continuousOn_const ?_ ?_)
    · exact (Real.continuous_sqrt.comp (by fun_prop)).continuousOn
    · intro x hx
      have hx' := hIcc hx
      exact (Real.sqrt_pos.2 (by nlinarith [hx'.1, hx'.2])).ne'

/-- The integral of the Fourier character `θ ↦ exp (k θ i)` over `[-π, π]`, for an integer `k`: it
is `2π` when `k = 0`, and vanishes otherwise because `exp (k θ i)` has period `2π`. -/
theorem integral_exp_int_mul_mul_I (k : ℤ) :
    ∫ θ in -Real.pi..Real.pi, Complex.exp (k * θ * Complex.I) =
      if k = 0 then 2 * (Real.pi : ℂ) else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [Int.cast_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      sub_neg_eq_add, Complex.real_smul, mul_one, ↓reduceIte]
    push_cast
    ring
  · have hc : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hk) Complex.I_ne_zero
    have hper : Complex.exp (k * Complex.I * Real.pi) =
        Complex.exp (k * Complex.I * ((-Real.pi : ℝ) : ℂ)) :=
      Complex.exp_eq_exp_iff_exists_int.mpr ⟨k, by push_cast; ring⟩
    simp_rw [mul_right_comm _ _ Complex.I]
    rw [integral_exp_mul_complex hc, ite_eq_right hk, hper, sub_self, zero_div]

end TauCeti
