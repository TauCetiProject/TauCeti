/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integrals of the characters of the circle and the torus

For `n ∈ ℤ`, `∫_{(0,2π]} e^{inθ} dθ = 2π [n = 0]` (`TauCeti.setIntegral_exp_int_mul_I`), and for
`d ∈ ℤ²`, `∫∫_{(0,2π]²} e^{i(d₁θ + d₂φ)} dθ dφ = 4π² [d = 0]`
(`TauCeti.setIntegral_exp_int_mul_add_int_mul_I`), the orthogonality of the characters in the
coordinates `θ` and `(θ, φ)` on `ℝ` and `ℝ²`.
-/

public section

noncomputable section

open Complex Set MeasureTheory

namespace TauCeti

/-- **Orthogonality of the characters of the circle.** For `n ∈ ℤ`,
`∫_{(0,2π]} e^{inθ} dθ = 2π` if `n = 0` and `0` otherwise. -/
theorem setIntegral_exp_int_mul_I (n : ℤ) :
    ∫ θ in Ioc 0 (2 * Real.pi), exp ((n * θ : ℝ) * I) =
      if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  split_ifs with hn
  · simp [hn]
  · have hc : (n * I : ℂ) ≠ 0 := mul_ne_zero (by exact_mod_cast hn) I_ne_zero
    have key := integral_exp_mul_complex (a := 0) (b := 2 * Real.pi) hc
    simp only [ofReal_mul, ofReal_intCast]
    simp_rw [show ∀ θ : ℝ, (n : ℂ) * θ * I = n * I * θ from fun θ => by ring]
    rw [key, show (n : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ) = n * (2 * Real.pi * I) by
      push_cast; ring]
    simp [exp_int_mul_two_pi_mul_I]

/-- **Orthogonality of the characters of the torus.** For `d ∈ ℤ²`,
`∫∫_{(0,2π]²} e^{i(d₁θ + d₂φ)} dθ dφ = 4π²` if `d = 0` and `0` otherwise. -/
theorem setIntegral_exp_int_mul_add_int_mul_I (d : ℤ × ℤ) :
    ∫ p in Ioc 0 (2 * Real.pi) ×ˢ Ioc 0 (2 * Real.pi), exp ((d.1 * p.1 + d.2 * p.2 : ℝ) * I) =
      if d = 0 then ((4 * Real.pi ^ 2 : ℝ) : ℂ) else 0 := by
  have hsplit : ∀ p : ℝ × ℝ, exp ((d.1 * p.1 + d.2 * p.2 : ℝ) * I) =
      exp ((d.1 * p.1 : ℝ) * I) * exp ((d.2 * p.2 : ℝ) * I) := fun p => by
    rw [← exp_add]; push_cast; ring_nf
  simp_rw [hsplit]
  rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun x : ℝ => exp ((d.1 * x : ℝ) * I))
    (fun y : ℝ => exp ((d.2 * y : ℝ) * I)), setIntegral_exp_int_mul_I,
    setIntegral_exp_int_mul_I]
  rcases d with ⟨a, b⟩
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · simp only [ha, hb, ite_true, Prod.mk_zero_zero]
      push_cast
      ring
    · simp [hb]
  · simp [ha]

end TauCeti
