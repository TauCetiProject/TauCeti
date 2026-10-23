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

Interval integrals of elementary functions in closed form or as series, continuing Mathlib's
`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`.

## Main declarations

* `TauCeti.integral_one_div_sqrt_one_sub_sq`: `∫ x in a..b, 1 / √(1 - x²) = arcsin b - arcsin a`
  for `a, b ∈ (-1, 1)`.
* `TauCeti.integral_cexp_intCast_mul_mul_I`: `∫ θ in -π..π, exp (k θ i)` is `2π` for
  integer `k = 0` and `0` otherwise, the orthogonality of the Fourier characters on `[-π, π]`.
* `TauCeti.integral_cos_pow_mul_cexp`: `∫ θ in -π..π, cosᵏ θ exp (n θ i)` in closed form, via the
  binomial expansion `TauCeti.cos_pow_mul_cexp` of `cosᵏ θ exp (n θ i)` into characters.
* `Real.hasSum_integral_exp_mul_cos_mul_cexp`: `∫ θ in -π..π, e^{κ cos θ} exp (n θ i)` as the
  sum of the termwise integrals of the exponential series of `e^{κ cos θ}`.
-/

public section

open scoped Nat

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
theorem integral_cexp_intCast_mul_mul_I (k : ℤ) :
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

/-- The binomial expansion of `cosᵏ θ exp (n θ i)` into the Fourier characters
`exp ((2m - k + n) θ i)`. -/
theorem cos_pow_mul_cexp (k : ℕ) (n : ℤ) (θ : ℝ) :
    (Real.cos θ : ℂ) ^ k * Complex.exp (n * θ * Complex.I) =
      ∑ m ∈ Finset.range (k + 1), (1 / 2 : ℂ) ^ k * k.choose m *
        Complex.exp (((2 * m - k + n : ℤ) : ℂ) * θ * Complex.I) := by
  have hcos : (Real.cos θ : ℂ) =
      (1 / 2) * (Complex.exp (θ * Complex.I) + Complex.exp (-θ * Complex.I)) := by
    rw [Complex.ofReal_cos, ← Complex.two_cos]
    ring
  rw [hcos, mul_pow, add_pow, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  calc (1 / 2 : ℂ) ^ k * (Complex.exp (m * (θ * Complex.I)) *
        Complex.exp ((k - m : ℕ) * (-θ * Complex.I)) * k.choose m) *
        Complex.exp (n * θ * Complex.I)
      = (1 / 2 : ℂ) ^ k * k.choose m * Complex.exp (m * (θ * Complex.I) +
          (k - m : ℕ) * (-θ * Complex.I) + n * θ * Complex.I) := by
        rw [Complex.exp_add, Complex.exp_add]
        ring
    _ = _ := by
        congr 3
        push_cast [hmk]
        ring

/-- The integral `∫ θ in -π..π, cosᵏ θ exp (n θ i)`, which is `2π` times the `n`-th Fourier
coefficient of the even function `cosᵏ`, read off the binomial expansion `cos_pow_mul_cexp` by
orthogonality of the characters. -/
theorem integral_cos_pow_mul_cexp (k : ℕ) (n : ℤ) :
    ∫ θ in -Real.pi..Real.pi, (Real.cos θ : ℂ) ^ k * Complex.exp (n * θ * Complex.I) =
      ∑ m ∈ Finset.range (k + 1),
        (1 / 2 : ℂ) ^ k * k.choose m * if 2 * m - k + n = 0 then 2 * (Real.pi : ℂ) else 0 := by
  simp_rw [cos_pow_mul_cexp]
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    (by fun_prop : Continuous fun θ : ℝ => (1 / 2 : ℂ) ^ k * k.choose m *
      Complex.exp (((2 * m - k + n : ℤ) : ℂ) * θ * Complex.I)).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_cexp_intCast_mul_mul_I]

end TauCeti

namespace Real

/-- Termwise integration of the exponential series `e^{κ cos θ} = ∑ₖ κᵏ cosᵏ θ / k!` against the
Fourier character `exp (n θ i)` over `[-π, π]`. -/
theorem hasSum_integral_exp_mul_cos_mul_cexp (κ : ℝ) (n : ℤ) :
    HasSum (fun k : ℕ => ((κ ^ k / k ! : ℝ) : ℂ) *
        ∫ θ in -Real.pi..Real.pi, (Real.cos θ : ℂ) ^ k * Complex.exp (n * θ * Complex.I))
      (∫ θ in -Real.pi..Real.pi,
        (Real.exp (κ * Real.cos θ) : ℂ) * Complex.exp (n * θ * Complex.I)) := by
  simp_rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => |κ| ^ k / k !)
    (fun k => by fun_prop) (fun k => MeasureTheory.ae_of_all _ fun θ _ => ?_)
    (MeasureTheory.ae_of_all _ fun _ _ => Real.summable_pow_div_factorial |κ|)
    intervalIntegrable_const (MeasureTheory.ae_of_all _ fun θ _ => ?_)
  · have harg : (n : ℂ) * θ * Complex.I = ((n * θ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have hexp : ‖Complex.exp (n * θ * Complex.I)‖ = 1 := by
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    have hcos : ‖(Real.cos θ : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one θ
    simpa [hexp, abs_div] using
      mul_le_of_le_one_right (by positivity : 0 ≤ |κ| ^ k / k !) (pow_le_one₀ (norm_nonneg _) hcos)
  · have h := (Complex.hasSum_ofReal.mpr
      (NormedSpace.expSeries_div_hasSum_exp (κ * Real.cos θ))).mul_right
        (Complex.exp (n * θ * Complex.I))
    rw [← Real.exp_eq_exp_ℝ] at h
    convert h using 2 with k
    push_cast
    ring

end Real
