/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.HaagerupZsido.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.HalfLineRational
import TauCeti.Analysis.SpecialFunctions.Trigonometric.TanhSeries

/-!
# The Haagerup–Zsidó weight against adjacent Cauchy resolvents

For `a ≥ 0`, the weight `w(y) = tanh (π y / 2)` of the Haagerup–Zsidó kernel satisfies

`∫_{y > 0} w(y) y ((y² + a²)⁻¹ - (y² + (a + 2)²)⁻¹) dy = 2 / (a + 1)`.

This is the `y`-integral to which the Fourier integral `∫ k(t) e^{itx} dt` of the kernel reduces
by Fubini at `x = a + 1 ≥ 1`: pairing the oscillation `sin t e^{itx}` with the damped exponential
`e^{-|t| y}` produces the two Lorentzians `y / (y² + (x ∓ 1)²)`, whose centres differ by `2`.
Evaluating it is the analytic core of the exterior reciprocal identity
`∫ k(t) e^{itx} dt = 1 / x` for `|x| ≥ 1`.

The proof expands the weight into its odd poles, `w(y) y = (4 / π) ∑_{n ≥ 0} y² / (y² + (2 n + 1)²)`
(`TauCeti.hasSum_pi_div_two_mul_tanh`). Each term integrates against the two resolvents by
`TauCeti.integral_Ioi_sq_div_sq_add_sq_mul_sq_add_sq`, to
`2 (1 / (a + 2 n + 1) - 1 / (a + 2 n + 3))`. These terms are nonnegative, so the sum and the
integral commute, and the series telescopes to `2 / (a + 1)`.

## Main results

* `TauCeti.HaagerupZsido.integral_weight_mul_mul_inv_sub_inv`: the value `2 / (a + 1)`;
* `TauCeti.HaagerupZsido.integrableOn_weight_mul_mul_inv_sub_inv`: the integrand is integrable on
  `(0, ∞)`.

## References

* U. Haagerup, L. Zsidó, the extremal kernel attaining the constant `π / 2`; see the account in
  S. Albeverio, K. A. Makarov, A. K. Motovilov, *Graph subspaces and the spectral shift function*,
  Canad. J. Math. **55** (2003), 449–503.
-/

public section

open Filter MeasureTheory Set
open scoped Real Topology

namespace TauCeti.HaagerupZsido

/-- The `n`-th odd-pole term of `w(y) y ((y² + a²)⁻¹ - (y² + (a + 2)²)⁻¹)`. -/
private noncomputable def oddPoleTerm (a : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  4 / π * (y ^ 2 / ((y ^ 2 + a ^ 2) * (y ^ 2 + (2 * n + 1) ^ 2)) -
    y ^ 2 / ((y ^ 2 + (a + 2) ^ 2) * (y ^ 2 + (2 * n + 1) ^ 2)))

private theorem hasSum_oddPoleTerm (a y : ℝ) :
    HasSum (fun n ↦ oddPoleTerm a n y)
      (weight y * y * ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹)) := by
  convert (hasSum_pi_div_two_mul_tanh y).mul_left
    (2 / π * y * ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹)) using 1
  · ext n
    simp only [oddPoleTerm, div_eq_mul_inv, mul_inv]
    ring
  · rw [weight_def]
    field_simp

private theorem oddPoleTerm_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    0 ≤ oddPoleTerm a n y := by
  refine mul_nonneg (by positivity) (sub_nonneg.mpr ?_)
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  gcongr
  linarith

private theorem integrableOn_oddPoleTerm {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    IntegrableOn (oddPoleTerm a n) (Ioi 0) := by
  have hc : (0 : ℝ) ≤ 2 * n + 1 := by positivity
  exact ((integrableOn_sq_div_sq_add_sq_mul_sq_add_sq ha hc (by positivity)).sub
    (integrableOn_sq_div_sq_add_sq_mul_sq_add_sq (by positivity) hc (by positivity))).const_mul _

private theorem integral_oddPoleTerm {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ∫ y in Ioi 0, oddPoleTerm a n y = 2 * (1 / (a + 2 * n + 1) - 1 / (a + 2 * (n + 1) + 1)) := by
  have hc : (0 : ℝ) ≤ 2 * n + 1 := by positivity
  simp only [oddPoleTerm]
  rw [integral_const_mul, integral_sub (integrableOn_sq_div_sq_add_sq_mul_sq_add_sq ha hc
    (by positivity)) (integrableOn_sq_div_sq_add_sq_mul_sq_add_sq (by positivity) hc
    (by positivity)), integral_Ioi_sq_div_sq_add_sq_mul_sq_add_sq ha hc (by positivity),
    integral_Ioi_sq_div_sq_add_sq_mul_sq_add_sq (by positivity) hc (by positivity)]
  field_simp
  ring

/-- The telescoping series `∑_{n ≥ 0} 2 (1 / (a + 2 n + 1) - 1 / (a + 2 n + 3)) = 2 / (a + 1)`. -/
private theorem hasSum_integral_oddPoleTerm {a : ℝ} (ha : 0 ≤ a) :
    HasSum (fun n : ℕ ↦ ∫ y in Ioi 0, oddPoleTerm a n y) (2 / (a + 1)) := by
  simp only [integral_oddPoleTerm ha]
  set g : ℕ → ℝ := fun n ↦ 1 / (a + 2 * n + 1)
  have hg : Tendsto g atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ ?_)
    exact tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  have hmono (n : ℕ) : 0 ≤ g n - g (n + 1) := by
    simp only [g, Nat.cast_add, Nat.cast_one, sub_nonneg]
    gcongr
    linarith
  have h : HasSum (fun n ↦ g n - g (n + 1)) (g 0) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hmono]
    simp only [Finset.sum_range_sub']
    simpa using (tendsto_const_nhds (x := g 0)).sub hg
  convert h.mul_left 2 using 1
  · simp [g]
  · simp only [g, Nat.cast_zero, mul_zero, add_zero]
    ring

/-- **The weight against adjacent Cauchy resolvents.** For `a ≥ 0`,
`∫_{y > 0} w(y) y ((y² + a²)⁻¹ - (y² + (a + 2)²)⁻¹) dy = 2 / (a + 1)`, where
`w(y) = tanh (π y / 2)` is the Haagerup–Zsidó weight. -/
theorem integral_weight_mul_mul_inv_sub_inv {a : ℝ} (ha : 0 ≤ a) :
    ∫ y in Ioi 0, weight y * y * ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹) = 2 / (a + 1) := by
  have hnorm : (fun n : ℕ ↦ ∫ y in Ioi 0, ‖oddPoleTerm a n y‖) =
      fun n ↦ ∫ y in Ioi 0, oddPoleTerm a n y := by
    ext n
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    exact Real.norm_of_nonneg (oddPoleTerm_nonneg ha n hy)
  have h := hasSum_integral_of_summable_integral_norm (integrableOn_oddPoleTerm ha)
    (hnorm ▸ (hasSum_integral_oddPoleTerm ha).summable)
  rw [(hasSum_integral_oddPoleTerm ha).unique h]
  exact integral_congr_ae (ae_of_all _ fun y ↦ (hasSum_oddPoleTerm a y).tsum_eq.symm)

/-- For `a ≥ 0`, the function `w(y) y ((y² + a²)⁻¹ - (y² + (a + 2)²)⁻¹)` is integrable on
`(0, ∞)`. -/
theorem integrableOn_weight_mul_mul_inv_sub_inv {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun y ↦ weight y * y * ((y ^ 2 + a ^ 2)⁻¹ - (y ^ 2 + (a + 2) ^ 2)⁻¹))
      (Ioi 0) :=
  Integrable.of_integral_ne_zero <| by
    rw [integral_weight_mul_mul_inv_sub_inv ha]
    positivity

end TauCeti.HaagerupZsido
