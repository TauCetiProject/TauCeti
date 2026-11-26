/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.Basic
import TauCeti.MeasureTheory.Integral.Bochner.PowerTail

/-!
# Mean bounds for quadratic-twist theta tails

A pointwise second moment of the theta series and their Möbius twists bounds the sum of their
joint tail integrals. For Jacobi twists, a uniform second moment over the numerators gives the
first-moment bound used to count twists with large tails.

## References

* The mean-tail estimate `New.sum_thetaTailIntegral_le` in `Lib/Analytic/QuadraticTwist.lean`
  under `grh/src` of <https://github.com/lsernau/grh-lean> (revision `72fead1`).
-/

public section

open MeasureTheory Real Set
open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-- A joint second-moment bound for normalized Gaussian theta series and their Möbius twists
controls the sum of their tail masses. The bound is allowed to hold only almost everywhere
above the cutoff. -/
theorem sum_quadraticTwistGaussianThetaTailIntegral_le_of_sum_sq_le
    {ι : Type*} {s : Finset ι} {j : Fin 2} {c : ι → ℕ → ℂ} {T δ C : ℝ}
    (hT : 0 < T) (hδ : 0 < δ)
    (hmoment : ∀ᵐ u ∂(volume.restrict (Ioi T⁻¹)),
      (∑ i ∈ s, (‖gaussianThetaSeries j (c i) u‖ ^ 2 +
        ‖gaussianThetaSeries j (fun n ↦ c i n * μ n) u‖ ^ 2)) ≤ C * u ^ (-2 * δ)) :
    ∑ i ∈ s, quadraticTwistGaussianThetaTailIntegral j (c i) T ≤
      √(s.card : ℝ) * √(2 * C) * T ^ δ / δ := by
  let f (i : ι) (u : ℝ) := ‖gaussianThetaSeries j (c i) u‖ +
    ‖gaussianThetaSeries j (fun n ↦ c i n * μ n) u‖
  have hf : ∀ i u, ‖f i u‖ = f i u :=
    fun i u ↦ norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsq : ∀ᵐ u ∂(volume.restrict (Ioi T⁻¹)), ∑ i ∈ s, ‖f i u‖ ^ 2 ≤
      (2 * C) * u ^ (-2 * δ) := by
    filter_upwards [hmoment] with u hu
    simp only [hf, mul_assoc]
    calc
      ∑ i ∈ s, f i u ^ 2 ≤ 2 * ∑ i ∈ s, (‖gaussianThetaSeries j (c i) u‖ ^ 2 +
          ‖gaussianThetaSeries j (fun n ↦ c i n * μ n) u‖ ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun _ _ ↦ add_sq_le
      _ ≤ 2 * (C * u ^ (-2 * δ)) := mul_le_mul_of_nonneg_left hu (by norm_num)
  simpa only [hf, f, quadraticTwistGaussianThetaTailIntegral_def,
    Real.inv_rpow hT.le, ← Real.rpow_neg hT.le, neg_neg] using
    sum_setIntegral_norm_div_le_of_sum_sq_le (inv_pos.mpr hT) hδ hsq

/-- If the Jacobi-twisted theta second moment is at most `C T² u⁻²ᵟ` uniformly over
unit-bounded coefficients, the sum of the joint tails over `1 ≤ v ≤ T²` is at most
`(2 √C / δ) T^(2 + δ)`. Uniformity allows application to the original coefficient sequence
and also to its Möbius twist, with the same constant. -/
theorem sum_quadraticTwistGaussianThetaTailIntegral_jacobiSym_le
    {j : Fin 2} {c : ℕ → ℂ} {T δ C : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1)
    (hmoment : ∀ b : ℕ → ℂ, (∀ n : ℕ+, ‖b n‖ ≤ 1) →
      ∀ᵐ u ∂(volume.restrict (Ioi T⁻¹)),
        ∑ v ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, ‖gaussianThetaSeries j
          (fun n ↦ b n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2 ≤
          C * T ^ 2 * u ^ (-2 * δ)) :
    ∑ v ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, quadraticTwistGaussianThetaTailIntegral j
      (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) T ≤
      (2 * √C / δ) * T ^ (2 + δ) := by
  let s := Finset.Icc 1 ⌊T ^ 2⌋₊
  let twist (b : ℕ → ℂ) (v n : ℕ) := b n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)
  have hμ (n : ℕ+) : ‖c n * (μ n : ℂ)‖ ≤ 1 := by
    have hnorm : ‖(μ n : ℂ)‖ ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hnorm).trans (hc n)
  have hjoint : ∀ᵐ u ∂(volume.restrict (Ioi T⁻¹)),
      (∑ v ∈ s, (‖gaussianThetaSeries j (twist c v) u‖ ^ 2 +
        ‖gaussianThetaSeries j (fun n ↦ twist c v n * μ n) u‖ ^ 2)) ≤
          (2 * (C * T ^ 2)) * u ^ (-2 * δ) := by
    filter_upwards [hmoment c hc, hmoment (fun n ↦ c n * μ n) hμ] with u h₁ h₂
    have htwist (v : ℕ) : (fun n ↦ twist c v n * μ n) = twist (fun n ↦ c n * μ n) v := by
      funext n
      exact mul_right_comm _ _ _
    simp only [htwist, Finset.sum_add_distrib, mul_assoc]
    simpa only [s, twist, mul_assoc, two_mul] using add_le_add h₁ h₂
  have hcard : (s.card : ℝ) ≤ T ^ 2 := by
    simpa [s, Nat.card_Icc] using Nat.floor_le (sq_nonneg T)
  refine (sum_quadraticTwistGaussianThetaTailIntegral_le_of_sum_sq_le hT hδ hjoint).trans ?_
  have hsqrt : √(2 * (2 * (C * T ^ 2))) = 2 * √C * T := by
    have hprod : 2 * (2 * (C * T ^ 2)) = 2 ^ 2 * (T ^ 2 * C) := by ring
    rw [hprod, Real.sqrt_mul (sq_nonneg _), Real.sqrt_mul (sq_nonneg T),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hT.le]
    ring
  rw [hsqrt, Real.rpow_add hT, Real.rpow_two]
  calc
    √(s.card : ℝ) * (2 * √C * T) * T ^ δ / δ ≤ T * (2 * √C * T) * T ^ δ / δ := by
      gcongr
      simpa [Real.sqrt_sq hT.le] using Real.sqrt_le_sqrt hcard
    _ = 2 * √C / δ * (T ^ 2 * T ^ δ) := by ring

end TauCeti
