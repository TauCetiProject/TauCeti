/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.ZetaValues
public import TauCeti.Analysis.Complex.SlitPlane
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Analysis.SpecialFunctions.Integrals.HalfLineRational
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral
import TauCeti.NumberTheory.ZetaValues

/-!
# Periodic Bernoulli kernels on the half-line

This file records Lebesgue integrability on `(0, ∞)` for the periodic Bernoulli kernels
`(B_{2n} - B_{2n}({u})) / (u + z)^k` and `B_{2n}({u}) / (u + z)^k` (`z ∈ Complex.slitPlane`,
`k ≥ 2`), obtained by specializing `TauCeti.integrableOn_div_ofReal_add_pow_of_norm_le` with the
uniform bound `|B_{2n}({u})| ≤ |B_{2n}|` (`TauCeti.abs_bernoulliFun_even_fract_le`), as well as the
positive-real specialization `(B_{2n} - B_{2n}({u})) / (u + x)^k` (`x > 0`, `k ≥ 2`) and the
integrability and strict positivity of the `(-1)^{n+1}`-scaled kernel.

## Main declarations

* `TauCeti.integrableOn_bernoulliFun_fract_div_pow_Ioi`: integrability of
  `B_{2n}({u}) / (u + z)^k` on `(0, ∞)` for `z ∈ slitPlane` and `k ≥ 2`.
* `TauCeti.integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi`: integrability of
  `(B_{2n} - B_{2n}({u})) / (u + z)^k` on `(0, ∞)` for `z ∈ slitPlane` and `k ≥ 2`.
* `TauCeti.integrableOn_real_bernoulli_sub_bernoulliFun_div_pow_Ioi`: real-variable integrability
  of `(B_{2n} - B_{2n}({u})) / (u + x)^k` on `(0, ∞)` for `x > 0` and `k ≥ 2`.
* `TauCeti.integrableOn_neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_div_pow_Ioi`:
  real-variable integrability of `(-1)^{n+1} (B_{2n} - B_{2n}({u})) / (u + x)^k` on `(0, ∞)`
  for `x > 0`, `k ≥ 2`.
* `TauCeti.integral_neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_div_pow_pos`: strict positivity
  of `∫_{u > 0} (-1)^{n+1} (B_{2n} - B_{2n}({u})) / (u + x)^k` for `n ≥ 1`, `k ≥ 2`, `x > 0`.
-/

public section

open Filter MeasureTheory Set Complex

namespace TauCeti

/-- Integrability of Olver's periodic Bernoulli integrand `B_{2n}({u}) / (u + z)^k` on `(0, ∞)`
for `z ∈ slitPlane` and `k ≥ 2`. -/
theorem integrableOn_bernoulliFun_fract_div_pow_Ioi (n : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun u : ℝ ↦
      (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((u : ℂ) + z) ^ k) (Ioi 0) := by
  let g : ℝ → ℂ := fun u ↦ (bernoulliFun (2 * n) (Int.fract u) : ℂ)
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.measurable.comp
      ((continuous_bernoulliFun (2 * n)).measurable.comp measurable_fract)).aestronglyMeasurable
  have hg_bdd : ∀ᵐ u ∂(volume.restrict (Ioi 0)), ‖g u‖ ≤ |(bernoulli (2 * n) : ℝ)| :=
    Eventually.of_forall fun u ↦ by
      simpa [g, Complex.norm_real, Real.norm_eq_abs] using abs_bernoulliFun_even_fract_le n u
  exact integrableOn_div_ofReal_add_pow_of_norm_le hg_meas hg_bdd hz hk

/-- Integrability of the periodic Bernoulli integrand `(B_{2n} - B_{2n}({u})) / (u + z)^k` on
`(0, ∞)` for `z ∈ slitPlane` and `k ≥ 2`. -/
theorem integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi (n : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun u : ℝ ↦
      (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
        ((u : ℂ) + z) ^ k) (Ioi 0) := by
  have hk2 : k - 2 + 2 = k := Nat.sub_add_cancel hk
  have hconst : IntegrableOn (fun u : ℝ ↦ ((bernoulli (2 * n) : ℝ) : ℂ) / ((u : ℂ) + z) ^ k)
      (Ioi 0) :=
    ((integrableOn_Ioi_one_div_ofReal_add_pow hz (k - 2)).const_mul
      ((bernoulli (2 * n) : ℝ) : ℂ)).congr
      (Eventually.of_forall fun _ ↦ by dsimp only; rw [mul_one_div, hk2])
  exact (hconst.sub (integrableOn_bernoulliFun_fract_div_pow_Ioi n hk hz)).congr
    (Eventually.of_forall fun _ ↦ by simp only [Pi.sub_apply, Complex.ofReal_sub, sub_div])

/-- Real-variable integrability of the periodic Bernoulli integrand
`(B_{2n} - B_{2n}({u})) / (u + x)^k` on `(0, ∞)` for `x > 0` and `k ≥ 2`. -/
theorem integrableOn_real_bernoulli_sub_bernoulliFun_div_pow_Ioi (n : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ ↦
      ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) / (u + x) ^ k)
      (Ioi 0) := by
  have h := Complex.reCLM.integrable_comp
    (integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi n hk (Complex.ofReal_mem_slitPlane.mpr hx))
  refine h.congr (Eventually.of_forall fun u ↦ ?_)
  simp only [Complex.reCLM_apply, ← Complex.ofReal_add, ← Complex.ofReal_pow,
    ← Complex.ofReal_div, Complex.ofReal_re]

/-- Real-variable integrability of the `(-1)^{n+1}`-scaled periodic Bernoulli integrand
`(-1)^{n+1} (B_{2n} - B_{2n}({u})) / (u + x)^k` on `(0, ∞)` for `x > 0` and `k ≥ 2`. -/
theorem integrableOn_neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_div_pow_Ioi (n : ℕ) {k : ℕ}
    (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ ↦
      (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
        (u + x) ^ k) (Ioi 0) :=
  ((integrableOn_real_bernoulli_sub_bernoulliFun_div_pow_Ioi n hk hx).const_mul
    ((-1 : ℝ) ^ (n + 1))).congr (Eventually.of_forall fun _ ↦ (mul_div_assoc _ _ _).symm)

/-- Strict positivity of the `(-1)^{n+1}`-scaled periodic Bernoulli integral on `(0, ∞)`: for
`n ≥ 1`, `k ≥ 2`, and `x > 0`,
`0 < ∫ u in Ioi (0 : ℝ), (-1)^{n+1} (B_{2n} - B_{2n}({u})) / (u + x)^k`. -/
theorem integral_neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_div_pow_pos {n k : ℕ}
    (hn : 1 ≤ n) (hk : 2 ≤ k) {x : ℝ} (hx : 0 < x) :
    0 < ∫ u in Ioi (0 : ℝ),
      (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
        (u + x) ^ k := by
  let f : ℝ → ℝ := fun u ↦
    (-1 : ℝ) ^ (n + 1) * ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
      (u + x) ^ k
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := mem_Ioi.mp hu
    exact div_nonneg (neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_fract_nonneg n u)
      (by positivity)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn
    (integrableOn_neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_div_pow_Ioi n hk hx)]
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support f ∩ Ioi (0 : ℝ) := fun u hu ↦ by
    have hnum : 0 < (-1 : ℝ) ^ (n + 1) *
        ((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) := by
      rw [Int.fract_eq_self.mpr ⟨hu.1.le, hu.2⟩]
      exact neg_one_pow_succ_mul_bernoulli_sub_bernoulliFun_pos (by omega : n ≠ 0) hu
    have hu0 : 0 < u := hu.1
    exact ⟨(div_pos hnum (by positivity)).ne', hu.1⟩
  exact lt_of_lt_of_le (by rw [Real.volume_Ioo]; norm_num) (measure_mono hsub)

end TauCeti
