/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.ZetaValues
public import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral
import TauCeti.NumberTheory.ZetaValues

/-!
# Periodic Bernoulli kernels on the half-line

This file records Lebesgue integrability on `(0, ∞)` for the periodic Bernoulli kernels
`(B_{2n} - B_{2n}({u})) / (u + z)^k` and `B_{2n}({u}) / (u + z)^k` (`z ∈ Complex.slitPlane`,
`k ≥ 2`), obtained by specializing `TauCeti.integrableOn_div_ofReal_add_pow_of_norm_le` with the
uniform bound `|B_{2n}({u})| ≤ |B_{2n}|` (`TauCeti.abs_bernoulliFun_even_fract_le`), as well as the
positive-real specialization `(B_{2n} - B_{2n}({u})) / (u + x)^k` (`x > 0`, `k ≥ 2`).

## Main declarations

* `TauCeti.integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi`: integrability of
  `(B_{2n} - B_{2n}({u})) / (u + z)^k` on `(0, ∞)` for `z ∈ slitPlane` and `k ≥ 2`.
* `TauCeti.integrableOn_bernoulliFun_fract_div_pow_Ioi`: integrability of
  `B_{2n}({u}) / (u + z)^k` on `(0, ∞)` for `z ∈ slitPlane` and `k ≥ 2`.
* `TauCeti.integrableOn_real_bernoulli_sub_bernoulliFun_div_pow_Ioi`: real-variable integrability
  of `(B_{2n} - B_{2n}({u})) / (u + x)^k` on `(0, ∞)` for `x > 0` and `k ≥ 2`.
-/

public section

open Filter MeasureTheory Set Complex

namespace TauCeti

/-- Integrability of the periodic Bernoulli integrand `(B_{2n} - B_{2n}({u})) / (u + z)^k` on
`(0, ∞)` for `z ∈ slitPlane` and `k ≥ 2`. -/
theorem integrableOn_bernoulli_sub_bernoulliFun_div_pow_Ioi (n : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun u : ℝ ↦
      (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
        ((u : ℂ) + z) ^ k) (Ioi 0) := by
  let g : ℝ → ℂ := fun u ↦
    (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ)
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.measurable.comp
      (measurable_const.sub (measurable_bernoulliFun_fract (2 * n)))).aestronglyMeasurable
  have hg_bdd : ∀ᵐ u ∂(volume.restrict (Ioi 0)), ‖g u‖ ≤ 2 * |(bernoulli (2 * n) : ℝ)| :=
    Eventually.of_forall fun u ↦ by
      have htri : |(bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)| ≤
          |(bernoulli (2 * n) : ℝ)| + |bernoulliFun (2 * n) (Int.fract u)| := by
        simpa using abs_sub_le (bernoulli (2 * n) : ℝ) 0 (bernoulliFun (2 * n) (Int.fract u))
      have hle : |(bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)| ≤
          2 * |(bernoulli (2 * n) : ℝ)| := by
        linarith [abs_bernoulliFun_even_fract_le n u]
      simpa only [g, Complex.norm_real, Real.norm_eq_abs] using hle
  exact integrableOn_div_ofReal_add_pow_of_norm_le hg_meas hg_bdd hz hk

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
  have heq : (((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u) : ℝ) : ℂ) /
      ((u : ℂ) + (x : ℂ)) ^ k =
      ((((bernoulli (2 * n) : ℝ) - bernoulliFun (2 * n) (Int.fract u)) /
        (u + x) ^ k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add, ← Complex.ofReal_pow, ← Complex.ofReal_div]
  simp only [Complex.reCLM_apply, heq, Complex.ofReal_re]

/-- Integrability of Olver's periodic Bernoulli integrand `B_{2n}({u}) / (u + z)^k` on `(0, ∞)`
for `z ∈ slitPlane` and `k ≥ 2`. -/
theorem integrableOn_bernoulliFun_fract_div_pow_Ioi (n : ℕ) {k : ℕ} (hk : 2 ≤ k)
    {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun u : ℝ ↦
      (bernoulliFun (2 * n) (Int.fract u) : ℂ) / ((u : ℂ) + z) ^ k) (Ioi 0) := by
  let g : ℝ → ℂ := fun u ↦ (bernoulliFun (2 * n) (Int.fract u) : ℂ)
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.measurable.comp
      (measurable_bernoulliFun_fract (2 * n))).aestronglyMeasurable
  have hg_bdd : ∀ᵐ u ∂(volume.restrict (Ioi 0)), ‖g u‖ ≤ |(bernoulli (2 * n) : ℝ)| :=
    Eventually.of_forall fun u ↦ by
      simpa [g, Complex.norm_real, Real.norm_eq_abs] using abs_bernoulliFun_even_fract_le n u
  exact integrableOn_div_ofReal_add_pow_of_norm_le hg_meas hg_bdd hz hk

end TauCeti
