/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.BesselI
public import TauCeti.Probability.Distributions.VonMisesFisher.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.Probability.Distributions.Uniform.Sphere.Coordinate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# The von Mises–Fisher normalizer in dimension at least two

On a real inner product space `E` of dimension `d ≥ 2`, the von Mises–Fisher normalizer, the
surface integral of `x ↦ exp ⟪η, x⟫` over the unit sphere, is a modified Bessel function of the
first kind of order `d / 2 - 1`: for `η ≠ 0` and `κ = ‖η‖`,

`∫ exp ⟪η, x⟫ dS(x) = (2 π) ^ (d / 2) * κ ^ (1 - d / 2) * I_{d/2-1}(κ)`.

Against the uniform sphere probability `σ`, which divides the surface measure by its total mass
`2 π ^ (d / 2) / Γ(d / 2)`, the same identity reads
`∫ exp ⟪η, x⟫ dσ(x) = Γ(d / 2) * (κ / 2) ^ (1 - d / 2) * I_{d/2-1}(κ)`. At `η = 0` the integrand is
`1`, and the normalizers are the total masses `1` and `2 π ^ (d / 2) / Γ(d / 2)` instead.

This makes the density of the direction/concentration law `vonMisesFisherMeasure m κ` explicit:
for `κ > 0` it is `exp (κ ⟪m, x⟫) / (Γ(d / 2) (κ / 2) ^ (1 - d / 2) I_{d/2-1}(κ))` relative to
`σ`.

The proof reduces to one dimension. The observable `⟪η, x⟫` has the same law as `⟪-η, x⟫`, so
the exponential can be replaced by `cosh ⟪η, x⟫ = ∑ⱼ ⟪η, x⟫ ^ (2 j) / (2 j)!`, and
`⟪η, x⟫ ^ 2 / κ ^ 2` has the Beta law with shapes `1 / 2` and `(d - 1) / 2`
(`map_sq_inner_uniformSphereMeasure`). Integrating the series termwise against the Beta moments
and simplifying `Γ(j + 1 / 2)` by Legendre's duplication formula gives the power series of the
Bessel function `Real.hasSum_besselI`.

## Main results

* `integral_exp_inner_uniformSphereMeasure_eq_besselI` — the normalizer relative to the uniform
  sphere probability;
* `integral_exp_inner_toSphere_eq_besselI` — the normalizer relative to the surface measure
  `volume.toSphere`;
* `vonMisesFisherMeasure_eq_withDensity_besselI` — the density of the direction/concentration law
  relative to the uniform sphere probability.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), §9.3.2.
* *NIST Digital Library of Mathematical Functions*, §10.32.2 (Poisson's integral for `I_ν`, the
  one-dimensional form of the normalizer identity).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Real Set
open scoped ENNReal RealInnerProductSpace Nat

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The `j`th term `⟪η, x⟫ ^ (2 j) / (2 j)!` of the series of `cosh ⟪η, x⟫` integrates against
the uniform sphere law to `Γ(d / 2) (κ / 2) ^ (1 - d / 2)` times the `j`th term of the series of
`I_{d/2-1}(κ)`, where `κ = ‖η‖`. -/
private lemma integral_inner_pow_div_uniformSphereMeasure (hd : 2 ≤ Module.finrank ℝ E) {η : E}
    (hη : η ≠ 0) (j : ℕ) :
    ∫ x : sphere (0 : E) 1, ⟪η, (x : E)⟫ ^ (2 * j) / (2 * j)! ∂uniformSphereMeasure E =
      Gamma ((Module.finrank ℝ E : ℝ) / 2) * (‖η‖ / 2) ^ (1 - (Module.finrank ℝ E : ℝ) / 2) *
        ((‖η‖ / 2) ^ (2 * (j : ℝ) + ((Module.finrank ℝ E : ℝ) / 2 - 1)) /
          (j ! * Gamma (j + ((Module.finrank ℝ E : ℝ) / 2 - 1) + 1))) := by
  set b : ℝ := (Module.finrank ℝ E : ℝ) / 2 with hb_def
  have hκ : 0 < ‖η‖ := norm_pos_iff.2 hη
  have h2 : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hd
  have ha : 0 < ((Module.finrank ℝ E : ℝ) - 1) / 2 := by linarith
  have hb : 0 < b := by linarith
  -- the Beta moment of order `j` of the normalized squared observable
  have hmoment : ∫ x : sphere (0 : E) 1, ⟪η, (x : E)⟫ ^ (2 * j) ∂uniformSphereMeasure E =
      ‖η‖ ^ (2 * j) * (Gamma (1 / 2 + j) * Gamma b / (Gamma (1 / 2) * Gamma (b + j))) := by
    simp_rw [pow_mul]
    rw [← integral_map (f := fun y : ℝ ↦ y ^ j) (by fun_prop) (by fun_prop),
      map_sq_inner_uniformSphereMeasure hd η, integral_map (by fun_prop) (by fun_prop)]
    simp_rw [mul_pow]
    rw [integral_const_mul, integral_pow_betaMeasure (by norm_num) ha,
      show (1 / 2 : ℝ) + ((Module.finrank ℝ E : ℝ) - 1) / 2 = b by rw [hb_def]; ring]
  have hA : 0 < (‖η‖ / 2) ^ (1 - b) := rpow_pos_of_pos (by positivity) _
  have hexp : (‖η‖ / 2) ^ (2 * (j : ℝ) + (b - 1)) =
      ‖η‖ ^ (2 * j) / 4 ^ j / (‖η‖ / 2) ^ (1 - b) := by
    rw [eq_div_iff hA.ne', ← rpow_add (by positivity),
      show 2 * (j : ℝ) + (b - 1) + (1 - b) = ((2 * j : ℕ) : ℝ) by push_cast; ring, rpow_natCast,
      div_pow, pow_mul 2, show (2 : ℝ) ^ 2 = 4 by norm_num]
  have hGb : 0 < Gamma (b + j) := Gamma_pos_of_pos (by positivity)
  rw [integral_div, hmoment, add_comm (1 / 2 : ℝ), Gamma_nat_add_half_eq_factorial,
    Gamma_one_half_eq, hexp, show (j : ℝ) + (b - 1) + 1 = b + j by ring]
  field_simp

/-- **The von Mises–Fisher normalizer.** In dimension `d ≥ 2`, the exponential moment of the
linear observable `⟪η, x⟫` of a uniform sphere point is
`Γ(d / 2) * (‖η‖ / 2) ^ (1 - d / 2) * I_{d/2-1}(‖η‖)` for every `η ≠ 0`. -/
theorem integral_exp_inner_uniformSphereMeasure_eq_besselI (hd : 2 ≤ Module.finrank ℝ E)
    {η : E} (hη : η ≠ 0) :
    ∫ x : sphere (0 : E) 1, exp ⟪η, (x : E)⟫ ∂uniformSphereMeasure E =
      Gamma ((Module.finrank ℝ E : ℝ) / 2) * (‖η‖ / 2) ^ (1 - (Module.finrank ℝ E : ℝ) / 2) *
        besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖ := by
  have hκ : 0 < ‖η‖ := norm_pos_iff.2 hη
  -- `⟪-η, x⟫` has the law of `⟪η, x⟫`, so the exponential moment is that of `cosh ⟪η, x⟫`
  have hsymm : ∫ x : sphere (0 : E) 1, exp ⟪-η, (x : E)⟫ ∂uniformSphereMeasure E =
      ∫ x : sphere (0 : E) 1, exp ⟪η, (x : E)⟫ ∂uniformSphereMeasure E := by
    have h := map_inner_uniformSphereMeasure hd (-η)
    rw [norm_neg, ← map_inner_uniformSphereMeasure hd η] at h
    rw [← integral_map (f := exp) (by fun_prop) (by fun_prop), h,
      integral_map (by fun_prop) (by fun_prop)]
  have hcosh : ∫ x : sphere (0 : E) 1, exp ⟪η, (x : E)⟫ ∂uniformSphereMeasure E =
      ∫ x : sphere (0 : E) 1, cosh ⟪η, (x : E)⟫ ∂uniformSphereMeasure E := by
    have hneg := integrable_exp_inner_uniformSphereMeasure (-η)
    simp_rw [inner_neg_left] at hneg hsymm
    simp_rw [cosh_eq]
    rw [integral_div, integral_add (integrable_exp_inner_uniformSphereMeasure η) hneg, hsymm]
    ring
  -- integrate the power series of `cosh` termwise
  set F : ℕ → sphere (0 : E) 1 → ℝ := fun j x ↦ ⟪η, (x : E)⟫ ^ (2 * j) / (2 * j)! with hF
  have hF_nonneg (j : ℕ) (x : sphere (0 : E) 1) : 0 ≤ F j x := by
    simp only [hF, pow_mul]
    positivity
  have hF_int (j : ℕ) : Integrable (F j) (uniformSphereMeasure E) := by
    refine Integrable.of_bound (by fun_prop) (‖η‖ ^ (2 * j) / (2 * j)!)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (hF_nonneg j x)]
    have hx : |⟪η, (x : E)⟫| ≤ |‖η‖| := by
      simpa using abs_real_inner_le_norm η (x : E)
    simp only [hF, pow_mul]
    gcongr ?_ / _
    exact pow_le_pow_left₀ (sq_nonneg _) (sq_le_sq.2 hx) j
  have hseries := (hasSum_besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) hκ).mul_left
    (Gamma ((Module.finrank ℝ E : ℝ) / 2) * (‖η‖ / 2) ^ (1 - (Module.finrank ℝ E : ℝ) / 2))
  have hsum := hasSum_integral_of_summable_integral_norm hF_int (by
    simp_rw [Real.norm_of_nonneg (hF_nonneg _ _), hF,
      integral_inner_pow_div_uniformSphereMeasure hd hη]
    exact hseries.summable)
  simp_rw [hF, ← cosh_eq_tsum, ← hcosh, integral_inner_pow_div_uniformSphereMeasure hd hη] at hsum
  exact hsum.unique hseries

/-- **The von Mises–Fisher normalizer on the surface measure.** In dimension `d ≥ 2`, the surface
integral of `exp ⟪η, x⟫` over the unit sphere is `(2 π) ^ (d / 2) * ‖η‖ ^ (1 - d / 2) *
I_{d/2-1}(‖η‖)` for every `η ≠ 0`. -/
theorem integral_exp_inner_toSphere_eq_besselI (hd : 2 ≤ Module.finrank ℝ E) {η : E}
    (hη : η ≠ 0) :
    ∫ x : sphere (0 : E) 1, exp ⟪η, (x : E)⟫ ∂(volume : Measure E).toSphere =
      (2 * π) ^ ((Module.finrank ℝ E : ℝ) / 2) * ‖η‖ ^ (1 - (Module.finrank ℝ E : ℝ) / 2) *
        besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) ‖η‖ := by
  have hκ : 0 < ‖η‖ := norm_pos_iff.2 hη
  have : Nontrivial E := ⟨⟨η, 0, hη⟩⟩
  have h2 : (2 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hd
  have hGb : 0 < Gamma ((Module.finrank ℝ E : ℝ) / 2) := Gamma_pos_of_pos (by linarith)
  have hsurf : (volume : Measure E).toSphere =
      (volume : Measure E).toSphere univ • uniformSphereMeasure E := by
    rw [uniformSphereMeasure_def, smul_smul,
      ENNReal.mul_inv_cancel (Measure.measure_univ_ne_zero.2 (Measure.toSphere_ne_zero _))
        (measure_ne_top _ _), one_smul]
  rw [hsurf, integral_smul_measure, integral_exp_inner_uniformSphereMeasure_eq_besselI hd hη,
    TauCeti.toSphere_volume_apply_univ, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    div_rpow hκ.le zero_le_two, mul_rpow zero_le_two pi_pos.le,
    rpow_sub two_pos, rpow_one]
  field_simp

/-- **The von Mises–Fisher density.** In dimension `d ≥ 2`, the von Mises–Fisher law with unit
direction `m` and concentration `κ > 0` has density
`exp (κ ⟪m, x⟫) / (Γ(d / 2) (κ / 2) ^ (1 - d / 2) I_{d/2-1}(κ))` relative to the uniform sphere
law. -/
theorem vonMisesFisherMeasure_eq_withDensity_besselI (hd : 2 ≤ Module.finrank ℝ E)
    (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 < κ) :
    vonMisesFisherMeasure m κ = (uniformSphereMeasure E).withDensity fun x ↦
      ENNReal.ofReal (exp (κ * ⟪(m : E), (x : E)⟫) /
        (Gamma ((Module.finrank ℝ E : ℝ) / 2) * (κ / 2) ^ (1 - (Module.finrank ℝ E : ℝ) / 2) *
          besselI ((Module.finrank ℝ E : ℝ) / 2 - 1) κ)) := by
  have hη : κ • (m : E) ≠ 0 := smul_ne_zero hκ.ne' (ne_zero_of_mem_sphere one_ne_zero m)
  have hnorm : ‖κ • (m : E)‖ = κ := by simp [norm_smul, abs_of_pos hκ]
  rw [vonMisesFisherMeasure_of_nonneg m hκ.le, vonMisesFisherNaturalMeasure_eq_withDensity,
    integral_exp_inner_uniformSphereMeasure_eq_besselI hd hη, hnorm]
  simp_rw [real_inner_smul_left]

end TauCeti.Probability
