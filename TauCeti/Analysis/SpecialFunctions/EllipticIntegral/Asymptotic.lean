/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.ModulusDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The complete elliptic integrals near modulus one

The complete integral of the first kind has a logarithmic singularity at `k = 1`
(DLMF 19.12.1): with `k' = √(1 - k²)`,

`K(k) - log (4 / k') → 0` as `k → 1⁻`.

The integral of the second kind stays bounded: `E(k) → E(1) = 1`. The product
`(1 - k²) K(k)` tends to zero; for this the elementary bound `K(k) ≤ π / (2 k')` already
suffices, without the logarithmic expansion. These are the boundary values from which
Legendre's relation `E K' + E' K - K K' = π / 2` is evaluated, in the limit `k → 0⁺` of its
complementary modulus.

The singularity is extracted by comparing `K(k)` with the elementary integral
`∫₀^{π/2} k sin θ (1 - k² sin² θ)^(-1/2) dθ = log ((1 + k) / k')`. Their difference has the
integrand `√((1 - k sin θ) / (1 + k sin θ))`, which is bounded by `1` and converges as `k → 1⁻`
to `cos θ / (1 + sin θ)`, whose integral over `[0, π/2]` is `log 2`.

## Main statements

* `TauCeti.Real.tendsto_legendreK_sub_log_nhdsLT_one`: `K(k) - log (4 / √(1 - k²)) → 0` as
  `k → 1⁻`.
* `TauCeti.Real.tendsto_legendreEc_nhds_one`: `E(k) → 1` as `k → 1`.
* `TauCeti.Real.tendsto_one_sub_sq_mul_legendreK_nhdsLT_one`: `(1 - k²) K(k) → 0` as `k → 1⁻`.

## References

* NIST *Digital Library of Mathematical Functions*, §§19.7 and 19.12,
  <https://dlmf.nist.gov/19.12>.
-/

public section

namespace TauCeti.Real

open _root_.Real Filter MeasureTheory intervalIntegral Set
open scoped Interval Topology

/-- The elementary companion of `K(k)`: for `k ^ 2 < 1`,
`∫₀^{π/2} k sin θ (1 - k² sin² θ)^(-1/2) dθ = log (1 + k) - log √(1 - k²)`, as
`θ ↦ -log (k cos θ + √(1 - k² sin² θ))` is an antiderivative. -/
private theorem integral_mul_sin_mul_legendreF_integrand {k : ℝ} (hk : k ^ 2 < 1) :
    ∫ θ in (0 : ℝ)..π / 2, k * sin θ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) =
      log (1 + k) - log √(1 - k ^ 2) := by
  have hderiv (θ : ℝ) : HasDerivAt (fun θ ↦ -log (k * cos θ + √(1 - k ^ 2 * sin θ ^ 2)))
      (k * sin θ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) θ := by
    have hΔ := one_sub_mul_sin_sq_pos hk θ
    have hs : 0 < √(1 - k ^ 2 * sin θ ^ 2) := sqrt_pos.2 hΔ
    have hss : √(1 - k ^ 2 * sin θ ^ 2) ^ 2 = 1 - k ^ 2 * sin θ ^ 2 := sq_sqrt hΔ.le
    -- `k cos θ + √(1 - k² sin² θ) > 0`, as `(1 - k² sin² θ) - k² cos² θ = 1 - k² > 0`
    have hu : 0 < k * cos θ + √(1 - k ^ 2 * sin θ ^ 2) := by
      nlinarith [sin_sq_add_cos_sq θ, sq_nonneg (k * cos θ + √(1 - k ^ 2 * sin θ ^ 2))]
    have hΔ' : HasDerivAt (fun θ ↦ 1 - k ^ 2 * sin θ ^ 2)
        (-(k ^ 2 * (2 * sin θ * cos θ))) θ := by
      simpa using ((hasDerivAt_sin θ).pow 2).const_mul (k ^ 2) |>.const_sub 1
    have h := (((hasDerivAt_cos θ).const_mul k).add (hΔ'.sqrt hΔ.ne')).log hu.ne' |>.neg
    convert h using 1
    rw [legendreF_integrand_eq_inv_sqrt, Pi.add_apply]
    field_simp
    ring
  have hcont : Continuous fun θ ↦ k * sin θ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) :=
    (continuous_const.mul continuous_sin).mul (continuous_legendreF_integrand hk)
  rw [integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hderiv θ) (hcont.intervalIntegrable _ _)]
  simp [add_comm, sub_eq_add_neg]

/-- The difference `K(k) - ∫₀^{π/2} k sin θ (1 - k² sin² θ)^(-1/2) dθ` tends to `log 2` as
`k → 1⁻`, by dominated convergence. -/
private theorem tendsto_integral_one_sub_mul_sin_mul_legendreF_integrand :
    Tendsto (fun k : ℝ ↦
        ∫ θ in (0 : ℝ)..π / 2, (1 - k * sin θ) * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ))
      (𝓝[<] 1) (𝓝 (log 2)) := by
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[<] 1 := Ioo_mem_nhdsLT one_pos
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  -- on `Ι 0 (π / 2)` we have `0 ≤ sin θ ≤ 1` and `0 ≤ cos θ`
  have hsin : ∀ θ ∈ Ι (0 : ℝ) (π / 2), 0 ≤ sin θ ∧ sin θ ≤ 1 ∧ 0 ≤ cos θ := by
    intro θ hθ
    rw [uIoc_of_le hpi] at hθ
    exact ⟨sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos]), sin_le_one θ,
      cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩⟩
  -- the limiting integrand `cos θ / (1 + sin θ)` has antiderivative `log (1 + sin θ)`
  have hlog2 : ∫ θ in (0 : ℝ)..π / 2, cos θ / (1 + sin θ) = log 2 := by
    have hpos : ∀ θ ∈ uIcc 0 (π / 2), 0 < 1 + sin θ := fun θ hθ ↦ by
      rw [uIcc_of_le hpi] at hθ
      linarith [sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos])]
    rw [integral_eq_sub_of_hasDerivAt (f := fun θ ↦ log (1 + sin θ))
      (f' := fun θ ↦ cos θ / (1 + sin θ))
      (fun θ hθ ↦ by simpa using ((hasDerivAt_sin θ).const_add 1).log (hpos θ hθ).ne')
      (ContinuousOn.intervalIntegrable (continuous_cos.continuousOn.div
        (continuous_const.add continuous_sin).continuousOn fun θ hθ ↦ (hpos θ hθ).ne'))]
    norm_num
  -- dominated convergence, with the integrand `√(1 - k sin θ) / √(1 + k sin θ)` bounded by `1`
  rw [← hlog2]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [hmem] with k hk
    have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
    exact ((continuous_const.sub (continuous_const.mul continuous_sin)).mul
      (continuous_legendreF_integrand hk2)).aestronglyMeasurable
  · filter_upwards [hmem] with k hk
    refine ae_of_all _ fun θ hθ ↦ ?_
    obtain ⟨hs0, -, -⟩ := hsin θ hθ
    have hks0 : 0 ≤ k * sin θ := mul_nonneg hk.1.le hs0
    rw [← mul_pow, one_sub_mul_one_sub_sq_rpow_neg_one_div_two, norm_of_nonneg (by positivity),
      div_le_one (sqrt_pos.2 (by linarith))]
    exact sqrt_le_sqrt (by linarith)
  · refine ae_of_all _ fun θ hθ ↦ ?_
    obtain ⟨hs0, hs1, hc0⟩ := hsin θ hθ
    -- the limit `√(1 - sin θ) / √(1 + sin θ)` is `cos θ / (1 + sin θ)`
    have hlim : √(1 - sin θ) / √(1 + sin θ) = cos θ / (1 + sin θ) := by
      have hc : cos θ = √(1 - sin θ) * √(1 + sin θ) := by
        rw [← sqrt_mul (by linarith), show (1 - sin θ) * (1 + sin θ) = cos θ ^ 2 by
          nlinarith [sin_sq_add_cos_sq θ], sqrt_sq hc0]
      have := sq_sqrt (show (0 : ℝ) ≤ 1 + sin θ by linarith)
      have := sqrt_pos.2 (show (0 : ℝ) < 1 + sin θ by linarith)
      rw [hc]
      field_simp
      nlinarith
    have hcont : ContinuousAt (fun k : ℝ ↦ √(1 - k * sin θ) / √(1 + k * sin θ)) 1 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (sqrt_pos.2 (by linarith)).ne'
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simp only [one_mul, hlim] at h
    refine h.congr' ?_
    filter_upwards with k
    rw [← mul_pow, one_sub_mul_one_sub_sq_rpow_neg_one_div_two]

/-- **The logarithmic singularity of `K` at modulus one** (DLMF 19.12.1): as `k → 1⁻`,
`K(k) - log (4 / √(1 - k²)) → 0`. -/
theorem tendsto_legendreK_sub_log_nhdsLT_one :
    Tendsto (fun k ↦ legendreK k - log (4 / √(1 - k ^ 2))) (𝓝[<] 1) (𝓝 0) := by
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[<] 1 := Ioo_mem_nhdsLT one_pos
  have hlog : Tendsto (fun k : ℝ ↦ log (1 + k) - log 4) (𝓝[<] 1) (𝓝 (log 2 - log 4)) := by
    have h : ContinuousAt (fun k : ℝ ↦ log (1 + k) - log 4) 1 :=
      ((continuous_const.add continuous_id).continuousAt.log (by norm_num)).sub continuousAt_const
    simpa [one_add_one_eq_two] using h.tendsto.mono_left nhdsWithin_le_nhds
  have h := tendsto_integral_one_sub_mul_sin_mul_legendreF_integrand.add hlog
  rw [show log 2 + (log 2 - log 4) = 0 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, log_mul two_ne_zero two_ne_zero]; ring] at h
  refine h.congr' ?_
  filter_upwards [hmem] with k hk
  have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
  have hc : √(1 - k ^ 2) ≠ 0 := (sqrt_pos.2 (by linarith)).ne'
  -- split `K(k)` as the integral above plus its elementary companion
  have hsplit : legendreK k =
      (∫ θ in (0 : ℝ)..π / 2, (1 - k * sin θ) * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) +
        ∫ θ in (0 : ℝ)..π / 2, k * sin θ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) := by
    rw [← intervalIntegral.integral_add, legendreK_def, legendreF_def]
    · exact integral_congr fun θ _ ↦ by ring
    · exact ((continuous_const.sub (continuous_const.mul continuous_sin)).mul
        (continuous_legendreF_integrand hk2)).intervalIntegrable _ _
    · exact ((continuous_const.mul continuous_sin).mul
        (continuous_legendreF_integrand hk2)).intervalIntegrable _ _
  rw [hsplit, integral_mul_sin_mul_legendreF_integrand hk2, log_div (by norm_num) hc]
  ring

/-- **The integral of the second kind at modulus one**: `E(k) → E(1) = 1` as `k → 1`. -/
theorem tendsto_legendreEc_nhds_one : Tendsto legendreEc (𝓝 1) (𝓝 1) := by
  simpa [legendreEc_one] using continuous_legendreEc.tendsto 1

/-- The singularity of `K` at modulus one is killed by the factor `1 - k²`.
This is the vanishing boundary term used in Legendre's relation. -/
theorem tendsto_one_sub_sq_mul_legendreK_nhdsLT_one :
    Tendsto (fun k : ℝ ↦ (1 - k ^ 2) * legendreK k) (𝓝[<] 1) (𝓝 0) := by
  have hupper : Tendsto (fun k : ℝ ↦ π / 2 * √(1 - k ^ 2)) (𝓝[<] 1) (𝓝 0) := by
    have h := (by fun_prop : Continuous fun k : ℝ ↦ π / 2 * √(1 - k ^ 2)).tendsto 1
    simpa using h.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ k : ℝ in 𝓝[<] 1, k ∈ Ioo 0 1 := Ioo_mem_nhdsLT one_pos
  refine tendsto_const_nhds.squeeze' hupper ?_ ?_
  · filter_upwards [hmem] with k hk
    have hk' : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
    exact mul_nonneg (by linarith) (legendreK_pos hk').le
  · filter_upwards [hmem] with k hk
    have hk' : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
    have hs : 0 < √(1 - k ^ 2) := sqrt_pos.2 (by linarith)
    calc
      (1 - k ^ 2) * legendreK k ≤ (1 - k ^ 2) * (π / 2 / √(1 - k ^ 2)) :=
        mul_le_mul_of_nonneg_left (legendreK_le_pi_div_two_div_sqrt hk') (by linarith)
      _ = π / 2 * √(1 - k ^ 2) := by
        field_simp [hs.ne']
        nlinarith [sq_sqrt (by linarith : 0 ≤ 1 - k ^ 2)]

end TauCeti.Real
