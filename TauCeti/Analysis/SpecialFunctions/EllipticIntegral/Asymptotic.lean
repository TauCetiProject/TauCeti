/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Elementary
import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.ModulusDerivative
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The complete elliptic integrals near modulus one

The complete integral of the first kind has a logarithmic singularity at `k = 1` (DLMF 19.12.1):
with `k' = √(1 - k²)`,

`K(k) - log (4 / k') → 0` as `k → 1⁻`.

In particular `(1 - k²) K(k) → 0`, while `E(k) → E(1) = 1`. These limits are what is needed to
evaluate expressions such as `E K' + E' K - K K'` at the endpoints of `(0, 1)`.

The proof splits the integrand of `K(k)` as `(1 - sin θ) Δ^(-1/2) + sin θ Δ^(-1/2)`, where
`Δ = 1 - k² sin² θ`. The second part integrates in closed form,
`∫₀^{π/2} sin θ Δ^(-1/2) dθ = artanh k / k`, and `artanh k - log (4 / k') → -log 2`. The first
part is dominated by `1`, and by dominated convergence it tends to
`∫₀^{π/2} cos θ / (1 + sin θ) dθ = log 2`.

## Main statements

* `TauCeti.Real.integral_sin_mul_one_sub_sq_mul_sin_sq_rpow_neg_half`:
  `∫₀^{π/2} sin θ (1 - k² sin² θ)^(-1/2) dθ = artanh k / k` for `0 < k² < 1`.
* `TauCeti.Real.tendsto_legendreK_sub_log_nhdsLT_one`: `K(k) - log (4 / √(1 - k²)) → 0` as
  `k → 1⁻`.
* `TauCeti.Real.tendsto_one_sub_sq_mul_legendreK_nhdsLT_one`: `(1 - k²) K(k) → 0` as `k → 1⁻`.
* `TauCeti.Real.tendsto_legendreEc_one`: `E(k) → 1` as `k → 1`.

## References

* NIST *Digital Library of Mathematical Functions*, §19.12, <https://dlmf.nist.gov/19.12>.
-/

public section

namespace TauCeti.Real

open _root_.Real Filter MeasureTheory intervalIntegral Set
open scoped Topology

/-! ### A closed form for the singular part -/

/-- The singular part of `K(k)` in closed form: for `k ≠ 0` with `k ^ 2 < 1`,
`∫₀^{π/2} sin θ (1 - k² sin² θ)^(-1/2) dθ = artanh k / k`. -/
theorem integral_sin_mul_one_sub_sq_mul_sin_sq_rpow_neg_half {k : ℝ} (hk₀ : k ≠ 0)
    (hk : k ^ 2 < 1) :
    ∫ θ in (0 : ℝ)..π / 2, sin θ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) = artanh k / k := by
  set k' := √(1 - k ^ 2)
  have hk' : 0 < k' := sqrt_pos.2 (by linarith)
  have hk'sq : k' ^ 2 = 1 - k ^ 2 := sq_sqrt (by linarith)
  -- An antiderivative is `-arsinh (k cos θ / k') / k`, since
  -- `1 + (k cos θ / k')² = (1 - k² sin² θ) / k'²`.
  have hderiv : ∀ θ ∈ uIcc 0 (π / 2), HasDerivAt (fun θ ↦ -arsinh (k * cos θ / k') / k)
      (sin θ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) θ := by
    intro θ _
    have hΔ := one_sub_mul_sin_sq_pos hk θ
    have hsq : √(1 + (k * cos θ / k') ^ 2) = √(1 - k ^ 2 * sin θ ^ 2) / k' := by
      rw [← sqrt_sq hk'.le, ← sqrt_div' _ (sq_nonneg _), sqrt_sq hk'.le]
      congr 1
      field_simp
      rw [hk'sq]
      nlinarith [sin_sq_add_cos_sq θ]
    refine ((((hasDerivAt_cos θ).const_mul k).div_const k').arsinh.neg.div_const k).congr_deriv ?_
    rw [hsq, legendreF_integrand_eq_inv_sqrt, smul_eq_mul]
    have := (sqrt_pos.2 hΔ).ne'
    field_simp
  have hint : IntervalIntegrable (fun θ ↦ sin θ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ))
      volume 0 (π / 2) :=
    (continuous_sin.mul (continuous_legendreF_integrand hk)).intervalIntegrable _ _
  have hartanh : arsinh (k / k') = artanh k := by
    have hmem : k ∈ Ioo (-1 : ℝ) 1 := by
      rw [mem_Ioo, ← abs_lt, ← sq_lt_one_iff_abs_lt_one]
      exact hk
    rw [← sinh_artanh hmem, arsinh_sinh]
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, cos_pi_div_two, cos_zero, mul_zero, zero_div,
    arsinh_zero, mul_one, hartanh]
  ring

/-! ### The regular part -/

/-- The integrand of the regular part of `K(k)` is bounded by `1` on `[0, π / 2]`. -/
private theorem one_sub_sin_mul_rpow_le_one {k θ : ℝ} (hk : k ^ 2 < 1) (h0 : 0 ≤ sin θ) :
    (1 - sin θ) * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) ≤ 1 := by
  have hΔ := one_sub_mul_sin_sq_pos hk θ
  have hs1 := sin_le_one θ
  rw [legendreF_integrand_eq_inv_sqrt, ← div_eq_mul_inv, div_le_one (sqrt_pos.2 hΔ)]
  -- `1 - k² sin² θ ≥ 1 - sin² θ ≥ (1 - sin θ)²`.
  refine le_sqrt_of_sq_le ?_
  nlinarith [mul_le_mul_of_nonneg_right (by linarith : k ^ 2 ≤ 1) (sq_nonneg (sin θ))]

/-- The limit of the regular part: `∫₀^{π/2} (1 - sin θ) (1 - sin² θ)^(-1/2) dθ = log 2`. -/
private theorem integral_one_sub_sin_mul_rpow_one :
    ∫ θ in (0 : ℝ)..π / 2, (1 - sin θ) * (1 - 1 ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) = log 2 := by
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  have hsin : ∀ θ ∈ uIcc 0 (π / 2), 0 ≤ sin θ := fun θ hθ ↦ by
    rw [uIcc_of_le hpi] at hθ
    exact sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos])
  -- On `[0, π / 2]` the integrand is `(1 - sin θ) / cos θ = cos θ / (1 + sin θ)`, the derivative
  -- of `log (1 + sin θ)`.
  have heq : EqOn (fun θ ↦ (1 - sin θ) * (1 - 1 ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ))
      (fun θ ↦ cos θ / (1 + sin θ)) (uIcc 0 (π / 2)) := by
    intro θ hθ
    have hcos : 0 ≤ cos θ := by
      rw [uIcc_of_le hpi] at hθ
      exact cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
    have h1s : 0 < 1 + sin θ := by linarith [hsin θ hθ]
    simp only
    rw [legendreF_integrand_eq_inv_sqrt, one_pow, one_mul, ← cos_sq', sqrt_sq hcos,
      eq_div_iff h1s.ne']
    rcases hcos.eq_or_lt with h | h
    · rw [← h, inv_zero, mul_zero, zero_mul]
    · field_simp
      nlinarith [sin_sq_add_cos_sq θ]
  have hderiv : ∀ θ ∈ uIcc 0 (π / 2), HasDerivAt (fun θ ↦ log (1 + sin θ))
      (cos θ / (1 + sin θ)) θ := fun θ hθ ↦
    ((hasDerivAt_sin θ).const_add 1).log (by linarith [hsin θ hθ])
  have hcont : ContinuousOn (fun θ ↦ cos θ / (1 + sin θ)) (uIcc 0 (π / 2)) :=
    continuous_cos.continuousOn.div (by fun_prop) fun θ hθ ↦ by linarith [hsin θ hθ]
  rw [integral_congr heq, integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable,
    sin_pi_div_two, sin_zero, add_zero, log_one, sub_zero]
  norm_num

/-- **The regular part of `K` at modulus one**: as `k → 1⁻`,
`∫₀^{π/2} (1 - sin θ) (1 - k² sin² θ)^(-1/2) dθ → log 2`. -/
private theorem tendsto_integral_one_sub_sin_mul_rpow :
    Tendsto (fun k : ℝ ↦
      ∫ θ in (0 : ℝ)..π / 2, (1 - sin θ) * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ))
      (𝓝[<] 1) (𝓝 (log 2)) := by
  have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝[<] 1 := Ioo_mem_nhdsLT (by norm_num)
  have hpi : (0 : ℝ) ≤ π / 2 := by positivity
  rw [← integral_one_sub_sin_mul_rpow_one]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [hmem] with k hk
    exact ((continuous_const.sub continuous_sin).mul
      (continuous_legendreF_integrand (by nlinarith [hk.1, hk.2]))).aestronglyMeasurable
  · filter_upwards [hmem] with k hk
    refine ae_of_all _ fun θ hθ ↦ ?_
    rw [uIoc_of_le hpi] at hθ
    have hs0 : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos])
    have hk2 : k ^ 2 < 1 := by nlinarith [hk.1, hk.2]
    rw [norm_of_nonneg (mul_nonneg (by linarith [sin_le_one θ]) (rpow_nonneg
      (one_sub_mul_sin_sq_pos hk2 θ).le _))]
    exact one_sub_sin_mul_rpow_le_one hk2 hs0
  · refine ae_of_all _ fun θ hθ ↦ ?_
    rw [uIoc_of_le hpi] at hθ
    have hs0 : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos])
    -- Where `sin θ ^ 2 ≠ 1` the integrand is continuous in `k` at `k = 1`; where
    -- `sin θ ^ 2 = 1` on `(0, π / 2]`, the factor `1 - sin θ` vanishes.
    by_cases h : 1 - 1 ^ 2 * sin θ ^ 2 = 0
    · have hs : sin θ = 1 := le_antisymm (sin_le_one θ) (by nlinarith [sin_le_one θ])
      simp only [hs, sub_self, zero_mul]
      exact tendsto_const_nhds
    · have hc : ContinuousAt (fun k : ℝ ↦ (1 - sin θ) * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ))
          1 :=
        continuousAt_const.mul (ContinuousAt.rpow_const (f := fun k : ℝ ↦ 1 - k ^ 2 * sin θ ^ 2)
          (by fun_prop) (Or.inl h))
      exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-! ### The logarithmic singularity -/

/-- **The logarithmic singularity of `K` at modulus one** (DLMF 19.12.1): with `k' = √(1 - k²)`,
`K(k) - log (4 / k') → 0` as `k → 1⁻`. -/
theorem tendsto_legendreK_sub_log_nhdsLT_one :
    Tendsto (fun k ↦ legendreK k - log (4 / √(1 - k ^ 2))) (𝓝[<] 1) (𝓝 0) := by
  set A : ℝ → ℝ := fun k ↦
    ∫ θ in (0 : ℝ)..π / 2, (1 - sin θ) * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)
  -- `artanh k / k - log (4 / k')`, rewritten as a function continuous at `k = 1`.
  set g : ℝ → ℝ := fun k ↦ ((1 - k) * log (1 + k) + negMulLog (1 - k)) / (2 * k) +
    log ((1 + k) / 4)
  have hg : Tendsto g (𝓝[<] 1) (𝓝 (-log 2)) := by
    have hcont : ContinuousAt g 1 := by
      have : ContinuousAt (fun k : ℝ ↦ negMulLog (1 - k)) 1 :=
        continuous_negMulLog.continuousAt.comp (by fun_prop)
      exact (((continuousAt_const.sub continuousAt_id).mul
        ((continuousAt_const.add continuousAt_id).log (by norm_num))).add this).div
        (by fun_prop) (by norm_num) |>.add
        (((continuousAt_const.add continuousAt_id).div_const 4).log (by norm_num))
    convert hcont.tendsto.mono_left nhdsWithin_le_nhds using 2
    have h4 : (4 : ℝ) = 2 * 2 := by norm_num
    simp only [g, sub_self, zero_mul, negMulLog_zero, add_zero, zero_div, zero_add]
    rw [h4, ← one_add_one_eq_two, div_mul_cancel_left₀ (by norm_num), log_inv]
  have hsplit : ∀ k ∈ Ioo (0 : ℝ) 1, legendreK k - log (4 / √(1 - k ^ 2)) = A k + g k := by
    intro k ⟨hk0, hk1⟩
    have hk : k ^ 2 < 1 := by nlinarith
    have hK : legendreK k = A k + artanh k / k := by
      have hF := continuous_legendreF_integrand hk
      have h₁ : IntervalIntegrable
          (fun θ ↦ (1 - sin θ) * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) volume 0 (π / 2) :=
        ((continuous_const.sub continuous_sin).mul hF).intervalIntegrable _ _
      have h₂ : IntervalIntegrable
          (fun θ ↦ sin θ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) volume 0 (π / 2) :=
        (continuous_sin.mul hF).intervalIntegrable _ _
      simp only [A]
      rw [← integral_sin_mul_one_sub_sq_mul_sin_sq_rpow_neg_half hk0.ne' hk, legendreK_def,
        legendreF_def, ← integral_add h₁ h₂]
      exact integral_congr fun θ _ ↦ by ring
    have h1m : 0 < 1 - k := by linarith
    have h1p : 0 < 1 + k := by linarith
    simp only [g]
    rw [hK, artanh_eq_half_log ⟨by linarith, hk1.le⟩, log_div (by norm_num)
      (sqrt_pos.2 (by nlinarith)).ne', log_sqrt (by nlinarith),
      show 1 - k ^ 2 = (1 - k) * (1 + k) by ring, log_mul h1m.ne' h1p.ne',
      log_div h1p.ne' h1m.ne', log_div h1p.ne' (by norm_num)]
    simp only [negMulLog]
    field_simp
    ring
  have hlim := (tendsto_integral_one_sub_sin_mul_rpow.add hg)
  rw [add_neg_cancel] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT one_pos] with k hk
  exact (hsplit k hk).symm

/-- As `k → 1⁻`, `(1 - k²) K(k) → 0`. -/
theorem tendsto_one_sub_sq_mul_legendreK_nhdsLT_one :
    Tendsto (fun k ↦ (1 - k ^ 2) * legendreK k) (𝓝[<] 1) (𝓝 0) := by
  -- `(1 - k²) K = (1 - k²) (K - log (4 / k')) + (1 - k²) log 4 + negMulLog (1 - k²) / 2`.
  have hc : ContinuousAt (fun k : ℝ ↦ (1 - k ^ 2) * log 4 + negMulLog (1 - k ^ 2) / 2) 1 :=
    ((by fun_prop : ContinuousAt (fun k : ℝ ↦ (1 - k ^ 2) * log 4) 1).add
      ((continuous_negMulLog.continuousAt.comp (by fun_prop)).div_const 2))
  have hsq : Tendsto (fun k : ℝ ↦ 1 - k ^ 2) (𝓝[<] 1) (𝓝 0) := by
    have : ContinuousAt (fun k : ℝ ↦ 1 - k ^ 2) 1 := by fun_prop
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (hsq.mul tendsto_legendreK_sub_log_nhdsLT_one).add
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [one_pow, sub_self, zero_mul, negMulLog_zero, zero_div, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with k hk
  have h : 0 < 1 - k ^ 2 := by nlinarith [hk.1, hk.2]
  rw [log_div (by norm_num) (sqrt_pos.2 h).ne', log_sqrt h.le, negMulLog]
  ring

/-- As `k → 1`, `E(k) → E(1) = 1`. -/
theorem tendsto_legendreEc_one : Tendsto legendreEc (𝓝 1) (𝓝 1) := by
  simpa using continuous_legendreEc.tendsto 1

end TauCeti.Real
