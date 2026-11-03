/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Analysis.SpecialFunctions.Artanh
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Elementary evaluations of Legendre's elliptic integrals

At the degenerate moduli and for special characteristics, Legendre's elliptic integrals reduce to
elementary functions. This file proves those reductions.

* **Modulus one.** For `|φ| < π / 2`, `F(φ, 1) = artanh (sin φ)`, and for `|φ| ≤ π / 2`,
  `E(φ, 1) = sin φ`; hence `E(1) = 1`. The complete integral of the first kind has no finite value
  at `k = 1`: `K(k) → +∞` as `k → 1⁻`.
* **Third kind** (DLMF 19.6.11, 19.6.13). For `α2 < 1` and `|φ| < π / 2`,
  `Π(φ, 0, α²) = arctan (√(1 - α²) tan φ) / √(1 - α²)`, hence `Π(0, α²) = π / (2 √(1 - α²))`;
  and for `k ^ 2 < 1`,
  `Π(φ, k, k²) = (E(φ, k) - k² sin φ cos φ / √(1 - k² sin² φ)) / (1 - k²)`.

The evaluations at `k = 0` of the first two kinds, and `Π(φ, k, 0) = F(φ, k)`, live next to the
definitions, in `TauCeti/Analysis/SpecialFunctions/EllipticIntegral/Legendre.lean`.

## Main statements

* `TauCeti.Real.legendreF_one_modulus`, `TauCeti.Real.legendreE_one_modulus` and
  `TauCeti.Real.legendreEc_one`: the integrals at modulus `1`.
* `TauCeti.Real.tendsto_legendreK_nhdsLT_one`: `K(k) → +∞` as `k → 1⁻`.
* `TauCeti.Real.legendrePi_zero_modulus`, `TauCeti.Real.legendrePic_zero_modulus` and
  `TauCeti.Real.legendrePi_modulus_sq`: the elementary reductions of the third kind.

## References

* NIST *Digital Library of Mathematical Functions*, §19.6, <https://dlmf.nist.gov/19.6>.
-/

public section

namespace TauCeti.Real

open _root_.Real Filter intervalIntegral Set
open scoped Topology

/-! ### Modulus one -/

/-- **The integral of the first kind at modulus one**: for `|φ| < π / 2`,
`F(φ, 1) = ∫₀^φ sec θ dθ = artanh (sin φ)`. -/
@[simp]
theorem legendreF_one_modulus {φ : ℝ} (hφ : |φ| < π / 2) :
    legendreF φ 1 = artanh (sin φ) := by
  have hsub : uIcc 0 φ ⊆ Ioo (-(π / 2)) (π / 2) :=
    ordConnected_Ioo.uIcc_subset (by simp [pi_pos]) (abs_lt.1 hφ)
  -- On `(-π / 2, π / 2)` the integrand `(1 - sin² θ)^(-1/2)` is `sec θ`, the derivative of
  -- `artanh (sin θ)`.
  have hderiv : ∀ θ ∈ uIcc 0 φ, HasDerivAt (fun θ ↦ artanh (sin θ))
      ((1 - 1 ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) θ := by
    intro θ hθ
    have hcos := cos_pos_of_mem_Ioo (hsub hθ)
    have hsin : sin θ ∈ Ioo (-1 : ℝ) 1 := by
      rw [mem_Ioo, ← abs_lt, ← sq_lt_one_iff_abs_lt_one]
      nlinarith [sin_sq_add_cos_sq θ]
    refine ((hasDerivAt_sin θ).artanh hsin).congr_deriv ?_
    rw [legendreF_integrand_eq_inv_sqrt, one_pow, one_mul, ← cos_sq', sqrt_sq hcos.le]
    field_simp
  have hcont : ContinuousOn (fun θ ↦ (1 - 1 ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) (uIcc 0 φ) := by
    refine ContinuousOn.rpow_const (f := fun θ ↦ 1 - 1 ^ 2 * sin θ ^ 2) (by fun_prop)
      fun θ hθ ↦ Or.inl ?_
    rw [one_pow, one_mul, ← cos_sq']
    exact (pow_pos (cos_pos_of_mem_Ioo (hsub hθ)) 2).ne'
  rw [legendreF_def, integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable, sin_zero,
    artanh_zero, sub_zero]

/-- **The integral of the second kind at modulus one**: for `|φ| ≤ π / 2`,
`E(φ, 1) = ∫₀^φ cos θ dθ = sin φ`. -/
@[simp]
theorem legendreE_one_modulus {φ : ℝ} (hφ : |φ| ≤ π / 2) : legendreE φ 1 = sin φ := by
  have hsub : uIcc 0 φ ⊆ Icc (-(π / 2)) (π / 2) :=
    uIcc_subset_Icc ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ (abs_le.1 hφ)
  have hderiv : ∀ θ ∈ uIcc 0 φ, HasDerivAt sin ((1 - 1 ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ)) θ := by
    intro θ hθ
    refine (hasDerivAt_sin θ).congr_deriv ?_
    rw [one_pow, one_mul, ← cos_sq', ← sqrt_eq_rpow, sqrt_sq (cos_nonneg_of_mem_Icc (hsub hθ))]
  rw [legendreE_def, integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_legendreE_integrand 1 0 φ), sin_zero, sub_zero]

/-- The complete integral of the second kind at modulus one: `E(1) = 1`. -/
@[simp]
theorem legendreEc_one : legendreEc 1 = 1 := by
  rw [legendreEc_def, legendreE_one_modulus (by rw [abs_of_pos (by positivity)]), sin_pi_div_two]

/-- A lower bound for `K(k)` which blows up as `k → 1⁻`: with `k' = √(1 - k²)`,
`log ((π / 2 + k') / k') ≤ K(k)`. -/
private theorem log_le_legendreK {k : ℝ} (hk : k ^ 2 < 1) :
    log ((π / 2 + √(1 - k ^ 2)) / √(1 - k ^ 2)) ≤ legendreK k := by
  set k' := √(1 - k ^ 2)
  have hk' : 0 < k' := sqrt_pos.2 (by linarith)
  have hk'sq : k' ^ 2 = 1 - k ^ 2 := sq_sqrt (by linarith)
  -- On `[0, π / 2]` the integrand is at least `(π / 2 + k' - θ)⁻¹`, because
  -- `1 - k² sin² θ ≤ cos² θ + k'² ≤ (cos θ + k')²` and `cos θ ≤ π / 2 - θ`.
  have hle : ∀ θ ∈ Icc 0 (π / 2),
      (π / 2 + k' - θ)⁻¹ ≤ (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ) := by
    rintro θ ⟨h0, h1⟩
    have hcos : cos θ ≤ π / 2 - θ := by
      rw [← sin_pi_div_two_sub]
      exact sin_le (by linarith)
    have hcos0 : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], h1⟩
    have hΔ := one_sub_mul_sin_sq_pos hk θ
    rw [legendreF_integrand_eq_inv_sqrt]
    refine inv_anti₀ (sqrt_pos.2 hΔ) (sqrt_le_iff.2 ⟨by linarith, ?_⟩)
    nlinarith [sin_sq_add_cos_sq θ, sin_sq_le_one θ, mul_nonneg hcos0 hk'.le]
  have hcont : ContinuousOn (fun θ ↦ (π / 2 + k' - θ)⁻¹) (uIcc 0 (π / 2)) := by
    rw [uIcc_of_le (by positivity)]
    exact ContinuousOn.inv₀ (f := fun θ ↦ π / 2 + k' - θ) (by fun_prop) fun θ hθ ↦ by
      linarith [hθ.2]
  have hint : ∫ θ in (0 : ℝ)..π / 2, (π / 2 + k' - θ)⁻¹ = log ((π / 2 + k') / k') := by
    rw [integral_comp_sub_left (fun x ↦ x⁻¹), add_sub_cancel_left, sub_zero,
      integral_inv_of_pos hk' (by positivity)]
  rw [← hint, legendreK_def, legendreF_def]
  exact integral_mono_on (by positivity) hcont.intervalIntegrable
    (intervalIntegrable_legendreF_integrand hk _ _) hle

/-- **Divergence of `K` at modulus one**: the complete integral of the first kind tends to `+∞`
as the modulus tends to `1` from below. -/
theorem tendsto_legendreK_nhdsLT_one : Tendsto legendreK (𝓝[<] 1) atTop := by
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[<] 1 := Ioo_mem_nhdsLT one_pos
  have hk' : Tendsto (fun k : ℝ ↦ √(1 - k ^ 2)) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun k : ℝ ↦ √(1 - k ^ 2)) (𝓝 1) (𝓝 √(1 - 1 ^ 2)) :=
        (by fun_prop : Continuous fun k : ℝ ↦ √(1 - k ^ 2)).tendsto 1
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [hmem] with k hk
      exact sqrt_pos.2 (by nlinarith [hk.1, hk.2])
  have hlog : Tendsto (fun k : ℝ ↦ log ((π / 2 + √(1 - k ^ 2)) / √(1 - k ^ 2))) (𝓝[<] 1)
      atTop := by
    refine tendsto_log_atTop.comp (tendsto_atTop_mono' _ ?_
      ((tendsto_inv_nhdsGT_zero.comp hk').const_mul_atTop (by positivity : (0 : ℝ) < π / 2)))
    filter_upwards [hk'.eventually self_mem_nhdsWithin] with k hk
    simp only [Function.comp_apply]
    rw [add_div, div_self hk.ne', ← div_eq_mul_inv]
    linarith
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [hmem] with k hk
  exact log_le_legendreK (by nlinarith [hk.1, hk.2])

/-! ### Elementary reductions of the third kind -/

/-- **The integral of the third kind at modulus zero** (DLMF 19.6.11): for `α2 < 1` and
`|φ| < π / 2`, `Π(φ, 0, α²) = arctan (√(1 - α²) tan φ) / √(1 - α²)`. -/
theorem legendrePi_zero_modulus {φ α2 : ℝ} (hα : α2 < 1) (hφ : |φ| < π / 2) :
    legendrePi φ 0 α2 = arctan (√(1 - α2) * tan φ) / √(1 - α2) := by
  set c := √(1 - α2)
  have hc : 0 < c := sqrt_pos.2 (by linarith)
  have hc2 : c ^ 2 = 1 - α2 := sq_sqrt (by linarith)
  have hsub : uIcc 0 φ ⊆ Ioo (-(π / 2)) (π / 2) :=
    ordConnected_Ioo.uIcc_subset (by simp [pi_pos]) (abs_lt.1 hφ)
  -- On `(-π / 2, π / 2)`, `arctan (c tan θ) / c` has derivative
  -- `1 / (cos² θ + c² sin² θ) = (1 - α² sin² θ)⁻¹`.
  have hderiv : ∀ θ ∈ uIcc 0 φ, HasDerivAt (fun θ ↦ arctan (c * tan θ) / c)
      ((1 - α2 * sin θ ^ 2)⁻¹ * (1 - 0 ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) θ := by
    intro θ hθ
    have hcos := cos_pos_of_mem_Ioo (hsub hθ)
    refine ((((hasDerivAt_tan hcos.ne').const_mul c).arctan).div_const c).congr_deriv ?_
    have hΔ : 1 - α2 * sin θ ^ 2 = cos θ ^ 2 + c ^ 2 * sin θ ^ 2 := by
      rw [hc2, cos_sq']
      ring
    rw [tan_eq_sin_div_cos, hΔ]
    rw [zero_pow two_ne_zero, zero_mul, sub_zero, one_rpow, mul_one]
    field_simp
  rw [legendrePi_def, integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_legendrePi_integrand (by norm_num) hα 0 φ)]
  simp

/-- The complete integral of the third kind at modulus zero: `Π(0, α²) = π / (2 √(1 - α²))` for
`α2 < 1`. -/
theorem legendrePic_zero_modulus {α2 : ℝ} (hα : α2 < 1) :
    legendrePic 0 α2 = π / (2 * √(1 - α2)) := by
  set c := √(1 - α2)
  have hc : 0 < c := sqrt_pos.2 (by linarith)
  -- As `φ → π / 2⁻`, `Π(φ, 0, α²) → Π(0, α²)` by continuity, while `c tan φ → +∞`, so
  -- `arctan (c tan φ) / c → π / (2 c)`.
  have hPi : Tendsto (legendrePi · 0 α2) (𝓝[<] (π / 2)) (𝓝 (legendrePi (π / 2) 0 α2)) :=
    ((continuous_legendrePi (k := 0) (by norm_num) hα).tendsto _).mono_left nhdsWithin_le_nhds
  have harctan : Tendsto (fun φ ↦ arctan (c * tan φ) / c) (𝓝[<] (π / 2)) (𝓝 (π / 2 / c)) :=
    ((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_tan_pi_div_two.const_mul_atTop hc)).div_const c
  rw [legendrePic_def, ← div_div]
  refine tendsto_nhds_unique hPi (harctan.congr' ?_)
  filter_upwards [Ioo_mem_nhdsLT (by linarith [pi_pos] : -(π / 2) < π / 2)] with φ hφ
  exact (legendrePi_zero_modulus hα (abs_lt.2 hφ)).symm

/-- **The integral of the third kind at characteristic `k²`** (DLMF 19.6.13): for `k ^ 2 < 1`,
`Π(φ, k, k²) = (E(φ, k) - k² sin φ cos φ / √(1 - k² sin² φ)) / (1 - k²)`. -/
theorem legendrePi_modulus_sq {k : ℝ} (hk : k ^ 2 < 1) (φ : ℝ) :
    legendrePi φ k (k ^ 2) =
      (legendreE φ k - k ^ 2 * sin φ * cos φ / √(1 - k ^ 2 * sin φ ^ 2)) / (1 - k ^ 2) := by
  have hderiv : ∀ θ ∈ uIcc 0 φ, HasDerivAt
      (fun θ ↦ (legendreE θ k - k ^ 2 * sin θ * cos θ / √(1 - k ^ 2 * sin θ ^ 2)) / (1 - k ^ 2))
      ((1 - k ^ 2 * sin θ ^ 2)⁻¹ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) θ := by
    intro θ _
    have hΔ := one_sub_mul_sin_sq_pos hk θ
    have hr := sqrt_pos.2 hΔ
    have hr2 : √(1 - k ^ 2 * sin θ ^ 2) ^ 2 = 1 - k ^ 2 * sin θ ^ 2 := sq_sqrt hΔ.le
    have hD : HasDerivAt (fun θ ↦ 1 - k ^ 2 * sin θ ^ 2)
        (-(k ^ 2 * (2 * sin θ * cos θ))) θ := by
      simpa using (((hasDerivAt_sin θ).pow 2).const_mul (k ^ 2)).const_sub 1
    have hN : HasDerivAt (fun θ ↦ k ^ 2 * sin θ * cos θ)
        (k ^ 2 * cos θ * cos θ + k ^ 2 * sin θ * -sin θ) θ :=
      ((hasDerivAt_sin θ).const_mul (k ^ 2)).mul (hasDerivAt_cos θ)
    refine (((hasDerivAt_legendreE k θ).sub (hN.div (hD.sqrt hΔ.ne') hr.ne')).div_const
      _).congr_deriv ?_
    rw [← sqrt_eq_rpow, legendreF_integrand_eq_inv_sqrt]
    have h1k : 1 - k ^ 2 ≠ 0 := by linarith
    field_simp
    grind [sin_sq_add_cos_sq]
  rw [legendrePi_def, integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_legendrePi_integrand hk (by linarith) 0 φ)]
  simp

/-- `Π(k, k²) = E(k) / (1 - k²)` for `k ^ 2 < 1`. -/
theorem legendrePic_modulus_sq {k : ℝ} (hk : k ^ 2 < 1) :
    legendrePic k (k ^ 2) = legendreEc k / (1 - k ^ 2) := by
  simp [legendrePic_def, legendrePi_modulus_sq hk, legendreEc_def]

end TauCeti.Real
