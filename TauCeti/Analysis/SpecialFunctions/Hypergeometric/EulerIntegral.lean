/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Topology.Order.ProjIcc
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import TauCeti.Analysis.Complex.SlitPlane

/-!
# Euler's integral for the regularized Gauss function

`Complex.eulerIntegral a b c z` is the normalized Euler integral with principal complex
powers (DLMF 15.6.1). It converges when `0 < b.re < c.re` and `1 - z ∈ Complex.slitPlane`.
For fixed `b`, `c` in that range it is jointly holomorphic in `(a, z)` on the cut plane.
The normalization gives the value `1 / Γ(c)` at `z = 0` and when `a = 0`.

The integral is defined at all parameters, but no analytic continuation in `b` or `c` is
implicit in this definition. In particular, its values outside the convergence region
must not be interpreted as the continued regularized Gauss function.

The integrability proof uses the Beta weight and the continuity of the remaining factor
on the closed interval. Analytic dependence uses the compact-parameter integral theorem
`TauCeti.analyticAt_integral_smul`.

## References

* NIST Digital Library of Mathematical Functions, §15.6, equation 15.6.1,
  <https://dlmf.nist.gov/15.6.E1>.
-/

public section

noncomputable section

open Set MeasureTheory

namespace Complex

/-- Euler's normalized integral for the regularized Gauss hypergeometric function.
Its convergence region is `0 < b.re < c.re` and `1 - z ∈ slitPlane`; outside that region
this definition is not an analytic continuation. All powers are principal complex powers. -/
def eulerIntegral (a b c z : ℂ) : ℂ :=
  (Gamma b * Gamma (c - b))⁻¹ *
    ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
      (1 - z * (t : ℂ)) ^ (-a)

/-- The integrand in Euler's representation is integrable throughout its classical
convergence region, including arguments outside the unit disk. -/
theorem intervalIntegrable_eulerIntegral {a b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hz : 1 - z ∈ slitPlane) :
    IntervalIntegrable (fun t : ℝ =>
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * (t : ℂ)) ^ (-a)) volume 0 1 := by
  refine (betaIntegral_convergent hb (sub_pos.mpr hbc)).mul_continuousOn ?_
  rw [uIcc_of_le zero_le_one]
  intro t ht
  exact ((continuousAt_const.sub (continuousAt_const.mul continuous_ofReal.continuousAt)).cpow
    continuousAt_const (one_sub_mul_ofReal_mem_slitPlane hz ht)).continuousWithinAt

/-- For fixed `b` and `c` in the convergence region, the unnormalized Euler integral is
jointly holomorphic in its first parameter and its argument. -/
theorem analyticOnNhd_integral_eulerIntegral_a_z {b c : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ =>
      ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - p.2 * (t : ℂ)) ^ (-p.1)) {p | 1 - p.2 ∈ slitPlane} := by
  intro p hp
  -- Clamp the real integration variable to the compact interval. This does not change
  -- the integral and lets the compact-parameter theorem apply on the whole source space.
  let φ : ℝ → ℂ := fun t => ((projIcc 0 1 zero_le_one t : ℝ) : ℂ)
  let K : Set ℂ := ofReal '' Icc (0 : ℝ) 1
  have hφ : Continuous φ := continuous_ofReal.comp
    (continuous_subtype_val.comp continuous_projIcc)
  have hφK (t : ℝ) : φ t ∈ K :=
    ⟨_, (projIcc 0 1 zero_le_one t).property, rfl⟩
  have hkernel : ∀ y ∈ K, AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × ℂ => (1 - q.1.2 * q.2) ^ (-q.1.1)) (p, y) := by
    rintro y ⟨t, ht, rfl⟩
    apply AnalyticAt.cpow
    · exact analyticAt_const.sub ((analyticAt_snd.comp analyticAt_fst).mul analyticAt_snd)
    · exact (analyticAt_fst.comp analyticAt_fst).neg
    · exact one_sub_mul_ofReal_mem_slitPlane hp ht
  have hweight := (betaIntegral_convergent (v := c - b) hb (sub_pos.mpr hbc)).1
  have h := TauCeti.analyticAt_integral_smul
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (g := fun t : ℝ => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1))
    (isCompact_Icc.image continuous_ofReal) hφ hφK hkernel hweight
  convert h using 1
  ext q
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simp only [smul_eq_mul, φ, projIcc_of_mem zero_le_one (Ioc_subset_Icc_self ht)]

/-- Euler's normalized integral is jointly holomorphic in `(a, z)` for fixed
`0 < b.re < c.re`, on the principal cut plane in `z`. -/
theorem analyticOnNhd_eulerIntegral_a_z {b c : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => eulerIntegral p.1 b c p.2)
      {p | 1 - p.2 ∈ slitPlane} := by
  exact analyticOnNhd_const.mul (analyticOnNhd_integral_eulerIntegral_a_z hb hbc)

/-- At zero argument Euler's normalization is the reciprocal Gamma factor. -/
@[simp]
theorem eulerIntegral_zero {a b c : ℂ} (hb : 0 < b.re) (hbc : b.re < c.re) :
    eulerIntegral a b c 0 = (Gamma c)⁻¹ := by
  have hG : Gamma b * Gamma (c - b) ≠ 0 :=
    mul_ne_zero (Gamma_ne_zero_of_re_pos hb) (Gamma_ne_zero_of_re_pos (sub_pos.mpr hbc))
  have hbeta := betaIntegral_eq_Gamma_mul_div b (c - b) hb (sub_pos.mpr hbc)
  rw [add_sub_cancel] at hbeta
  simp only [eulerIntegral, zero_mul, sub_zero, one_cpow, mul_one]
  rw [← betaIntegral, hbeta, div_eq_mul_inv, inv_mul_cancel_left₀ hG]

/-- When the first parameter vanishes, Euler's integral is constant in its argument. -/
@[simp]
theorem eulerIntegral_zero_left {b c : ℂ} (hb : 0 < b.re) (hbc : b.re < c.re) (z : ℂ) :
    eulerIntegral 0 b c z = (Gamma c)⁻¹ := by
  rw [eulerIntegral, neg_zero]
  simp only [cpow_zero, mul_one]
  simpa only [eulerIntegral, zero_mul, sub_zero, one_cpow, mul_one] using
    (eulerIntegral_zero (a := 0) hb hbc)

end Complex
