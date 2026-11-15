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
# Euler's integral for the Gauss hypergeometric function

Euler's integral (DLMF 15.6.1), normalized by `Γ(b) Γ(c - b)`, represents the
regularized Gauss function when `0 < re b < re c`. We define this integral using
principal complex powers and prove convergence for every `z` in the cut plane
`{z | 1 - z ∈ Complex.slitPlane}`. The endpoint singularities are those of the
Beta integral; the remaining power is continuous on the closed integration interval.
For fixed `b`, `c` in that range the integral is jointly holomorphic in `(a, z)` on
this cut plane, by the compact-parameter theorem `TauCeti.analyticAt_integral_smul`.

The integral is defined at all parameters, but no representation of the Gauss
function is asserted outside the convergence region. In particular, its normalized
value can vanish when a Gamma factor has a pole.

## References

* NIST Digital Library of Mathematical Functions, §15.6, equation 15.6.1.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Complex

/-- Euler's integral, normalized to represent the regularized Gauss function in
its convergence region `0 < b.re < c.re`, with `1 - z ∈ Complex.slitPlane`.
Outside that region this is only the totalized integral, not an analytic continuation. -/
def eulerIntegral (a b c z : ℂ) : ℂ :=
  (Gamma b * Gamma (c - b))⁻¹ *
    ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
      (1 - z * t) ^ (-a)

/-- The defining normalized integral representation of `eulerIntegral`, at all parameters. -/
theorem eulerIntegral_def (a b c z : ℂ) :
    eulerIntegral a b c z =
      (Gamma b * Gamma (c - b))⁻¹ *
        ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (1 - z * t) ^ (-a) := (rfl)

/-- The Euler kernel has no branch-cut crossing on the closed integration interval. -/
theorem continuousOn_eulerKernel (a : ℂ) {z : ℂ} (hz : 1 - z ∈ slitPlane) :
    ContinuousOn (fun t : ℝ => (1 - z * t) ^ (-a)) (Icc 0 1) := by
  refine continuousOn_of_forall_continuousAt fun t ht => ?_
  apply ContinuousAt.cpow (by fun_prop) (by fun_prop)
  exact one_sub_mul_ofReal_mem_slitPlane hz ht

/-- Euler's integrand is interval integrable throughout its classical parameter
region, for every argument off the cut `[1, ∞)`. -/
theorem intervalIntegrable_eulerIntegrand (a : ℂ) {b c z : ℂ}
    (hb : 0 < b.re) (hcb : b.re < c.re) (hz : 1 - z ∈ slitPlane) :
    IntervalIntegrable (fun t : ℝ =>
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a))
      volume 0 1 := by
  exact (betaIntegral_convergent hb (by simpa using sub_pos.mpr hcb)).mul_continuousOn
    (by simpa only [uIcc_of_le zero_le_one] using continuousOn_eulerKernel a hz)

/-- For fixed `b` and `c` in the convergence region, the unnormalized Euler integral is
jointly holomorphic in its first parameter and its argument, away from the cut `[1, ∞)`. -/
private theorem analyticOnNhd_integral_eulerIntegrand {b c : ℂ} (hb : 0 < b.re)
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
  have hweight := ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (betaIntegral_convergent (v := c - b) hb (by simpa using sub_pos.mpr hbc))).integrable
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
theorem analyticOnNhd_eulerIntegral {b c : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => eulerIntegral p.1 b c p.2)
      {p | 1 - p.2 ∈ slitPlane} := by
  exact analyticOnNhd_const.mul (analyticOnNhd_integral_eulerIntegrand hb hbc)

/-- With first parameter zero the normalized Euler integral is constant, even when
its argument lies on the cut. This statement does not identify a continued function there. -/
@[simp]
theorem eulerIntegral_zero_left {b c : ℂ} (hb : 0 < b.re) (hcb : b.re < c.re) (z : ℂ) :
    eulerIntegral 0 b c z = (Gamma c)⁻¹ := by
  have hcb' : 0 < (c - b).re := by simpa using sub_pos.mpr hcb
  simp only [eulerIntegral_def, neg_zero, cpow_zero, mul_one]
  rw [← betaIntegral, betaIntegral_eq_Gamma_mul_div b (c - b) hb hcb', add_sub_cancel]
  field_simp [Gamma_ne_zero_of_re_pos hb, Gamma_ne_zero_of_re_pos hcb']

/-- At zero argument the normalized Euler integral is the reciprocal Gamma factor. -/
@[simp]
theorem eulerIntegral_zero (a : ℂ) {b c : ℂ} (hb : 0 < b.re) (hcb : b.re < c.re) :
    eulerIntegral a b c 0 = (Gamma c)⁻¹ := by
  simpa [eulerIntegral_def] using eulerIntegral_zero_left hb hcb 0

end Complex
