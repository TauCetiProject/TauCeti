/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Topology.Order.ProjIcc
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric

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

On the open unit disc `‖z‖ < 1`, expanding `(1 - z * t) ^ (-a)` in its binomial series and
integrating term by term against `Complex.betaIntegral` identifies `eulerIntegral a b c z`
with `(Gamma c)⁻¹ * ₂F₁(a, b; c; z)` for all `a : ℂ` and `0 < b.re < c.re`
(`Complex.eulerIntegral_eq_inv_Gamma_mul_ordinaryHypergeometric`). Taking real parameters
gives the real integral formula `TauCeti.ordinaryHypergeometric_eq_integral`.

## References

* NIST Digital Library of Mathematical Functions, §15.6, equation 15.6.1.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set

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

section PowerSeries

open scoped Nat

private theorem eulerIntegral_term_eq (a : ℂ) {b c : ℂ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (z : ℂ) (n : ℕ) :
    (Gamma b * Gamma (c - b))⁻¹ *
      (∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (Ring.multichoose a n * (z * t) ^ n)) =
      (Gamma c)⁻¹ * (((n !⁻¹ : ℂ) * (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b *
        ((ascPochhammer ℂ n).eval c)⁻¹) * z ^ n) := by
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hc : 0 < c.re := hb.trans hbc
  have hcongr : ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (Ring.multichoose a n * (z * t) ^ n) =
      Ring.multichoose a n * z ^ n * betaIntegral (b + n) (c - b) := by
    rw [betaIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
    rw [uIoc_of_le zero_le_one] at ht
    have hexp : b + (n : ℂ) - 1 = (b - 1) + n := by ring
    rw [mul_pow, hexp, cpow_add _ _ (ofReal_ne_zero.mpr ht.1.ne'), cpow_natCast]; ring
  have hne {u : ℂ} (hu : 0 < u.re) (k : ℕ) : u ≠ -(k : ℂ) := fun h ↦ by
    have hr := congrArg re h; simp at hr; linarith [k.cast_nonneg (α := ℝ)]
  have hPc : (ascPochhammer ℂ n).eval c ≠ 0 := fun h0 ↦ by
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff n c).mp h0
    exact hne hc k (neg_eq_iff_eq_neg.mp hk.symm)
  have hmc : Ring.multichoose a n = (ascPochhammer ℂ n).eval a / n ! := by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
    rw [← h]; field_simp [Nat.cast_ne_zero.mpr n.factorial_ne_zero]
  have hGn {u : ℂ} (hu : 0 < u.re) : Gamma (u + n) = (ascPochhammer ℂ n).eval u * Gamma u := by
    rw [← Gamma_add_nat_div_Gamma_eq u (hne hu), div_mul_cancel₀ _ (Gamma_ne_zero_of_re_pos hu)]
  have hbn : 0 < (b + n).re := by simp [add_re]; linarith [n.cast_nonneg (α := ℝ)]
  have hadd : b + (n : ℂ) + (c - b) = c + n := by ring
  rw [hcongr, betaIntegral_eq_Gamma_mul_div (b + n) (c - b) hbn hcb, hadd, hGn hb, hGn hc, hmc]
  field_simp [Gamma_ne_zero_of_re_pos hb, Gamma_ne_zero_of_re_pos hcb, Gamma_ne_zero_of_re_pos hc,
    hPc, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- On the open unit disc, Euler's normalized integral equals `(Γ c)⁻¹ * ₂F₁(a, b; c; z)` for all
`a : ℂ` and `0 < b.re < c.re` (DLMF 15.6.1). -/
theorem eulerIntegral_eq_inv_Gamma_mul_ordinaryHypergeometric (a : ℂ) {b c z : ℂ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (hz : ‖z‖ < 1) :
    eulerIntegral a b c z = (Gamma c)⁻¹ * ₂F₁ a b c z := by
  let w : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)
  have hw_int : IntervalIntegrable w volume 0 1 :=
    betaIntegral_convergent hb (by simpa using sub_pos.mpr hbc)
  have hzb : z ∈ Metric.eball (0 : ℂ) 1 := by
    simpa only [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_one] using hz
  have hsum : Summable fun n : ℕ ↦ ‖Ring.multichoose a n‖ * ‖z‖ ^ n := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, norm_smul, ← Ring.multichoose_eq,
      mul_comm] using FormalMultilinearSeries.summable_norm_apply _
        (Metric.eball_subset_eball (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero a).r_le
          hzb)
  have hdct : HasSum (fun n ↦ ∫ t : ℝ in 0..1, w t * (Ring.multichoose a n * (z * t) ^ n))
      (∫ t : ℝ in 0..1, w t * (1 - z * t) ^ (-a)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n t ↦ ‖w t‖ * (‖Ring.multichoose a n‖ * ‖z‖ ^ n))
      (fun _ ↦ by rw [uIoc_of_le zero_le_one]
                  exact (hw_int.mul_continuousOn (by fun_prop)).1.aestronglyMeasurable)
      (fun n ↦ Eventually.of_forall fun t ht ↦ ?_) (Eventually.of_forall fun t _ ↦ hsum.mul_left _)
      ((hw_int.norm.mul_const (∑' n : ℕ, ‖Ring.multichoose a n‖ * ‖z‖ ^ n)).congr
        fun _ _ ↦ by rw [tsum_mul_left]) (Eventually.of_forall fun t ht ↦ ?_)
    · rw [uIoc_of_le zero_le_one] at ht
      have ht_le : ‖(t : ℂ)‖ ≤ 1 := by rw [norm_real, Real.norm_of_nonneg ht.1.le]; exact ht.2
      rw [norm_mul (w t), norm_mul (Ring.multichoose a n), norm_pow, norm_mul z]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (mul_le_of_le_one_right (norm_nonneg z) ht_le) n) (norm_nonneg _)) (norm_nonneg _)
    · rw [uIoc_of_le zero_le_one] at ht
      have hzt : ‖z * (t : ℂ)‖ < 1 := by
        rw [norm_mul, norm_real, Real.norm_of_nonneg ht.1.le]
        exact (mul_le_of_le_one_right (norm_nonneg z) ht.2).trans_lt hz
      simpa [one_div, ← cpow_neg] using
        (TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one (r := a) hzt).mul_left _
  have key := (hdct.mul_left (Gamma b * Gamma (c - b))⁻¹).congr_fun fun n ↦
    (eulerIntegral_term_eq a hb hbc z n).symm
  rw [eulerIntegral_def, ← key.tsum_eq, tsum_mul_left]
  exact congrArg _ (by simpa [ordinaryHypergeometric] using
    (ordinaryHypergeometric_sum_eq a b c z).symm)

end PowerSeries

end Complex

namespace TauCeti

/-- Euler's integral representation for the real Gauss hypergeometric function `₂F₁` (DLMF 15.6.1):
for every `a : ℝ`, `0 < b < c`, and `|z| < 1`,
`₂F₁(a, b; c; z) = Γ(c) / (Γ(b) Γ(c - b)) * ∫ t in 0..1, t^(b-1) (1-t)^(c-b-1) (1 - z t)^(-a)`. -/
theorem ordinaryHypergeometric_eq_integral {a b c z : ℝ}
    (hb : 0 < b) (hbc : b < c) (hz : |z| < 1) :
    ₂F₁ a b c z =
      Real.Gamma c / (Real.Gamma b * Real.Gamma (c - b)) *
        ∫ t in (0 : ℝ)..1, t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - z * t) ^ (-a) := by
  apply Complex.ofReal_injective
  have heul := Complex.eulerIntegral_eq_inv_Gamma_mul_ordinaryHypergeometric (a : ℂ)
    (b := (b : ℂ)) (c := (c : ℂ)) (z := (z : ℂ))
    (by simpa using hb) (by simpa using hbc) (by simpa [Real.norm_eq_abs] using hz)
  have hint : Complex.ofReal (∫ t in (0 : ℝ)..1,
        t ^ (b - 1) * (1 - t) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      ∫ t : ℝ in 0..1, (t : ℂ) ^ ((b : ℂ) - 1) * (1 - (t : ℂ)) ^ ((c : ℂ) - b - 1) *
        (1 - (z : ℂ) * t) ^ (-(a : ℂ)) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le zero_le_one] at ht
    push_cast
    rw [Complex.ofReal_cpow ht.1, Complex.ofReal_cpow (sub_nonneg.mpr ht.2),
      Complex.ofReal_cpow (by nlinarith [(abs_lt.mp hz).1, (abs_lt.mp hz).2, ht.1, ht.2])]
    push_cast; rfl
  rw [ofReal_ordinaryHypergeometric, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul,
    ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, Complex.ofReal_sub,
    hint, div_eq_mul_inv, mul_assoc, ← Complex.eulerIntegral_def, heul,
    mul_inv_cancel_left₀ (Complex.Gamma_ne_zero_of_re_pos (by simpa using hb.trans hbc))]

end TauCeti
