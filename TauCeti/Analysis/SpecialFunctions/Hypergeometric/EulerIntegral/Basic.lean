/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Topology.Order.ProjIcc
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import TauCeti.Analysis.Complex.SlitPlane
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.SpecialFunctions.Integrability.Cpow
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Euler's integral for the Gauss hypergeometric function

Euler's integral (DLMF 15.6.1), normalized by `Γ(b) Γ(c - b)`, represents the
regularized Gauss function when `0 < re b < re c`. We define this integral using
principal complex powers and prove convergence for every `z` in the cut plane
`{z | 1 - z ∈ Complex.slitPlane}`. The endpoint singularities are those of the
Beta integral; the remaining power is continuous on the closed integration interval.
For fixed `b`, `c` in that range the integral is jointly holomorphic in `(a, z)` on
this cut plane, by the compact-parameter theorem `TauCeti.analyticAt_integral_smul`.

On the open unit disk `‖z‖ < 1`, expanding `(1 - z t) ^ (-a)` in its binomial series and
integrating term by term against the Beta weight identifies `Complex.regularizedGaussHGFun a b c z`
with `Complex.eulerIntegral a b c z` throughout `0 < b.re < c.re`; for `a = -n` both sides are
polynomials in `z`, so the identity holds at every `z`. When `(a + b).re < c.re` as
well, dominated convergence extends `eulerIntegral a b c` continuously to the closed unit disk and
evaluates it at `z = 1` via Euler's Beta integral; contiguous parameter shifts then remove
`0 < b.re < c.re`, yielding Gauss's summation theorem (DLMF 15.4.20) as a boundary limit along
`Metric.ball 0 1` whenever `(a + b).re < c.re`.

The integral is defined at all parameters, but no representation of the Gauss
function is asserted outside the convergence region. In particular, its normalized
value can vanish when a Gamma factor has a pole.

## Main results

* `Complex.eulerIntegral` — Euler's normalized integral representation.
* `Complex.analyticOnNhd_eulerIntegral` — joint holomorphy in `(a, z)` on
  `{p | 1 - p.2 ∈ slitPlane}` when `0 < b.re < c.re`.
* `Complex.regularizedGaussHGFun_eq_eulerIntegral` — `𝐅(a, b; c; z) = eulerIntegral a b c z` on
  `‖z‖ < 1` when `0 < b.re < c.re` (DLMF 15.6.1).
* `Complex.regularizedGaussHGFun_neg_natCast_eq_eulerIntegral` — the same for the terminating
  `𝐅(-n, b; c; z)` at every `z`, both sides being polynomials in `z`.
* `Complex.eulerIntegral_one` — `eulerIntegral a b c 1 = Γ(c - a - b) / (Γ(c - a) Γ(c - b))` when
  `0 < b.re` and `(a + b).re < c.re`.
* `Complex.continuousOn_eulerIntegral_closedBall` — continuity of `eulerIntegral a b c` on
  `Metric.closedBall 0 1` when `0 < b.re < c.re` and `(a + b).re < c.re`.
* `Complex.tendsto_regularizedGaussHGFun_nhdsWithin_ball_one` — Gauss's summation formula (DLMF
  15.4.20) as the limit of `regularizedGaussHGFun a b c` at `1` within `Metric.ball 0 1` when
  `(a + b).re < c.re`.

## References

* NIST Digital Library of Mathematical Functions, §15.4 (equation 15.4.20) and §15.6 (equation
  15.6.1).
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

/-- On the cut plane, restricting the Euler integrand to `[ρ, 1]` with `ρ > 0` removes the
condition `0 < b.re`; only `b.re < c.re` is needed for the endpoint at one. -/
theorem intervalIntegrable_eulerIntegrand_right (a : ℂ) {b c z : ℂ} (hbc : b.re < c.re)
    (hz : 1 - z ∈ slitPlane) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    IntervalIntegrable (fun t : ℝ =>
      (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a))
      volume ρ 1 := by
  have hsub : uIcc ρ 1 ⊆ Icc 0 1 := by
    rw [uIcc_of_le hρ1]
    exact Icc_subset_Icc_left hρ.le
  apply TauCeti.intervalIntegrable_ofReal_cpow_mul_one_sub_cpow_mul hρ
  · simp only [sub_re, one_re]
    linarith
  · exact (continuousOn_eulerKernel a hz).mono hsub

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
    (continuous_subtypeVal.comp continuous_projIcc)
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

private theorem inv_Gamma_mul_integral_multichoose_mul_pow (a : ℂ) {b c : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (z : ℂ) (n : ℕ) :
    (Gamma b * Gamma (c - b))⁻¹ *
        (∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (Ring.multichoose a n * (z * (t : ℂ)) ^ n)) =
      (regularizedGaussHGFunSeries a b c).coeff n * z ^ n := by
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hint :
      (∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (Ring.multichoose a n * (z * (t : ℂ)) ^ n)) =
        Ring.multichoose a n * z ^ n * betaIntegral (b + n) (c - b) := by
    rw [betaIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le zero_le_one] at ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have hpow : (t : ℂ) ^ (b - 1) * (t : ℂ) ^ n = (t : ℂ) ^ (b + n - 1) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0, sub_add_eq_add_sub]
    rw [mul_pow]
    linear_combination Ring.multichoose a n * z ^ n * (1 - (t : ℂ)) ^ (c - b - 1) * hpow
  have hmc : Ring.multichoose a n = (ascPochhammer ℂ n).eval a / n.factorial := by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
    have hfac : (n.factorial : ℂ) ≠ 0 := mod_cast Nat.factorial_ne_zero n
    rw [← h, mul_div_cancel_left₀ _ hfac]
  have hbn_re : 0 < (b + n).re := by
    simp only [add_re, natCast_re]
    linarith [n.cast_nonneg (α := ℝ)]
  have hpoch := Gamma_add_nat_div_Gamma_eq (n := n) b (ne_neg_natCast_of_re_pos hb)
  have hbnc : b + (n : ℂ) + (c - b) = c + n := by ring
  rw [hint, betaIntegral_eq_Gamma_mul_div (b + n) (c - b) hbn_re hcb, hbnc, hmc,
    coeff_regularizedGaussHGFunSeries, ← hpoch]
  field_simp [Gamma_ne_zero_of_re_pos hb, Gamma_ne_zero_of_re_pos hcb]

/-- **Euler's integral representation** (DLMF 15.6.1) on the open unit disk: when
`0 < b.re < c.re` and `‖z‖ < 1`, `regularizedGaussHGFun a b c z` equals `eulerIntegral a b c z`. -/
theorem regularizedGaussHGFun_eq_eulerIntegral (a : ℂ) {b c z : ℂ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z = eulerIntegral a b c z := by
  -- Expand `(1 - z t) ^ (-a)` in powers of `z t` and integrate term by term.
  have hdct := TauCeti.hasSum_integral_mul_multichoose_mul_pow a
    (betaIntegral_convergent (v := c - b) hb (by simpa using sub_pos.mpr hbc))
    (v := fun t : ℝ => z * t) (by fun_prop) hz fun t ht => by
      rw [norm_mul, Complex.norm_of_nonneg ht.1.le]
      exact mul_le_of_le_one_right (norm_nonneg z) ht.2
  have heuler := (hdct.mul_left (Gamma b * Gamma (c - b))⁻¹).congr_fun fun n =>
    (inv_Gamma_mul_integral_multichoose_mul_pow a hb hbc z n).symm
  exact (regularizedGaussHGFun_eq_tsum_coeff_mul_pow a b c z).trans heuler.tsum_eq

/-- **Euler's integral representation** (DLMF 15.6.1) of the terminating Gauss function: when
`0 < b.re < c.re`, the polynomial `regularizedGaussHGFun (-n) b c z` equals
`eulerIntegral (-n) b c z` for every `z`, including `z` on the cut `[1, ∞)`. -/
theorem regularizedGaussHGFun_neg_natCast_eq_eulerIntegral (n : ℕ) {b c : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (z : ℂ) :
    regularizedGaussHGFun (-n) b c z = eulerIntegral (-n) b c z := by
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)
  have hw_int : IntervalIntegrable w volume 0 1 := betaIntegral_convergent hb hcb
  -- With first parameter `-n` the Euler kernel is the polynomial `(1 - z t) ^ n`, so the
  -- integral is a polynomial in `z`.
  have hpoly : eulerIntegral (-n) b c = fun z => (Gamma b * Gamma (c - b))⁻¹ *
      ∑ k ∈ Finset.range (n + 1),
        (∫ t : ℝ in 0..1, w t * ((-(t : ℂ)) ^ k * n.choose k)) * z ^ k := by
    ext z
    simp_rw [eulerIntegral_def, ← intervalIntegral.integral_mul_const]
    rw [← intervalIntegral.integral_finsetSum fun k _ =>
      (hw_int.mul_continuousOn (by fun_prop)).mul_const _]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [neg_neg, cpow_natCast, show (1 : ℂ) - z * t = -(t : ℂ) * z + 1 by ring, add_pow,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [w]
    ring
  have hf : AnalyticOnNhd ℂ (eulerIntegral (-n) b c) univ := by
    rw [hpoly]
    exact fun z _ => Differentiable.analyticAt (by fun_prop) z
  have hg : AnalyticOnNhd ℂ (regularizedGaussHGFun (-n) b c) univ := by
    have h := (regularizedGaussHGFunSeries (-n) b c).hasFPowerSeriesOnBall (by simp)
    rw [radius_regularizedGaussHGFunSeries_eq_top_of_left] at h
    exact fun z _ => h.analyticAt_of_mem (by simp)
  refine congrFun (hg.eq_of_eventuallyEq hf (z₀ := 0) ?_) z
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with z hz
  exact regularizedGaussHGFun_eq_eulerIntegral _ hb hbc (by simpa using hz)

/-- At `z = 1`, Euler's normalized integral reduces to Euler's Beta integral when `0 < b.re` and
`(a + b).re < c.re`. -/
theorem eulerIntegral_one {a b c : ℂ} (hb : 0 < b.re) (habc : (a + b).re < c.re) :
    eulerIntegral a b c 1 = Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) := by
  have hcab : 0 < (c - a - b).re := by
    simp only [sub_re, add_re] at habc ⊢
    linarith
  have hae : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
  have hint :
      (∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (1 - 1 * (t : ℂ)) ^ (-a)) = betaIntegral b (c - a - b) := by
    rw [betaIntegral]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with t ht1 ht
    rw [uIoc_of_le zero_le_one] at ht
    have h1t : (1 : ℂ) - (t : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (ofReal_ne_one.mpr ht1).symm
    rw [one_mul, mul_assoc, ← cpow_add _ _ h1t]
    congr 2
    ring
  have hca : b + (c - a - b) = c - a := by ring
  rw [eulerIntegral_def, hint, betaIntegral_eq_Gamma_mul_div b (c - a - b) hb hcab, hca]
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  rw [mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  linear_combination
    Gamma (c - a - b) * (Gamma (c - b))⁻¹ * (Gamma (c - a))⁻¹ * inv_mul_cancel₀ hΓb

private theorem one_sub_mul_ofReal_mem_slitPlane_of_mem_closedBall {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 - z * (t : ℂ) ∈ slitPlane := by
  have hnorm : ‖-(z * (t : ℂ))‖ < 1 := by
    rw [norm_neg, norm_mul, Complex.norm_of_nonneg ht.1.le]
    exact (mul_le_of_le_one_left ht.1.le (by simpa using hz)).trans_lt ht.2
  simpa [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one hnorm

private theorem norm_eulerIntegrand_le (a b c : ℂ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * (t : ℂ)) ^ (-a)‖ ≤
      Real.exp (Real.pi * |a.im|) *
        (2 ^ (-a.re) * ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖ +
          ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - a - b - 1)‖) := by
  let w₁ : ℝ := ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖
  let w₂ : ℝ := ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - a - b - 1)‖
  have hcpow : ‖(1 - z * (t : ℂ)) ^ (-a)‖ ≤
      Real.exp (Real.pi * |a.im|) * (2 ^ (-a.re) + (1 - t) ^ (-a.re)) := by
    simpa [neg_im, neg_re] using
      norm_one_sub_mul_ofReal_cpow_le (-a) (by simpa using hz) ht.1.le ht.2
  have hw₂_eq : w₁ * (1 - t) ^ (-a.re) = w₂ := by
    have h1t_eq : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
    have h1t_ne : (1 : ℂ) - (t : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (ofReal_ne_one.mpr ht.2.ne).symm
    have hnorm_1t : ‖(1 - (t : ℂ)) ^ (-a)‖ = (1 - t) ^ (-a.re) := by
      rw [h1t_eq, norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr ht.2), neg_re]
    dsimp only [w₁, w₂]
    rw [← hnorm_1t, ← norm_mul, mul_assoc, ← cpow_add _ _ h1t_ne]
    congr 3
    ring
  rw [norm_mul]
  calc w₁ * ‖(1 - z * (t : ℂ)) ^ (-a)‖
      ≤ w₁ * (Real.exp (Real.pi * |a.im|) * (2 ^ (-a.re) + (1 - t) ^ (-a.re))) :=
        mul_le_mul_of_nonneg_left hcpow (norm_nonneg _)
    _ = Real.exp (Real.pi * |a.im|) * (2 ^ (-a.re) * w₁ + w₁ * (1 - t) ^ (-a.re)) := by ring
    _ = Real.exp (Real.pi * |a.im|) * (2 ^ (-a.re) * w₁ + w₂) := by rw [hw₂_eq]

/-- When `0 < b.re < c.re` and `(a + b).re < c.re`, `eulerIntegral a b c` is continuous on the
closed unit disk `Metric.closedBall 0 1`. -/
theorem continuousOn_eulerIntegral_closedBall {a b c : ℂ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (habc : (a + b).re < c.re) :
    ContinuousOn (eulerIntegral a b c) (Metric.closedBall 0 1) := by
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hcab : 0 < (c - a - b).re := by
    simp only [sub_re, add_re] at habc ⊢
    linarith
  -- Restrict to `(0, 1)`, where `‖z * t‖ < 1` holds uniformly on `closedBall 0 1`.
  let μ : Measure ℝ := volume.restrict (Ioo 0 1)
  have hμ : μ = volume.restrict (Ioc 0 1) := restrict_Ioo_eq_restrict_Ioc
  let F : ℂ → ℝ → ℂ := fun z t =>
    (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * (t : ℂ)) ^ (-a)
  let w : ℂ → ℝ → ℝ := fun v t => ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (v - 1)‖
  let C : ℝ := Real.exp (Real.pi * |a.im|)
  have hbeta_int {v : ℂ} (hv : 0 < v.re) : Integrable (w v) μ := by
    rw [hμ]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (betaIntegral_convergent hb hv).norm
  -- Apply dominated convergence on `μ` with integrable majorant
  -- `C * (2 ^ (-a.re) * w (c - b) + w (c - a - b))`.
  have hcont_int : ContinuousOn (fun z => ∫ t, F z t ∂μ) (Metric.closedBall 0 1) := by
    refine MeasureTheory.continuousOn_of_dominated
      (bound := fun t => C * (2 ^ (-a.re) * w (c - b) t + w (c - a - b) t))
      (fun z hz => ?_) (fun z hz => ?_)
      ((((hbeta_int hcb).const_mul (2 ^ (-a.re))).add (hbeta_int hcab)).const_mul C) ?_
    · refine (continuousOn_of_forall_continuousAt fun t ht => ?_).aestronglyMeasurable
        measurableSet_Ioo
      refine ((ContinuousAt.cpow (by fun_prop) continuousAt_const
        (ofReal_mem_slitPlane.mpr ht.1)).mul
        (ContinuousAt.cpow (by fun_prop) continuousAt_const ?_)).mul
        (ContinuousAt.cpow (by fun_prop) continuousAt_const
          (one_sub_mul_ofReal_mem_slitPlane_of_mem_closedBall hz ht))
      simpa using ofReal_mem_slitPlane.mpr (sub_pos.mpr ht.2)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact norm_eulerIntegrand_le a b c hz ht
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      refine continuousOn_of_forall_continuousAt fun z hz => ?_
      exact continuousAt_const.mul
        (ContinuousAt.cpow (by fun_prop) continuousAt_const
          (one_sub_mul_ofReal_mem_slitPlane_of_mem_closedBall hz ht))
  have heq : eulerIntegral a b c = fun z => (Gamma b * Gamma (c - b))⁻¹ * ∫ t, F z t ∂μ := by
    ext z
    rw [eulerIntegral_def, intervalIntegral.integral_of_le zero_le_one, ← hμ]
  rw [heq]
  exact continuousOn_const.mul hcont_int

private theorem tendsto_regularizedGaussHGFun_nhdsWithin_ball_one_of_re_pos_of_re_lt {a b c : ℂ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (habc : (a + b).re < c.re) :
    Tendsto (regularizedGaussHGFun a b c) (𝓝[Metric.ball 0 1] 1)
      (𝓝 (Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)))) := by
  have hcont := ((continuousOn_eulerIntegral_closedBall hb hbc habc).continuousWithinAt
    (by simp : (1 : ℂ) ∈ Metric.closedBall 0 1)).mono Metric.ball_subset_closedBall
  rw [ContinuousWithinAt, eulerIntegral_one hb habc] at hcont
  exact hcont.congr' (eventuallyEq_nhdsWithin_of_eqOn fun z hz =>
    (regularizedGaussHGFun_eq_eulerIntegral a hb hbc (by simpa using hz)).symm)

private theorem tendsto_regularizedGaussHGFun_nhdsWithin_ball_one_of_re_pos {a b c : ℂ}
    (hb : 0 < b.re) (habc : (a + b).re < c.re) :
    Tendsto (regularizedGaussHGFun a b c) (𝓝[Metric.ball 0 1] 1)
      (𝓝 (Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)))) := by
  obtain ⟨N, hcN⟩ := exists_nat_gt (b.re - c.re)
  induction N generalizing a c with
  | zero =>
    exact tendsto_regularizedGaussHGFun_nhdsWithin_ball_one_of_re_pos_of_re_lt hb
      (by simp only [Nat.cast_zero] at hcN; linarith) habc
  | succ N ih =>
    -- Shift `c` upward via DLMF 15.5.15 until `b.re < c.re` holds.
    have hcN' : b.re - (c + 1).re < N := by
      simp only [Nat.cast_add, Nat.cast_one] at hcN
      simp only [add_re, one_re]
      linarith
    have h₁ := ih (a := a) (c := c + 1)
      (by simp only [add_re, one_re] at habc ⊢; linarith) hcN'
    have h₂ := ih (a := a + 1) (c := c + 1)
      (by simp only [add_re, one_re] at habc ⊢; linarith) hcN'
    have hlim := (h₁.const_mul (c - a)).add (h₂.const_mul a)
    have hcab : 0 < (c - a - b).re := by simp only [sub_re, add_re] at habc ⊢; linarith
    have hcab_ne : c - a - b ≠ 0 := by simpa using ne_neg_natCast_of_re_pos hcab 0
    have hval :
        (c - a) * (Gamma (c + 1 - a - b) / (Gamma (c + 1 - a) * Gamma (c + 1 - b))) +
            a * (Gamma (c + 1 - (a + 1) - b) /
              (Gamma (c + 1 - (a + 1)) * Gamma (c + 1 - b))) =
          Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) := by
      have hr₁ : c + 1 - a - b = c - a - b + 1 := by ring
      have hr₂ : c + 1 - a = c - a + 1 := by ring
      have hr₃ : c + 1 - b = c - b + 1 := by ring
      have hr₄ : c + 1 - (a + 1) - b = c - a - b := by ring
      have hr₅ : c + 1 - (a + 1) = c - a := by ring
      rw [hr₁, hr₂, hr₃, hr₄, hr₅, Gamma_add_one (c - a - b) hcab_ne]
      simp only [div_eq_mul_inv, mul_inv]
      linear_combination
        -(c - a - b) * Gamma (c - a - b) * (Gamma (c - b + 1))⁻¹ *
            one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c - a) -
          Gamma (c - a - b) * (Gamma (c - a))⁻¹ *
            one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c - b)
    rw [hval] at hlim
    exact hlim.congr' (eventuallyEq_nhdsWithin_of_eqOn fun z hz =>
      (regularizedGaussHGFun_eq_sub_mul_add_mul a b c (by simpa using hz)).symm)

private theorem regularizedGaussHGFun_eq_mul_sub_mul_mul (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      c * regularizedGaussHGFun a (b + 1) (c + 1) z -
        a * (c - b) * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 2) z := by
  have h₁ := regularizedGaussHGFun_eq_sub_mul_add_mul b a c hz
  rw [regularizedGaussHGFun_symm b a, regularizedGaussHGFun_symm b a,
    regularizedGaussHGFun_symm (b + 1) a] at h₁
  have h₂ := regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul a b (c + 1) hz
  have hc2 : c + 1 + 1 = c + 2 := by ring
  rw [hc2] at h₂
  linear_combination h₁ + (c - b) * h₂

/-- **Gauss's summation theorem** as a limit on the open unit disk (DLMF 15.4.20): when
`(a + b).re < c.re`, `regularizedGaussHGFun a b c z` tends to
`Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b))` as `z → 1` within `Metric.ball 0 1`. -/
theorem tendsto_regularizedGaussHGFun_nhdsWithin_ball_one {a b c : ℂ}
    (habc : (a + b).re < c.re) :
    Tendsto (regularizedGaussHGFun a b c) (𝓝[Metric.ball 0 1] 1)
      (𝓝 (Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)))) := by
  obtain ⟨N, hbN⟩ := exists_nat_gt (-b.re)
  induction N generalizing a b c with
  | zero =>
    exact tendsto_regularizedGaussHGFun_nhdsWithin_ball_one_of_re_pos
      (by simp only [Nat.cast_zero, neg_lt_zero] at hbN; exact hbN) habc
  | succ N ih =>
    -- Shift `b` and `c` upward together so `(c - a - b).re` stays positive until `0 < b.re` holds.
    have hbN' : -(b + 1).re < N := by
      simp only [Nat.cast_add, Nat.cast_one] at hbN
      simp only [add_re, one_re]
      linarith
    have hre2 : (2 : ℂ).re = 2 := by norm_num
    have h₁ := ih (a := a) (b := b + 1) (c := c + 1)
      (by simp only [add_re, one_re] at habc ⊢; linarith) hbN'
    have h₂ := ih (a := a + 1) (b := b + 1) (c := c + 2)
      (by simp only [add_re, one_re, hre2] at habc ⊢; linarith) hbN'
    have hz_id : Tendsto (fun z : ℂ => z) (𝓝[Metric.ball 0 1] 1) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hlim := (h₁.const_mul c).sub ((hz_id.const_mul (a * (c - b))).mul h₂)
    have hval :
        c * (Gamma (c + 1 - a - (b + 1)) / (Gamma (c + 1 - a) * Gamma (c + 1 - (b + 1)))) -
            a * (c - b) * 1 *
              (Gamma (c + 2 - (a + 1) - (b + 1)) /
                (Gamma (c + 2 - (a + 1)) * Gamma (c + 2 - (b + 1)))) =
          Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) := by
      have hr₁ : c + 1 - a - (b + 1) = c - a - b := by ring
      have hr₂ : c + 1 - a = c - a + 1 := by ring
      have hr₃ : c + 1 - (b + 1) = c - b := by ring
      have hr₄ : c + 2 - (a + 1) - (b + 1) = c - a - b := by ring
      have hr₅ : c + 2 - (a + 1) = c - a + 1 := by ring
      have hr₆ : c + 2 - (b + 1) = c - b + 1 := by ring
      rw [hr₁, hr₂, hr₃, hr₄, hr₅, hr₆]
      simp only [div_eq_mul_inv, mul_inv]
      linear_combination
        a * Gamma (c - a - b) * (Gamma (c - a + 1))⁻¹ *
            one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c - b) -
          Gamma (c - a - b) * (Gamma (c - b))⁻¹ *
            one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c - a)
    rw [hval] at hlim
    exact hlim.congr' (eventuallyEq_nhdsWithin_of_eqOn fun z hz =>
      (regularizedGaussHGFun_eq_mul_sub_mul_mul a b c (by simpa using hz)).symm)

end Complex
