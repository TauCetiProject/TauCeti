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
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric
import TauCeti.RingTheory.Binomial

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
integrating termwise against the Beta kernel identifies `Complex.eulerIntegral a b c z` with
`Complex.regularizedGaussHGFun a b c z` (`Complex.eulerIntegral_eq_regularizedGaussHGFun`).
Outside `0 < re b < re c`, `eulerIntegral` is only the totalized integral, not an analytic
continuation; in particular, its normalized value can vanish when a Gamma factor has a pole.

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

private theorem integral_beta_mul_multichoose_term (a : ℂ) {b c : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (z : ℂ) (n : ℕ) :
    (Gamma b * Gamma (c - b))⁻¹ *
        (∫ t : ℝ in 0..1, ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
          (Ring.multichoose a n * (z * (t : ℂ)) ^ n)) =
      ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b /
        (n.factorial * Gamma (c + n))) * z ^ n := by
  have hint : (∫ t : ℝ in 0..1, ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
        (Ring.multichoose a n * (z * (t : ℂ)) ^ n)) =
      Ring.multichoose a n * z ^ n * (Gamma (b + n) * Gamma (c - b) / Gamma (c + n)) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← setIntegral_congr_set Ioo_ae_eq_Ioc,
      setIntegral_congr_fun measurableSet_Ioo (g := fun t : ℝ => (Ring.multichoose a n * z ^ n) *
        ((t : ℂ) ^ (b + n - 1) * (1 - (t : ℂ)) ^ (c - b - 1))) (fun t ht => by
          dsimp only; rw [mul_pow, ← cpow_natCast (t : ℂ) n,
            add_sub_right_comm,
            cpow_add _ _ (ofReal_ne_zero.2 ht.1.ne')]; ring),
      integral_const_mul, setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one, ← betaIntegral,
      betaIntegral_eq_Gamma_mul_div (b + n) (c - b)
        (by simp; linarith [n.cast_nonneg (α := ℝ)]) (by simpa using sub_pos.2 hbc),
      add_right_comm b (n : ℂ) (c - b), add_sub_cancel]
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using sub_pos.2 hbc)
  have hpoch := (div_eq_iff hGb).1
    (Gamma_add_nat_div_Gamma_eq (n := n) b (ne_neg_natCast_of_re_pos hb))
  rw [hint, TauCeti.Ring.multichoose_eq_ascPochhammer_eval_div_factorial, hpoch]
  field_simp [hGb, hGcb, Nat.cast_ne_zero.2 n.factorial_ne_zero]

/-- **Euler's integral representation of the regularized Gauss series on the open unit disk**
(DLMF 15.6.1). For `0 < Re b < Re c`, arbitrary `a : ℂ`, and `‖z‖ < 1`, the normalized Euler
integral equals `regularizedGaussHGFun a b c z`. -/
theorem eulerIntegral_eq_regularizedGaussHGFun (a : ℂ) {b c z : ℂ}
    (hb : 0 < b.re) (hbc : b.re < c.re) (hz : ‖z‖ < 1) :
    eulerIntegral a b c z = regularizedGaussHGFun a b c z := by
  have hcb' : 0 < (c - b).re := by simpa using sub_pos.2 hbc
  let F : ℕ → ℝ → ℂ := fun n t =>
    ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) * (Ring.multichoose a n * (z * (t : ℂ)) ^ n)
  let bound : ℕ → ℝ → ℝ := fun n t =>
    ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖ * ‖Ring.multichoose a n * z ^ n‖
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) (volume.restrict (uIoc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff.1 ((betaIntegral_convergent hb hcb').mul_continuousOn
      (g := fun t : ℝ => Ring.multichoose a n * (z * (t : ℂ)) ^ n)
      (by fun_prop))).aestronglyMeasurable
  have h_bound (n : ℕ) : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → ‖F n t‖ ≤ bound n t := by
    refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    simp only [F, bound, norm_mul, norm_pow]
    gcongr
    exact mul_le_of_le_one_right (norm_nonneg z)
      (by simpa [Real.norm_eq_abs, abs_of_pos ht.1] using ht.2)
  have h_lim : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) 1 → HasSum (fun n => F n t)
      ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * (t : ℂ)) ^ (-a)) := by
    refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hzt : ‖z * (t : ℂ)‖ < 1 := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      exact (mul_le_of_le_one_right (norm_nonneg z) ht.2).trans_lt hz
    simpa [F, one_div, ← cpow_neg] using
      (TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one (r := a) hzt).mul_left _
  have hint_sum := intervalIntegral.hasSum_integral_of_dominated_convergence bound hF_meas h_bound
    (Eventually.of_forall fun _ _ => (TauCeti.summable_norm_multichoose_mul_pow hz).mul_left _)
    (by simpa only [bound, tsum_mul_left] using (betaIntegral_convergent hb hcb').norm.mul_const _)
    h_lim
  rw [eulerIntegral_def]
  exact ((hint_sum.mul_left (Gamma b * Gamma (c - b))⁻¹).congr_fun
    fun n => (integral_beta_mul_multichoose_term a hb hbc z n).symm).unique
    (hasSum_regularizedGaussHGFun a b c hz)

end Complex
