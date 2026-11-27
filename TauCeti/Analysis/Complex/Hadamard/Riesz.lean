/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import TauCeti.Analysis.Complex.Hadamard.OrderOne
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The zero contribution for the first Riesz kernel

A zero `ρ` of multiplicity `m` contributes `m y^ρ / (ρ (1 - ρ))` to a first Riesz explicit
formula. This file proves absolute convergence, continuity and power bounds for the zero sum, and
relates its Mellin transform to the logarithmic derivative after subtracting the affine interpolant
at `0` and `1`. It treats the entire factor of the completed function, not the gamma factors
or the trivial-zero correction.

The partial-fraction calculation uses `OrderLE.logDeriv_eq_add_tsum`, the genus-one Hadamard
expansion of the logarithmic derivative.
-/

public section

open Complex Filter MeasureTheory Set

namespace TauCeti

variable {f : ℂ → ℂ}

/-- The contribution of the zeros of an entire function to a first Riesz explicit formula,
with multiplicities read from the whole-plane divisor. -/
noncomputable def rieszZeroSeries (f : ℂ → ℂ) (y : ℝ) : ℂ :=
  ∑' ρ : (MeromorphicOn.divisor f univ).support,
    ((MeromorphicOn.divisor f univ ρ).toNat : ℂ) / (ρ * (1 - ρ)) * (y : ℂ) ^ (ρ : ℂ)

/-- The divisor expansion of the first Riesz zero series. -/
theorem rieszZeroSeries_def (f : ℂ → ℂ) (y : ℝ) :
    rieszZeroSeries f y = ∑' ρ : (MeromorphicOn.divisor f univ).support,
      ((MeromorphicOn.divisor f univ ρ).toNat : ℂ) / (ρ * (1 - ρ)) * (y : ℂ) ^ (ρ : ℂ) := (rfl)

/-- The coefficients of the first Riesz zero series are absolutely summable for an entire
function of order less than two. -/
theorem OrderLE.summable_norm_divisor_div_mul_one_sub {A : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2) :
    Summable (fun ρ : (MeromorphicOn.divisor f univ).support ↦
      ‖((MeromorphicOn.divisor f univ ρ).toNat : ℂ) / (ρ * (1 - ρ))‖) := by
  classical
  refine (h.summable_norm_divisor_mul_one_div_sub_add_one_div hf hA 1).congr_cofinite ?_
  rw [EventuallyEq, eventually_cofinite]
  refine (((finite_singleton (0 : ℂ)).union (finite_singleton 1)).preimage
    Subtype.coe_injective.injOn).subset fun ρ hρ ↦ ?_
  by_contra hnot
  simp only [mem_preimage, mem_union, mem_singleton_iff, not_or] at hnot
  apply hρ
  congr 1
  field_simp [hnot.1, sub_ne_zero.mpr (Ne.symm hnot.2)]
  ring

private theorem norm_rieszTerm_le (hf : Differentiable ℂ f) {σ : ℝ}
    (hσ : ∀ ρ, f ρ = 0 → ρ.re ≤ σ) (ρ : (MeromorphicOn.divisor f univ).support)
    {y : ℝ} (hy : 1 ≤ y) :
    ‖((MeromorphicOn.divisor f univ ρ).toNat : ℂ) / (ρ * (1 - ρ)) * (y : ℂ) ^ (ρ : ℂ)‖ ≤
      ‖((MeromorphicOn.divisor f univ ρ).toNat : ℂ) / (ρ * (1 - ρ))‖ * y ^ σ := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hy)]
  have hρ := hσ ρ ((hf.analyticAt _).apply_eq_zero_of_divisor_ne_zero ρ.prop)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy hρ) (norm_nonneg _)

/-- Absolute convergence of the first Riesz zero series when the zeros are bounded to the right. -/
theorem OrderLE.summable_norm_rieszZeroSeries {A σ : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2) (hσ : ∀ ρ, f ρ = 0 → ρ.re ≤ σ)
    {y : ℝ} (hy : 1 ≤ y) :
    Summable (fun ρ : (MeromorphicOn.divisor f univ).support ↦
      ‖((MeromorphicOn.divisor f univ ρ).toNat : ℂ) / (ρ * (1 - ρ)) * (y : ℂ) ^ (ρ : ℂ)‖) := by
  refine ((h.summable_norm_divisor_div_mul_one_sub hf hA).mul_right (y ^ σ)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (fun ρ ↦ norm_rieszTerm_le hf hσ ρ hy)

/-- A right bound `σ` on the zeros gives a `y^σ` bound for the first Riesz zero series on `y ≥ 1`.
The coefficient sum is independent of `σ`. -/
theorem OrderLE.norm_rieszZeroSeries_le {A σ : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2) (hσ : ∀ ρ, f ρ = 0 → ρ.re ≤ σ)
    {y : ℝ} (hy : 1 ≤ y) :
    ‖rieszZeroSeries f y‖ ≤
      (∑' ρ : (MeromorphicOn.divisor f univ).support,
        ‖((MeromorphicOn.divisor f univ ρ).toNat : ℂ) / (ρ * (1 - ρ))‖) * y ^ σ := by
  rw [rieszZeroSeries_def, ← tsum_mul_right]
  have hs := h.summable_norm_rieszZeroSeries hf hA hσ hy
  exact (norm_tsum_le_tsum_norm hs).trans
    (hs.tsum_le_tsum (fun ρ ↦ norm_rieszTerm_le hf hσ ρ hy)
      ((h.summable_norm_divisor_div_mul_one_sub hf hA).mul_right (y ^ σ)))

/-- The affine interpolation of the logarithmic derivative at `0` and `1` minus the logarithmic
derivative at `s` is the partial-fraction series with first Riesz weights, multiplied by
`s (s - 1)`. No division by `s` or `s - 1` is needed, so the identity includes both endpoints. -/
theorem OrderLE.hasSum_riesz_divisor_logDeriv (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (h1 : f 1 ≠ 0) {s : ℂ} (hs : f s ≠ 0) :
    HasSum (fun ρ : (MeromorphicOn.divisor f univ).support ↦
      (s * (s - 1)) * (((MeromorphicOn.divisor f univ ρ).toNat : ℂ) /
        (ρ * (1 - ρ)) / (s - ρ)))
      (logDeriv f 0 + s * (logDeriv f 1 - logDeriv f 0) - logDeriv f s) := by
  let a (z : ℂ) (ρ : (MeromorphicOn.divisor f univ).support) : ℂ :=
    ((MeromorphicOn.divisor f univ ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / ρ)
  have ha (z : ℂ) (hz : f z ≠ 0) : HasSum (a z) (logDeriv f z - logDeriv f 0) := by
    have hsum : Summable (a z) :=
      (h.summable_norm_divisor_mul_one_div_sub_add_one_div hf (by norm_num) z).of_norm
    rw [h.logDeriv_eq_add_tsum hf h0 hz, add_sub_cancel_left]
    exact hsum.hasSum
  convert ((ha 1 h1).mul_left s).sub (ha s hs) using 1
  · ext ρ
    have hz (z : ℂ) (h : f z ≠ 0) : z - (ρ : ℂ) ≠ 0 := by
      have hρ := (hf.analyticAt _).apply_eq_zero_of_divisor_ne_zero ρ.prop
      exact sub_ne_zero.mpr fun e ↦ h (e ▸ hρ)
    dsimp [a]
    have hρ : (ρ : ℂ) ≠ 0 := by simpa using (hz 0 h0)
    field_simp [hρ, hz 1 h1, hz s hs]
    ring
  · ring

/-- The first Riesz zero series is continuous up to `y = 1`. -/
theorem OrderLE.continuousOn_rieszZeroSeries {A σ : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2) (hσ : ∀ ρ, f ρ = 0 → ρ.re ≤ σ) :
    ContinuousOn (rieszZeroSeries f) (Ici 1) := by
  refine continuousOn_of_locally_continuousOn fun y _ ↦ ?_
  refine ⟨Iio (y + 1), isOpen_Iio, lt_add_one y, ?_⟩
  simp only [funext (rieszZeroSeries_def f)]
  refine continuousOn_tsum (fun ρ x hx ↦ ?_)
    ((h.summable_norm_divisor_div_mul_one_sub hf hA).mul_right ((y + 1) ^ max σ 0))
    (fun ρ x hx ↦ ?_)
  · exact continuousWithinAt_const.mul
      ((continuousAt_ofReal_cpow_const x ρ
        (Or.inr (zero_lt_one.trans_le (mem_Ici.mp hx.1)).ne')).continuousWithinAt)
  · have hmax z hz := (hσ z hz).trans (le_max_left σ 0)
    refine (norm_rieszTerm_le hf hmax ρ hx.1).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (zero_le_one.trans (mem_Ici.mp hx.1)) (mem_Iio.mp hx.2).le
        (le_max_right _ _)) (norm_nonneg _)

/-- Above the right bound on the zeros the first Riesz zero series has an absolutely convergent
upper-tail Mellin integral. -/
theorem OrderLE.integrableOn_rieszZeroSeries_mul_cpow {A σ : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2) (hσ : ∀ ρ, f ρ = 0 → ρ.re ≤ σ)
    {s : ℂ} (hs : σ < s.re) :
    IntegrableOn (fun y : ℝ ↦ rieszZeroSeries f y * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hb := (integrableOn_Ioi_rpow_of_lt (a := σ - s.re - 1) (by linarith) zero_lt_one).const_mul
    (∑' ρ : (MeromorphicOn.divisor f univ).support,
      ‖((MeromorphicOn.divisor f univ ρ).toNat : ℂ) / (ρ * (1 - ρ))‖)
  refine hb.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((h.continuousOn_rieszZeroSeries hf hA hσ).mono Ioi_subset_Ici_self).mul
      (fun x hx ↦ (continuousAt_ofReal_cpow_const x _
        (Or.inr (zero_lt_one.trans (mem_Ioi.mp hx)).ne')).continuousWithinAt)
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (1 : ℝ)))] with y hy
    have hy' : 1 < y := hy
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hy')]
    refine (mul_le_mul_of_nonneg_right (h.norm_rieszZeroSeries_le hf hA hσ hy'.le)
      (Real.rpow_nonneg (by positivity) _)).trans_eq ?_
    rw [mul_assoc, ← Real.rpow_add (by positivity)]
    simp [sub_eq_add_neg, add_assoc]

/-- The upper-tail Mellin integral of the first Riesz zero series is the sum of the simple
fractions with residues `m_ρ / (ρ (1 - ρ))`. -/
theorem OrderLE.hasSum_integral_rieszZeroSeries_mul_cpow {A σ : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2) (hσ : ∀ ρ, f ρ = 0 → ρ.re ≤ σ)
    {s : ℂ} (hs : σ < s.re) :
    HasSum (fun ρ : (MeromorphicOn.divisor f univ).support ↦
      ((MeromorphicOn.divisor f univ ρ).toNat : ℂ) / (ρ * (1 - ρ)) / (s - ρ))
      (∫ y : ℝ in Ioi 1, rieszZeroSeries f y * (y : ℂ) ^ (-s - 1)) := by
  let S := (MeromorphicOn.divisor f univ).support
  have hd : IsDiscrete S := by simpa [S] using (MeromorphicOn.divisor f univ).discreteSupport
  have : DiscreteTopology S := isDiscrete_iff_discreteTopology.mp hd
  have : Countable S := countable_of_Lindelof_of_discrete
  let c (ρ : S) : ℂ := ((MeromorphicOn.divisor f univ ρ).toNat : ℂ) / (ρ * (1 - ρ))
  let g (ρ : S) (y : ℝ) : ℂ := c ρ * (y : ℂ) ^ ((ρ : ℂ) - s - 1)
  have hre (ρ : S) : (ρ : ℂ).re ≤ σ :=
    hσ ρ ((hf.analyticAt _).apply_eq_zero_of_divisor_ne_zero ρ.prop)
  have hlt (ρ : S) : ((ρ : ℂ) - s - 1).re < -1 := by
    simp only [sub_re, one_re]
    linarith [hre ρ]
  have hi (ρ : S) : IntegrableOn (g ρ) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt (hlt ρ) zero_lt_one).const_mul _
  have hnorm (ρ : S) : ∫ y : ℝ in Ioi 1, ‖g ρ y‖ ≤
      ‖c ρ‖ * (∫ y : ℝ in Ioi 1, y ^ (σ - s.re - 1)) := by
    have hb := integrableOn_Ioi_rpow_of_lt (a := σ - s.re - 1) (by linarith) zero_lt_one
    rw [← integral_const_mul]
    refine integral_mono_ae (hi ρ).norm (hb.const_mul _) ?_
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (1 : ℝ)))] with y hy
    have hy' : 1 < y := hy
    dsimp [g]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hy')]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy'.le ?_) (norm_nonneg _)
    simp only [sub_re, one_re]
    linarith [hre ρ]
  have hsum := ((h.summable_norm_divisor_div_mul_one_sub hf hA).mul_right
    (∫ y : ℝ in Ioi 1, y ^ (σ - s.re - 1))).of_nonneg_of_le
      (fun ρ ↦ integral_nonneg fun y ↦ norm_nonneg (g ρ y)) hnorm
  convert hasSum_integral_of_summable_integral_norm hi hsum using 1
  · ext ρ
    dsimp [g, c]
    rw [integral_const_mul, integral_Ioi_cpow_of_lt (hlt ρ) zero_lt_one]
    have he : -(1 : ℂ) / ((ρ : ℂ) - s) = 1 / (s - (ρ : ℂ)) := by
      rw [neg_div, ← div_neg_eq_neg_div, neg_sub]
    simp only [ofReal_one, one_cpow, sub_add_cancel, he, mul_one_div]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (1 : ℝ)))] with y hy
    have hy' : 1 < y := hy
    rw [rieszZeroSeries_def, ← tsum_mul_right]
    refine tsum_congr fun ρ ↦ ?_
    dsimp [g, c]
    rw [mul_assoc, ← cpow_add _ _ (ofReal_ne_zero.mpr (zero_lt_one.trans hy').ne')]
    congr 2
    ring

/-- The Mellin transform of the first Riesz zero series recovers the logarithmic derivative
of the entire function with its affine interpolant subtracted and sign reversed. -/
theorem OrderLE.mul_integral_rieszZeroSeries_mul_cpow (h : OrderLE f 1)
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) (h1 : f 1 ≠ 0)
    {σ : ℝ} (hσ : ∀ ρ, f ρ = 0 → ρ.re ≤ σ) {s : ℂ} (hs : σ < s.re) :
    (s * (s - 1)) * (∫ y : ℝ in Ioi 1, rieszZeroSeries f y * (y : ℂ) ^ (-s - 1)) =
      logDeriv f 0 + s * (logDeriv f 1 - logDeriv f 0) - logDeriv f s :=
  ((h.hasSum_integral_rieszZeroSeries_mul_cpow hf (by norm_num) hσ hs).mul_left _).unique
    (h.hasSum_riesz_divisor_logDeriv hf h0 h1 fun hfs ↦ hs.not_ge (hσ s hfs))

end TauCeti
