/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import TauCeti.Analysis.Fourier.Hardy.RadialMean
import Mathlib.Analysis.Complex.TaylorSeries
import TauCeti.Analysis.Complex.Herglotz
import TauCeti.Analysis.Complex.Poisson.Integral
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The harmonic-majorant description of the Hardy space

A holomorphic function `F` on the open unit disk belongs to the Hardy space `H²` of the disk when
`‖F‖ ^ 2` has a real harmonic majorant. This file identifies these functions with the disk
functions `F_x w = ∑ n, x̂ n * w ^ n` of boundary Hardy functions `x ∈ TauCeti.HardySpace`, and
identifies the squared boundary norm `‖x‖ ^ 2` with the least value at the origin of a harmonic
majorant of `‖F_x‖ ^ 2`. This is the description of `H²` of the disk by harmonic majorants, the
analytic counterpart of the boundary model used for Toeplitz operators.

## Main definitions

* `TauCeti.HardySpace.poissonMajorant`: the Poisson integral `w ↦ ∫ P_w(t) ‖x t‖ ^ 2 dt` of the
  squared boundary modulus.

## Main results

* `TauCeti.HardySpace.diskFunction_eq_integral`: the Cauchy formula
  `F_x w = ∫ (1 - w * conj (e t))⁻¹ * x t dt`, where `e t = AddCircle.toCircle t`.
* `TauCeti.HardySpace.diskFunction_eq_integral_poissonKernel`: the Poisson formula
  `F_x w = ∫ P_w(t) * x t dt`.
* `TauCeti.HardySpace.harmonicOnNhd_poissonMajorant`,
  `TauCeti.HardySpace.norm_sq_diskFunction_le_poissonMajorant` and
  `TauCeti.HardySpace.poissonMajorant_zero`: the Poisson majorant is a harmonic majorant of
  `‖F_x‖ ^ 2` with value `‖x‖ ^ 2` at the origin.
* `TauCeti.HardySpace.isLeast_harmonic_majorant_zero`: `‖x‖ ^ 2` is the least value at the origin
  of a harmonic majorant of `‖F_x‖ ^ 2`.
* `TauCeti.HardySpace.exists_eqOn_diskFunction_of_harmonic_majorant`: a holomorphic function on
  the disk with a harmonic majorant `u` of its squared modulus is a disk function `F_x` with
  `‖x‖ ^ 2 ≤ u 0`.
* `TauCeti.HardySpace.exists_eqOn_diskFunction_iff`: the disk functions of Hardy functions are
  exactly the holomorphic functions on the disk whose squared modulus has a harmonic majorant.

## Implementation notes

The disk function is the Poisson integral of `x`, and the Cauchy–Schwarz inequality for the
probability measure `P_w(t) dt` shows that the Poisson integral of `‖x‖ ^ 2` majorizes
`‖F_x‖ ^ 2`. That Poisson integral is the real part of the Herglotz transform
`MeasureTheory.Measure.herglotzTransform` of the measure `‖x t‖ ^ 2 dt`, hence harmonic.

Conversely, if `F` is holomorphic with a harmonic majorant `u`, then for `0 < r < 1` the dilation
`w ↦ F (r * w)` is the disk function of the Hardy function with coefficients `aₙ * r ^ n`, where
`aₙ` are the Taylor coefficients of `F` at the origin. The circle means of this dilation are
circle means of `F`, which `TauCeti.circleAverage_le_of_harmonic_majorant` bounds by
`u 0`; their limit gives `∑ n, ‖aₙ‖ ^ 2 * r ^ (2 * n) ≤ u 0`, and letting `r → 1⁻` shows that
`(aₙ)` is square summable with `∑ n, ‖aₙ‖ ^ 2 ≤ u 0`.

## References

* P. L. Duren, *Theory of Hᵖ Spaces*, Academic Press (1970), Chapters 1 and 2.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw–Hill (1987), Chapter 17.
* J. Xia, *Traces, Indices and Spectral Theory of Toeplitz Operators on Multiply Connected
  Domains*, PhD thesis, Stony Brook (1983), Theorem I.2.1, specialized to the unit disk.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Topology AddCircle
open scoped ComplexConjugate

namespace TauCeti.HardySpace

variable (x : HardySpace) {w : ℂ}

private theorem integrable_coe :
    Integrable (x : Lp ℂ 2 (haarAddCircle (T := 1))) haarAddCircle :=
  (Lp.memLp _).integrable one_le_two

/-- **Cauchy formula for `H²`.** On the open unit disk the disk function is the integral of the
boundary function against the Cauchy–Szegő kernel `(1 - w * conj (e t))⁻¹`. -/
theorem diskFunction_eq_integral (hw : ‖w‖ < 1) :
    x.diskFunction w = ∫ t, (1 - w * conj (toCircle t : ℂ))⁻¹ *
      (x : Lp ℂ 2 (haarAddCircle (T := 1))) t ∂haarAddCircle := by
  have h := hasSum_integral_inv_one_sub_mul_fourier x.integrable_coe hw (-1)
  simp only [fourier_neg, fourier_one, mul_neg, mul_one, neg_neg] at h
  rw [diskFunction_def, ← h.tsum_eq]
  exact tsum_congr fun n ↦ mul_comm _ _

/-- Against the conjugate Cauchy–Szegő kernel a Hardy function integrates to its constant
coefficient, because its negative Fourier coefficients vanish. -/
private theorem integral_inv_one_sub_conj_mul (hw : ‖w‖ < 1) :
    ∫ t, (1 - conj w * (toCircle t : ℂ))⁻¹ * (x : Lp ℂ 2 (haarAddCircle (T := 1))) t
      ∂haarAddCircle = fourierCoeff (x : Lp ℂ 2 (haarAddCircle (T := 1))) 0 := by
  have h := hasSum_integral_inv_one_sub_mul_fourier x.integrable_coe
    (by rwa [norm_conj] : ‖conj w‖ < 1) 1
  simp only [fourier_one, mul_one] at h
  refine h.unique ?_
  convert hasSum_single (f := fun n : ℕ ↦ conj w ^ n *
    fourierCoeff (x : Lp ℂ 2 (haarAddCircle (T := 1))) (-n)) 0 fun n hn ↦ ?_ using 1
  · simp
  · rw [x.fourierCoeff_eq_zero (by omega), mul_zero]

/-- **Poisson formula for `H²`.** On the open unit disk the disk function is the Poisson integral
of the boundary function. -/
theorem diskFunction_eq_integral_poissonKernel (hw : ‖w‖ < 1) :
    x.diskFunction w = ∫ t, (poissonKernel 0 w (toCircle t) : ℂ) *
      (x : Lp ℂ 2 (haarAddCircle (T := 1))) t ∂haarAddCircle := by
  have hA := continuous_inv_one_sub_mul_fourier (T := 1) hw (-1)
  have hB := continuous_inv_one_sub_mul_fourier (T := 1) (by rwa [norm_conj] : ‖conj w‖ < 1) 1
  simp only [fourier_neg, fourier_one] at hA hB
  have hint := x.integrable_coe
  calc
    x.diskFunction w = (∫ t, (1 - w * conj (toCircle t : ℂ))⁻¹ *
          (x : Lp ℂ 2 (haarAddCircle (T := 1))) t ∂haarAddCircle) +
        (∫ t, (1 - conj w * (toCircle t : ℂ))⁻¹ *
          (x : Lp ℂ 2 (haarAddCircle (T := 1))) t ∂haarAddCircle) -
        ∫ t, (x : Lp ℂ 2 (haarAddCircle (T := 1))) t ∂haarAddCircle := by
      rw [x.diskFunction_eq_integral hw, x.integral_inv_one_sub_conj_mul hw]
      simp [fourierCoeff]
    _ = _ := by
      have hA' := hint.continuous_mul_of_compactSpace hA
      have hB' := hint.continuous_mul_of_compactSpace hB
      have hAB : Integrable (fun t ↦ (1 - w * conj (toCircle t : ℂ))⁻¹ *
          (x : Lp ℂ 2 (haarAddCircle (T := 1))) t + (1 - conj w * (toCircle t : ℂ))⁻¹ *
          (x : Lp ℂ 2 (haarAddCircle (T := 1))) t) haarAddCircle := hA'.add hB'
      rw [← integral_add hA' hB', ← integral_sub hAB hint]
      refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
      dsimp only
      rw [ofReal_poissonKernel_eq (z := (toCircle t : ℂ)) (by simp) hw]
      ring

/-- The Poisson integral `w ↦ ∫ P_w(t) ‖x t‖² dt` of the squared boundary modulus of a Hardy
function. On the open unit disk it is a harmonic majorant of the squared modulus of the disk
function, with value `‖x‖ ^ 2` at the origin. -/
def poissonMajorant (w : ℂ) : ℝ :=
  ∫ t, poissonKernel 0 w (toCircle t) * ‖(x : Lp ℂ 2 (haarAddCircle (T := 1))) t‖ ^ 2
    ∂haarAddCircle

/-- The Poisson majorant written as its defining integral. -/
theorem poissonMajorant_def (w : ℂ) :
    x.poissonMajorant w = ∫ t, poissonKernel 0 w (toCircle t) *
      ‖(x : Lp ℂ 2 (haarAddCircle (T := 1))) t‖ ^ 2 ∂haarAddCircle :=
  (rfl)

private theorem integrable_norm_sq :
    Integrable (fun t ↦ ‖(x : Lp ℂ 2 (haarAddCircle (T := 1))) t‖ ^ 2) haarAddCircle :=
  (Lp.memLp _).integrable_norm_pow two_ne_zero

/-- The squared modulus of the disk function is bounded by the Poisson integral of the squared
boundary modulus. -/
theorem norm_sq_diskFunction_le_poissonMajorant (hw : ‖w‖ < 1) :
    ‖x.diskFunction w‖ ^ 2 ≤ x.poissonMajorant w := by
  set f : UnitAddCircle → ℂ := ⇑(x : Lp ℂ 2 (haarAddCircle (T := 1)))
  set P : UnitAddCircle → ℝ := fun t ↦ poissonKernel 0 w (toCircle t)
  set c := x.diskFunction w
  have hP := continuous_poissonKernel_toCircle (T := 1) hw
  have hP0 (t : UnitAddCircle) : 0 ≤ P t := poissonKernel_nonneg (by simpa using hw.le)
  have hPf : Integrable (fun t ↦ (P t : ℂ) * f t) haarAddCircle :=
    x.integrable_coe.continuous_mul_of_compactSpace (continuous_ofReal.comp hP)
  have hcross : ∫ t, P t * (conj c * f t).re ∂haarAddCircle = ‖c‖ ^ 2 := by
    have h : ∫ t, P t * (conj c * f t).re ∂haarAddCircle =
        (∫ t, conj c * ((P t : ℂ) * f t) ∂haarAddCircle).re := by
      have h' := integral_re (hPf.const_mul (conj c))
      simp only [RCLike.re_to_complex] at h'
      rw [← h']
      refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
      dsimp only
      rw [mul_left_comm, re_ofReal_mul]
    rw [h, integral_const_mul, ← x.diskFunction_eq_integral_poissonKernel hw, conj_mul',
      ← ofReal_pow, ofReal_re]
  have hnonneg : 0 ≤ ∫ t, P t * ‖f t - c‖ ^ 2 ∂haarAddCircle :=
    integral_nonneg fun t ↦ mul_nonneg (hP0 t) (sq_nonneg _)
  have hexp : ∫ t, P t * ‖f t - c‖ ^ 2 ∂haarAddCircle =
      x.poissonMajorant w - 2 * ∫ t, P t * (conj c * f t).re ∂haarAddCircle +
        ‖c‖ ^ 2 * ∫ t, P t ∂haarAddCircle := by
    have h1 : Integrable (fun t ↦ P t * ‖f t‖ ^ 2) haarAddCircle :=
      x.integrable_norm_sq.continuous_mul_of_compactSpace hP
    have h2 : Integrable (fun t ↦ P t * (conj c * f t).re) haarAddCircle := by
      simpa only [RCLike.re_to_complex] using
        (x.integrable_coe.const_mul (conj c)).re.continuous_mul_of_compactSpace hP
    have h3 : Integrable P haarAddCircle :=
      hP.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h12 : Integrable (fun t ↦ P t * ‖f t‖ ^ 2 - 2 * (P t * (conj c * f t).re))
        haarAddCircle := h1.sub (h2.const_mul 2)
    rw [poissonMajorant_def,
      ← integral_const_mul, ← integral_const_mul, ← integral_sub h1 (h2.const_mul 2),
      ← integral_add h12 (h3.const_mul _)]
    refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
    simp only [P]
    rw [@norm_sub_sq ℂ, ← RCLike.re_to_complex]
    simp only [RCLike.inner_apply, RCLike.re_to_complex]
    rw [show (c * conj (f t)).re = (conj c * f t).re by rw [← conj_re, map_mul, conj_conj]]
    ring
  rw [hexp, hcross, integral_poissonKernel_toCircle hw] at hnonneg
  linarith

/-- The Poisson majorant has value `‖x‖ ^ 2` at the origin. -/
@[simp]
theorem poissonMajorant_zero : x.poissonMajorant 0 = ‖x‖ ^ 2 := by
  rw [poissonMajorant_def, ← Submodule.norm_coe, ← Lp.integral_norm_sq_eq_norm_sq]
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  simp [poissonKernel_def]

/-- On the open unit disk the Poisson majorant is the real part of the Herglotz transform of the
measure `‖x t‖ ^ 2 dt`, carried to the unit circle. -/
private theorem exists_poissonMajorant_eq_re_herglotzTransform :
    ∃ μ : Measure Circle, IsFiniteMeasure μ ∧
      ∀ w ∈ ball (0 : ℂ) 1, x.poissonMajorant w = (μ.herglotzTransform w).re := by
  set ρ : UnitAddCircle → NNReal := fun t ↦ ‖(x : Lp ℂ 2 (haarAddCircle (T := 1))) t‖₊ ^ 2
  have hρ : Measurable ρ := (Lp.stronglyMeasurable _).measurable.nnNorm.pow_const 2
  have hfin : IsFiniteMeasure (haarAddCircle.withDensity fun t ↦ (ρ t : ENNReal)) := by
    refine isFiniteMeasure_withDensity ?_
    refine ne_of_eq_of_ne (lintegral_congr fun t ↦ ?_) x.integrable_norm_sq.2.ne
    simp [ρ, eNorm_eq_nnNorm]
  refine ⟨(haarAddCircle.withDensity fun t ↦ (ρ t : ENNReal)).map toCircle, inferInstance,
    fun w hw ↦ ?_⟩
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  have hne (z : ℂ) (hz : ‖z‖ = 1) : z - w ≠ 0 :=
    sub_ne_zero.2 (ne_of_apply_ne norm (hz.trans_ne hw'.ne'))
  have hH : Continuous fun z : Circle ↦ ((z : ℂ) + w) / ((z : ℂ) - w) :=
    (continuous_subtypeVal.add continuous_const).div
      (continuous_subtypeVal.sub continuous_const) fun z ↦ hne z (Circle.norm_coe z)
  have hint : Integrable (fun t : UnitAddCircle ↦ ((toCircle t : ℂ) + w) / ((toCircle t : ℂ) - w) *
      ((‖(x : Lp ℂ 2 (haarAddCircle (T := 1))) t‖ ^ 2 : ℝ) : ℂ)) haarAddCircle :=
    x.integrable_norm_sq.ofReal.continuous_mul_of_compactSpace (hH.comp continuous_toCircle)
  rw [Measure.herglotzTransform_def, integral_map continuous_toCircle.aemeasurable
    hH.aestronglyMeasurable, integral_withDensity_eq_integral_smul hρ]
  have h := integral_re hint
  simp only [RCLike.re_to_complex] at h
  have hρ' : (fun t ↦ ρ t • (((toCircle t : ℂ) + w) / ((toCircle t : ℂ) - w))) =
      fun t ↦ ((toCircle t : ℂ) + w) / ((toCircle t : ℂ) - w) *
        ((‖(x : Lp ℂ 2 (haarAddCircle (T := 1))) t‖ ^ 2 : ℝ) : ℂ) := by
    funext t
    rw [NNReal.smul_def, real_smul, mul_comm]
    simp [ρ]
  rw [hρ', ← h, poissonMajorant_def]
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  dsimp only
  rw [re_mul_ofReal, poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply,
    herglotzRieszKernel_def]
  simp only [sub_zero]

/-- The Poisson majorant is harmonic on the open unit disk. -/
theorem harmonicOnNhd_poissonMajorant :
    InnerProductSpace.HarmonicOnNhd x.poissonMajorant (ball 0 1) := by
  obtain ⟨μ, hμ, hre⟩ := x.exists_poissonMajorant_eq_re_herglotzTransform
  intro w hw
  have hG : AnalyticAt ℂ μ.herglotzTransform w :=
    μ.differentiableOn_herglotzTransform.analyticAt (isOpen_ball.mem_nhds hw)
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 hG.harmonicAt_re
  filter_upwards [isOpen_ball.mem_nhds hw] with v hv using hre v hv

/-- The squared boundary norm `‖x‖ ^ 2` is the least value at the origin of a real harmonic
majorant of the squared modulus of the disk function, and it is attained by the Poisson
majorant. -/
theorem isLeast_harmonic_majorant_zero :
    IsLeast {c | ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧
      (∀ w ∈ ball (0 : ℂ) 1, ‖x.diskFunction w‖ ^ 2 ≤ u w) ∧ u 0 = c} (‖x‖ ^ 2) := by
  refine ⟨⟨x.poissonMajorant, x.harmonicOnNhd_poissonMajorant, fun w hw ↦
    x.norm_sq_diskFunction_le_poissonMajorant (mem_ball_zero_iff.1 hw), x.poissonMajorant_zero⟩,
    ?_⟩
  rintro _ ⟨u, hu, hmaj, rfl⟩
  exact x.norm_sq_le_harmonic_majorant_zero hu hmaj

/-! ### Holomorphic functions with a harmonic majorant -/

variable {F : ℂ → ℂ}

/-- A holomorphic function on the open unit disk is the sum there of its Taylor series at the
origin, with coefficients `aₙ = iteratedDeriv n F 0 / n!`. -/
private theorem hasSum_taylorCoeff_mul_pow (hF : DifferentiableOn ℂ F (ball 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    HasSum (fun n ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0 * z ^ n) (F z) := by
  convert Complex.hasSum_taylorSeries_on_ball hF hz using 2 with n
  simp only [sub_zero, smul_eq_mul]
  ring

/-- For `0 < r < 1`, the dilation `w ↦ F (r * w)` of a holomorphic function on the open unit disk
is the disk function of the Hardy function with coefficients `aₙ * r ^ n`, where `aₙ` are the
Taylor coefficients of `F` at the origin: these decay geometrically. -/
private theorem exists_diskFunction_eq_comp_mul (hF : DifferentiableOn ℂ F (ball 0 1)) {r : ℝ}
    (hr₀ : 0 < r) (hr₁ : r < 1) :
    ∃ y : HardySpace, (∀ w ∈ ball (0 : ℂ) 1, y.diskFunction w = F (r * w)) ∧
      ∀ n, hardyBasis.repr y n = (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0 * (r : ℂ) ^ n := by
  set a : ℕ → ℂ := fun n ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0
  -- The terms `aₙ ρ ^ n` of the Taylor series at a radius `ρ ∈ (r, 1)` are bounded.
  set ρ : ℝ := (1 + r) / 2
  have hρ₀ : 0 < ρ := by positivity
  have hrρ : r < ρ := by simp only [ρ]; linarith
  obtain ⟨C, hC⟩ : BddAbove (Set.range fun n ↦ ‖a n * (ρ : ℂ) ^ n‖) :=
    (hasSum_taylorCoeff_mul_pow hF (by
      rw [mem_ball_zero_iff, norm_real, Real.norm_of_nonneg hρ₀.le]
      simp only [ρ]
      linarith)).summable.tendsto_atTop_zero.norm.bddAbove_range
  have hb (n : ℕ) : ‖a n * (r : ℂ) ^ n‖ ^ 2 ≤ C ^ 2 * ((r / ρ) ^ 2) ^ n := by
    have h : ‖a n * (r : ℂ) ^ n‖ = ‖a n * (ρ : ℂ) ^ n‖ * (r / ρ) ^ n := by
      simp only [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hr₀.le,
        Real.norm_of_nonneg hρ₀.le, div_pow]
      field_simp
    rw [h, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    gcongr
    exact hC ⟨n, rfl⟩
  have hsum : Summable fun n ↦ ‖a n * (r : ℂ) ^ n‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun _ ↦ by positivity) hb
      ((summable_geometric_of_lt_one (by positivity) (by
        rw [div_pow, div_lt_one (by positivity)]; gcongr)).mul_left _)
  refine ⟨hardyBasis.repr.symm ⟨fun n ↦ a n * (r : ℂ) ^ n, memℓp_gen (by simpa using hsum)⟩,
    fun w hw ↦ ?_, fun n ↦ by simp [a]⟩
  have hrw : (r : ℂ) * w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_of_nonneg hr₀.le]
    nlinarith [mem_ball_zero_iff.1 hw, norm_nonneg w]
  rw [diskFunction_hardyBasis_repr_symm]
  refine ((hasSum_taylorCoeff_mul_pow hF hrw).congr_fun fun n ↦ ?_).tsum_eq
  simp only [a, mul_pow, mul_assoc]

/-- For `0 < r < 1`, the Taylor coefficients `aₙ` at the origin of a holomorphic function on the
unit disk with a harmonic majorant `u` of `‖F‖ ^ 2` satisfy `∑ n, ‖aₙ‖ ^ 2 * r ^ (2 * n) ≤ u 0`:
the left side is the squared norm of the Hardy function whose disk function is `w ↦ F (r * w)`. -/
private theorem sum_range_norm_sq_taylorCoeff_mul_le (hF : DifferentiableOn ℂ F (ball 0 1))
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1))
    (hmajor : ∀ w ∈ ball (0 : ℂ) 1, ‖F w‖ ^ 2 ≤ u w) {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1)
    (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖(n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0‖ ^ 2 * r ^ (2 * n) ≤
      u 0 := by
  obtain ⟨y, hy, hrepr⟩ := exists_diskFunction_eq_comp_mul hF hr₀ hr₁
  -- The squared circle means of `F_y` are those of `F` on smaller circles.
  have hmean : ∀ᶠ s : ℝ in 𝓝[<] 1,
      Real.circleAverage (fun w ↦ ‖y.diskFunction w‖ ^ 2) 0 s ≤ u 0 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with s hs
    have hs' : |s| < 1 := abs_lt.2 hs
    have hrs : |r * s| < 1 := by
      rw [abs_mul, abs_of_pos hr₀]; nlinarith [abs_nonneg s]
    have hsub : closedBall (0 : ℂ) |r * s| ⊆ ball 0 1 := closedBall_subset_ball hrs
    refine le_of_eq_of_le ?_
      (circleAverage_le_of_harmonic_majorant (g := fun w ↦ ‖F w‖ ^ 2)
        ((hF.continuousOn.norm.pow 2).mono (sphere_subset_closedBall.trans hsub)).circleIntegrable'
        (hu.mono hsub) fun w hw ↦ hmajor w (hsub (sphere_subset_closedBall hw)))
    rw [Real.circleAverage_eq_circleAverage_zero_one,
      Real.circleAverage_eq_circleAverage_zero_one (c := 0) (R := r * s)]
    refine Real.circleAverage_congr_sphere fun z hz ↦ ?_
    have hsz : (s : ℂ) * z + 0 ∈ ball (0 : ℂ) 1 := by
      rw [add_zero, mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs,
        show ‖z‖ = 1 by simpa using hz, mul_one]
      exact hs'
    rw [hy _ hsz]
    push_cast
    ring_nf
  have hy_le := le_of_tendsto y.tendsto_circleAverage_norm_sq_diskFunction hmean
  rw [← hardyBasis.tsum_norm_inner_sq y] at hy_le
  simp only [← HilbertBasis.repr_apply_apply] at hy_le
  have hsum : Summable fun n ↦ ‖hardyBasis.repr y n‖ ^ 2 := by
    simpa only [← HilbertBasis.repr_apply_apply] using hardyBasis.summable_norm_inner_sq y
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun n _ ↦ ?_))
    ((hsum.sum_le_tsum _ fun n _ ↦ by positivity).trans hy_le)
  rw [hrepr]
  simp only [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hr₀.le]
  ring

/-- **Holomorphic functions with a harmonic majorant come from `H²`.** A holomorphic function on
the open unit disk whose squared modulus has a real harmonic majorant `u` is the disk function of a
Hardy function `x` with `‖x‖ ^ 2 ≤ u 0`. -/
theorem exists_eqOn_diskFunction_of_harmonic_majorant (hF : DifferentiableOn ℂ F (ball 0 1))
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1))
    (hmajor : ∀ w ∈ ball (0 : ℂ) 1, ‖F w‖ ^ 2 ≤ u w) :
    ∃ x : HardySpace, Set.EqOn F x.diskFunction (ball 0 1) ∧ ‖x‖ ^ 2 ≤ u 0 := by
  set a : ℕ → ℂ := fun n ↦ (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0
  -- Letting `r → 1⁻` in the dilated bounds controls every partial sum of `∑ ‖aₙ‖ ^ 2`.
  have hpartial (N : ℕ) : ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 ≤ u 0 := by
    have hcont : Continuous fun r : ℝ ↦ ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * r ^ (2 * n) := by
      fun_prop
    have hlim : Tendsto (fun r : ℝ ↦ ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * r ^ (2 * n)) (𝓝[<] 1)
        (𝓝 (∑ n ∈ Finset.range N, ‖a n‖ ^ 2)) := by
      simpa using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
    exact sum_range_norm_sq_taylorCoeff_mul_le hF hu hmajor hr.1 hr.2 N
  have hsum : Summable fun n ↦ ‖a n‖ ^ 2 :=
    summable_of_sum_range_le (fun _ ↦ by positivity) hpartial
  refine ⟨hardyBasis.repr.symm ⟨a, memℓp_gen (by simpa using hsum)⟩, fun w hw ↦ ?_, ?_⟩
  · rw [diskFunction_hardyBasis_repr_symm]
    exact (hasSum_taylorCoeff_mul_pow hF hw).tsum_eq.symm
  · rw [← hardyBasis.tsum_norm_inner_sq]
    simp only [← HilbertBasis.repr_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    exact Real.tsum_le_of_sum_range_le (fun _ ↦ by positivity) hpartial

/-- **The harmonic-majorant description of `H²`.** A function on the open unit disk is the disk
function of a Hardy function exactly when it is holomorphic there and its squared modulus has a
real harmonic majorant. -/
theorem exists_eqOn_diskFunction_iff :
    (∃ x : HardySpace, Set.EqOn F x.diskFunction (ball 0 1)) ↔
      DifferentiableOn ℂ F (ball 0 1) ∧ ∃ u : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd u (ball 0 1) ∧ ∀ w ∈ ball (0 : ℂ) 1, ‖F w‖ ^ 2 ≤ u w := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x.differentiableOn_diskFunction.congr hx, x.poissonMajorant,
    x.harmonicOnNhd_poissonMajorant, fun w hw ↦ ?_⟩, fun ⟨hF, u, hu, hmajor⟩ ↦ ?_⟩
  · rw [hx hw]
    exact x.norm_sq_diskFunction_le_poissonMajorant (mem_ball_zero_iff.1 hw)
  · obtain ⟨x, hx, -⟩ := exists_eqOn_diskFunction_of_harmonic_majorant hF hu hmajor
    exact ⟨x, hx⟩

end TauCeti.HardySpace
