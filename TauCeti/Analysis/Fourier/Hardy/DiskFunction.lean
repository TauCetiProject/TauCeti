/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Normed.Group.Tannery
public import TauCeti.Analysis.Fourier.Hardy.Basic

/-!
# The holomorphic disk function of a Hardy function

A boundary Hardy function `x`, with Fourier coefficients `x̂ n`, defines the power series
`F_x w = ∑ n, x̂ n * w ^ n` on the open unit disk. Because the coefficients are square summable,
they are bounded by `‖x‖`, so the series converges on the whole disk.

## Main results

* `TauCeti.HardySpace.diskFunction`: the function `F_x`.
* `TauCeti.HardySpace.hasFPowerSeriesOnBall_diskFunction`: `F_x` is the sum of its Taylor series
  on the unit disk; in particular it is holomorphic there
  (`TauCeti.HardySpace.differentiableOn_diskFunction`) and the partial sums converge locally
  uniformly (`TauCeti.HardySpace.tendstoLocallyUniformlyOn_diskFunction`).
* `TauCeti.HardySpace.norm_diskFunction_le`: the pointwise bound
  `‖F_x w‖ ≤ ‖x‖ / √(1 - ‖w‖ ^ 2)`, from the Cauchy–Schwarz inequality in `ℓ²`.
* `TauCeti.HardySpace.tendsto_eLpNorm_diskFunction_sub`: the circle restrictions
  `t ↦ F_x (r * e (t))` converge to `x` in `L²` as `r → 1⁻`.

## References

* J. B. Conway, *A Course in Functional Analysis*, second edition.
* P. L. Duren, *Theory of Hᵖ Spaces*, chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped ENNReal InnerProductSpace

namespace TauCeti

namespace HardySpace

variable (x : HardySpace) {w : ℂ}

/-- The holomorphic function `w ↦ ∑ n, x̂ n * w ^ n` on the unit disk determined by a boundary
Hardy function `x`, where `x̂ n` is its `n`-th Fourier coefficient. Outside the open unit disk
the value is a junk value. -/
def diskFunction (w : ℂ) : ℂ :=
  ∑' n : ℕ, fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n * w ^ n

/-- The disk function is the coefficient series `∑' n, x̂ n * w ^ n` at every point. -/
theorem diskFunction_def (w : ℂ) :
    x.diskFunction w =
      ∑' n : ℕ, fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n * w ^ n :=
  (rfl)

/-- The Taylor series of the disk function converges absolutely on the open unit disk. -/
theorem summable_norm_fourierCoeff_mul_pow (hw : ‖w‖ < 1) :
    Summable fun n : ℕ =>
      ‖fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n * w ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg w) hw).mul_left ‖x‖)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (x.norm_fourierCoeff_le n) (by positivity)

/-- On the open unit disk the disk function is the sum of its Taylor series. -/
theorem hasSum_diskFunction (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ =>
      fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n * w ^ n)
      (x.diskFunction w) :=
  (x.summable_norm_fourierCoeff_mul_pow hw).of_norm.hasSum

/-- The value of the disk function at the origin is the zeroth Fourier coefficient. -/
@[simp]
theorem diskFunction_apply_zero :
    x.diskFunction 0 = fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) 0 := by
  rw [diskFunction, tsum_eq_single 0 (fun n hn => by simp [hn])]
  simp

/-- The disk function of the `n`-th Hardy basis vector is the monomial `w ^ n`. -/
@[simp]
theorem diskFunction_hardyBasis (n : ℕ) (w : ℂ) : (hardyBasis n).diskFunction w = w ^ n := by
  rw [diskFunction, tsum_eq_single n fun m hm => by
    rw [← hardyBasis_repr, HilbertBasis.repr_self, lp.single_apply, Pi.single_eq_of_ne hm,
      zero_mul]]
  rw [← hardyBasis_repr, HilbertBasis.repr_self, lp.single_apply, Pi.single_eq_same, one_mul]

/-- On the open unit disk the disk function depends additively on the Hardy function. -/
theorem diskFunction_add (y : HardySpace) (hw : ‖w‖ < 1) :
    (x + y).diskFunction w = x.diskFunction w + y.diskFunction w := by
  refine ((x + y).hasSum_diskFunction hw).unique ?_
  have h := (x.hasSum_diskFunction hw).add (y.hasSum_diskFunction hw)
  simp only [← hardyBasis_repr, ← add_mul] at h
  simpa only [← hardyBasis_repr, map_add, lp.coeFn_add, Pi.add_apply] using h

/-- On the open unit disk the disk function depends linearly on the Hardy function. -/
theorem diskFunction_smul (c : ℂ) (hw : ‖w‖ < 1) :
    (c • x).diskFunction w = c * x.diskFunction w := by
  refine ((c • x).hasSum_diskFunction hw).unique ?_
  have h := (x.hasSum_diskFunction hw).mul_left c
  simp only [← hardyBasis_repr, ← mul_assoc] at h
  simpa only [← hardyBasis_repr, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] using h

/-- The coefficient series of the disk function, as a formal power series in one variable. -/
private abbrev diskSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun n : ℕ =>
    fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n

/-- The Taylor series of the disk function has radius of convergence at least one. -/
private theorem one_le_radius_diskSeries : 1 ≤ x.diskSeries.radius := by
  have h := x.diskSeries.le_radius_of_bound ‖x‖ (r := 1) fun n => by
    rw [NNReal.coe_one, one_pow, mul_one, FormalMultilinearSeries.ofScalars_norm]
    exact x.norm_fourierCoeff_le n
  simpa using h

/-- The disk function is the sum of its Taylor series on the open unit disk. -/
theorem hasFPowerSeriesOnBall_diskFunction :
    HasFPowerSeriesOnBall x.diskFunction
      (FormalMultilinearSeries.ofScalars ℂ fun n : ℕ =>
        fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n) 0 1 := by
  have h := (x.diskSeries.hasFPowerSeriesOnBall
    (zero_lt_one.trans_le x.one_le_radius_diskSeries)).mono zero_lt_one
    x.one_le_radius_diskSeries
  have hsum : x.diskSeries.sum = x.diskFunction := by
    funext w
    rw [FormalMultilinearSeries.sum, diskFunction]
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rwa [hsum] at h

/-- The disk function is analytic on the open unit disk. -/
theorem analyticOnNhd_diskFunction : AnalyticOnNhd ℂ x.diskFunction (Metric.ball 0 1) := by
  intro w hw
  have h := x.hasFPowerSeriesOnBall_diskFunction.analyticAt_of_mem
    (y := w) (by simpa [← ENNReal.coe_one, Metric.eball_coe] using hw)
  simpa using h

/-- The disk function is holomorphic on the open unit disk. -/
theorem differentiableOn_diskFunction : DifferentiableOn ℂ x.diskFunction (Metric.ball 0 1) :=
  x.analyticOnNhd_diskFunction.differentiableOn

/-- The partial sums of the Taylor series converge to the disk function locally uniformly on
the open unit disk. -/
theorem tendstoLocallyUniformlyOn_diskFunction :
    TendstoLocallyUniformlyOn (fun N (w : ℂ) => ∑ n ∈ Finset.range N,
      fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n * w ^ n)
      x.diskFunction atTop (Metric.ball 0 1) := by
  have h := x.hasFPowerSeriesOnBall_diskFunction.tendstoLocallyUniformlyOn
  simpa [← ENNReal.coe_one, Metric.eball_coe, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using h

/-- The pointwise bound `‖F_x w‖ ≤ ‖x‖ / √(1 - ‖w‖ ^ 2)` on the open unit disk, obtained by
pairing the coefficient sequence of `x` with the square-summable sequence `(conj w ^ n)` in `ℓ²`. -/
theorem norm_diskFunction_le (hw : ‖w‖ < 1) :
    ‖x.diskFunction w‖ ≤ ‖x‖ / √(1 - ‖w‖ ^ 2) := by
  have hw2 : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
  have hgeom : Summable fun n : ℕ => (‖w‖ ^ 2) ^ n :=
    summable_geometric_of_lt_one (by positivity) hw2
  have hpow (n : ℕ) : ‖(starRingEnd ℂ w) ^ n‖ ^ 2 = (‖w‖ ^ 2) ^ n := by
    rw [norm_pow, Complex.norm_conj, ← pow_mul, ← pow_mul, mul_comm]
  let k : lp (fun _ : ℕ => ℂ) 2 := ⟨fun n => (starRingEnd ℂ w) ^ n, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, hpow] using hgeom)⟩
  have hk : ‖k‖ ^ 2 = (1 - ‖w‖ ^ 2)⁻¹ := by
    have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) k
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    rw [h, ← tsum_geometric_of_lt_one (by positivity) hw2]
    exact tsum_congr hpow
  have hinner : ⟪k, hardyBasis.repr x⟫_ℂ = x.diskFunction w := by
    rw [lp.inner_eq_tsum, diskFunction]
    congr 1
    funext n
    simp [k, hardyBasis_repr, mul_comm]
  have hpos : 0 < 1 - ‖w‖ ^ 2 := sub_pos.mpr hw2
  have hknorm : ‖k‖ = (√(1 - ‖w‖ ^ 2))⁻¹ := by
    rw [← Real.sqrt_inv, ← hk, Real.sqrt_sq (norm_nonneg k)]
  calc ‖x.diskFunction w‖ = ‖⟪k, hardyBasis.repr x⟫_ℂ‖ := by rw [hinner]
    _ ≤ ‖k‖ * ‖hardyBasis.repr x‖ := norm_inner_le_norm _ _
    _ = ‖x‖ / √(1 - ‖w‖ ^ 2) := by
      rw [LinearIsometryEquiv.norm_map, hknorm, div_eq_mul_inv, mul_comm]

/-! ### Radial approximation in `L²` -/

section Radial

variable {r : ℝ}

/-- The coefficients of the radial dilation `x_r = ∑ n, r ^ n x̂ n e_n`. -/
private abbrev radialCoeff (r : ℝ) (n : ℕ) : ℂ :=
  (r : ℂ) ^ n * fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n

private theorem norm_radialCoeff_le (n : ℕ) :
    ‖x.radialCoeff r n‖ ≤ ‖x‖ * |r| ^ n := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (x.norm_fourierCoeff_le n) (by positivity)

private theorem summable_radialCoeff (hr : |r| < 1) :
    Summable fun n : ℕ => ‖x‖ * |r| ^ n :=
  (summable_geometric_of_lt_one (abs_nonneg r) hr).mul_left ‖x‖

/-- The radial dilation `x_r = ∑ n, r ^ n x̂ n e_n` of a Hardy function. -/
private def radial (r : ℝ) : HardySpace :=
  ∑' n : ℕ, x.radialCoeff r n • hardyBasis n

private theorem summable_radial (hr : |r| < 1) :
    Summable fun n : ℕ => x.radialCoeff r n • hardyBasis n := by
  refine Summable.of_norm_bounded (x.summable_radialCoeff hr) fun n => ?_
  rw [norm_smul, hardyBasis.orthonormal.1 n, mul_one]
  exact x.norm_radialCoeff_le n

private theorem hardyBasis_repr_radial (hr : |r| < 1) (n : ℕ) :
    hardyBasis.repr (x.radial r) n = x.radialCoeff r n := by
  rw [HilbertBasis.repr_apply_apply, radial,
    ← innerSL_apply_apply ℂ, ContinuousLinearMap.map_tsum _ (x.summable_radial hr),
    tsum_eq_single n fun m hm => by
      rw [innerSL_apply_apply, inner_smul_right (𝕜 := ℂ) (E := HardySpace),
        (orthonormal_iff_ite.mp hardyBasis.orthonormal n m).trans (ite_eq_right (Ne.symm hm)),
        mul_zero]]
  rw [innerSL_apply_apply, inner_smul_right (𝕜 := ℂ) (E := HardySpace),
    inner_self_eq_one_of_norm_eq_one (hardyBasis.orthonormal.1 n), mul_one]

/-- The radial dilation is represented by the continuous function `t ↦ F_x (r * e (t))`. -/
private theorem coe_radial_ae_eq (hr : |r| < 1) :
    (x.radial r : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =ᵐ[AddCircle.haarAddCircle]
      fun t => x.diskFunction (r * AddCircle.toCircle t) := by
  let g : ℕ → C(UnitAddCircle, ℂ) := fun n => x.radialCoeff r n • fourier (n : ℤ)
  have hg : Summable g := by
    refine Summable.of_norm_bounded (x.summable_radialCoeff hr) fun n => ?_
    rw [norm_smul, fourier_norm, mul_one]
    exact x.norm_radialCoeff_le n
  have hcoe : (x.radial r : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (∑' n, g n) := by
    rw [radial, ← hardySubmodule.subtypeL_apply, ContinuousLinearMap.map_tsum _
      (x.summable_radial hr), ContinuousLinearMap.map_tsum _ hg]
    congr 1
    funext n
    simp [g, coe_fourierBasis]
  rw [hcoe]
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
    (∑' n, g n)] with t ht
  rw [ht]
  refine (ContinuousMap.tsum_apply hg t).symm.trans ?_
  rw [diskFunction]
  congr 1
  funext n
  simp only [g, radialCoeff, ContinuousMap.smul_apply, smul_eq_mul, fourier_apply,
    natCast_zsmul, AddCircle.toCircle_nsmul, Circle.coe_pow]
  ring

/-- The radial dilations converge to the Hardy function as `r → 1⁻`. -/
private theorem tendsto_radial : Tendsto x.radial (𝓝[<] 1) (𝓝 x) := by
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 ≤ r ∧ r < 1 :=
    eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)) fun r hr => ⟨hr.1.le, hr.2⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun r => ‖x.radial r - x‖ ^ 2) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[<] (1 : ℝ))
      (f := fun r (n : ℕ) => ‖((r : ℂ) ^ n - 1) *
        fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n‖ ^ 2)
      (g := fun _ => 0)
      (bound := fun n : ℕ => ‖hardyBasis.repr x n‖ ^ 2) ?_ ?_ ?_
    · rw [tsum_zero] at hdom
      refine hdom.congr' ?_
      filter_upwards [hev] with r hr
      have hr' : |r| < 1 := abs_lt.mpr ⟨by linarith [hr.1], hr.2⟩
      have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (hardyBasis.repr (x.radial r - x))
      rw [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] at h
      rw [h]
      congr 1
      funext n
      rw [Real.rpow_two, map_sub, lp.coeFn_sub, Pi.sub_apply, x.hardyBasis_repr_radial hr',
        hardyBasis_repr, radialCoeff, sub_one_mul]
    · simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp (hardyBasis.repr x)).summable (by norm_num)
    · intro n
      have hc : Continuous fun r : ℝ => ‖((r : ℂ) ^ n - 1) *
          fourierCoeff (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) n‖ ^ 2 := by
        fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [hev] with r hr n
      rw [norm_pow, norm_norm, hardyBasis_repr, norm_mul]
      have h1 : ‖(r : ℂ) ^ n - 1‖ ≤ 1 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [pow_le_one₀ hr.1 hr.2.le (n := n), pow_nonneg hr.1 n]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hroot := hsq.sqrt
  simpa only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hroot

/-- The circle restrictions `t ↦ F_x (r * e (t))` of the disk function converge to the boundary
function `x` in `L²` as `r → 1⁻`. -/
theorem tendsto_eLpNorm_diskFunction_sub :
    Tendsto (fun r : ℝ => eLpNorm (fun t => x.diskFunction (r * AddCircle.toCircle t) -
      (x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) t) 2 AddCircle.haarAddCircle)
      (𝓝[<] 1) (𝓝 0) := by
  have hlim : Tendsto (fun r => ‖((x.radial r - x : HardySpace) :
      Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))‖ₑ) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    have h := ((continuous_enorm.comp continuous_subtype_val).tendsto 0).comp
      (tendsto_sub_nhds_zero_iff.mpr x.tendsto_radial)
    simpa [Function.comp_def] using h
  refine hlim.congr' ?_
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), |r| < 1 :=
    eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)) fun r hr => abs_lt.mpr hr
  filter_upwards [hev] with r hr
  rw [Lp.enorm_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (x.radial r : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) x,
    x.coe_radial_ae_eq hr] with t ht hrad
  rw [Submodule.coe_sub, ht, Pi.sub_apply, hrad]

end Radial

end HardySpace

end TauCeti
