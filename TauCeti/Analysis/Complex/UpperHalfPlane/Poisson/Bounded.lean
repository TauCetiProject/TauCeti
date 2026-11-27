/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Function
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.PositiveHarmonic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.VagueLimit
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity
import TauCeti.MeasureTheory.Measure.Decomposition.RNDeriv
import TauCeti.MeasureTheory.Measure.Vague

/-!
# Bounded harmonic and holomorphic functions on the upper half-plane are Poisson integrals

A bounded harmonic function `u` on the upper half-plane `ℂ₊` is the Poisson integral of a bounded
measurable function on `ℝ`: if `|u| ≤ S` on `ℂ₊`, there is a measurable `w : ℝ → ℝ` with `|w| ≤ S`
and `u(z) = ∫ P(z, x) w(x) dx` on `ℂ₊`
(`TauCeti.exists_eq_integral_upperHalfPlanePoissonKernel_mul_of_abs_le`). Applied to the real and
imaginary parts, a bounded holomorphic function `F` on `ℂ₊` is the Poisson integral `P[w]` of a
bounded measurable `w : ℝ → ℂ` (`TauCeti.exists_eq_upperHalfPlanePoissonIntegralFun_of_norm_le`).
Thus every bounded holomorphic `F` is the Poisson integral of some bounded measurable boundary
density; identifying this density with the nontangential limit `F*`, which would give
`F = P[F*]`, needs Fatou's theorem and is not proved here.

The proof goes through the representation of nonnegative harmonic functions,
`TauCeti.exists_eq_mul_im_add_upperHalfPlanePoissonIntegral`. The function `v = u + S` is harmonic
and takes values in `[0, 2S]`, so `v = c Im z + P[ν]` with `c ≥ 0` and `ν` Poisson-finite.

* `c = 0`, since `c = lim v(iy) / y`
  (`TauCeti.tendsto_div_of_eq_mul_im_add_upperHalfPlanePoissonIntegral`) and
  `0 ≤ v(iy) / y ≤ 2S / y`.
* `ν ≤ 2S · dx`: `ν` is the vague limit of the measures `v(x + iy) dx`
  (`TauCeti.tendsto_integral_mul_of_eq_mul_im_add_upperHalfPlanePoissonIntegral`), whose densities
  are at most `2S`, so `ν(K) ≤ 2S |V|` for every compact `K` and open `V ⊇ K`
  (`IsCompact.measure_le_of_tendsto_integral`), hence `ν(K) ≤ 2S |K|` by outer regularity, and
  `ν(A) ≤ 2S |A|` for every Borel `A` by inner regularity of `ν`.
* Hence `ν = h dx` with `0 ≤ h ≤ 2S` (the Radon–Nikodym derivative of `ν`,
  `MeasureTheory.Measure.exists_eq_withDensity_of_le_smul`), and
  `u = P[h] - S = P[h - S]` since the Poisson kernel has integral `1`.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §3.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Set Topology InnerProductSpace
open UpperHalfPlane (upperHalfPlaneSet)
open scoped Real NNReal ENNReal CompactlySupported

namespace TauCeti

variable {v : ℂ → ℝ} {M c : ℝ} {ν : Measure ℝ}

/-- A point `y i` of the imaginary axis with `y > 0` lies in the upper half-plane. -/
private theorem mul_I_mem_upperHalfPlaneSet {y : ℝ} (hy : 0 < y) :
    (y : ℂ) * I ∈ upperHalfPlaneSet := by
  simpa using hy

/-- A point `x + y i` with `y > 0` lies in the upper half-plane. -/
private theorem add_mul_I_mem_upperHalfPlaneSet (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (x : ℂ) + y * I ∈ upperHalfPlaneSet := by
  simpa using hy

/-- If `v = c Im + P[ν]` is bounded on `ℂ₊`, the linear coefficient `c` vanishes. -/
private theorem coeff_eq_zero_of_le
    (hrep : ∀ z ∈ upperHalfPlaneSet, v z = c * z.im + upperHalfPlanePoissonIntegral ν z)
    (hv : ∀ z ∈ upperHalfPlaneSet, 0 ≤ v z ∧ v z ≤ M) : c = 0 := by
  have h := tendsto_div_of_eq_mul_im_add_upperHalfPlanePoissonIntegral hrep
  have hM : Tendsto (fun y : ℝ ↦ M / y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine tendsto_nhds_unique h (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM
    ?_ ?_)
  · filter_upwards [eventually_gt_atTop 0] with y hy
    exact div_nonneg (hv _ (mul_I_mem_upperHalfPlaneSet hy)).1 hy.le
  · filter_upwards [eventually_gt_atTop 0] with y hy
    exact div_le_div_of_nonneg_right (hv _ (mul_I_mem_upperHalfPlaneSet hy)).2 hy.le

/-- If `v = c Im + P[ν]` takes values in `[0, M]` on `ℂ₊`, then `ν(K) ≤ M |K|` for every compact
`K`. -/
private theorem measure_le_of_isCompact (hu : HarmonicOnNhd v upperHalfPlaneSet)
    (hν : IsPoissonFinite ν)
    (hrep : ∀ z ∈ upperHalfPlaneSet, v z = c * z.im + upperHalfPlanePoissonIntegral ν z)
    (hv : ∀ z ∈ upperHalfPlaneSet, 0 ≤ v z ∧ v z ≤ M) {K : Set ℝ} (hK : IsCompact K) :
    ν K ≤ ENNReal.ofReal M * volume K := by
  have := hν.isFiniteMeasureOnCompacts
  -- The measures `v(x + iy) dx`.
  set σ : ℝ → Measure ℝ := fun y ↦ volume.withDensity fun x ↦ ENNReal.ofReal (v (x + y * I))
  have hcont {y : ℝ} (hy : 0 < y) : Continuous fun x : ℝ ↦ v (x + y * I) :=
    hu.continuousOn.comp_continuous (by fun_prop) fun x ↦ add_mul_I_mem_upperHalfPlaneSet x hy
  have hlim (f : C_c(ℝ, ℝ)) :
      Tendsto (fun y ↦ ∫ x, f x ∂σ y) (𝓝[>] 0) (𝓝 (∫ x, f x ∂ν)) := by
    refine (tendsto_integral_mul_of_eq_mul_im_add_upperHalfPlanePoissonIntegral hν hrep
      f.continuous f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    rw [TauCeti.MeasureTheory.integral_withDensity_ofReal (hcont hy).aemeasurable
      (.of_forall fun x ↦ (hv _ (add_mul_I_mem_upperHalfPlaneSet x hy)).1)]
    simp_rw [smul_eq_mul]
    exact integral_congr_ae (.of_forall fun x ↦ mul_comm _ _)
  have hbound {V : Set ℝ} (hV : IsOpen V) :
      ∀ᶠ y in 𝓝[>] (0 : ℝ), σ y V ≤ ENNReal.ofReal M * volume V := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    rw [withDensity_apply _ hV.measurableSet, ← setLIntegral_const]
    exact setLIntegral_mono measurable_const fun x _ ↦
      ENNReal.ofReal_le_ofReal (hv _ (add_mul_I_mem_upperHalfPlaneSet x hy)).2
  -- Outer regularity of Lebesgue measure.
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hMε : 0 < (ε : ℝ≥0∞) / (ENNReal.ofReal M + 1) :=
    ENNReal.div_pos (by simpa using hε.ne') (by simp)
  obtain ⟨V, hKV, hV, hVlt⟩ := hK.measure_lt_top.ne |> fun h ↦
    Set.exists_isOpen_lt_of_lt K (volume K + ε / (ENNReal.ofReal M + 1))
      (ENNReal.lt_add_right h hMε.ne')
  refine (hK.measure_le_of_tendsto_integral hV hKV (hbound hV) hlim).trans ?_
  calc ENNReal.ofReal M * volume V
      ≤ ENNReal.ofReal M * (volume K + ε / (ENNReal.ofReal M + 1)) := by gcongr
    _ ≤ ENNReal.ofReal M * volume K + ε := by
      rw [mul_add]
      gcongr
      calc ENNReal.ofReal M * (ε / (ENNReal.ofReal M + 1))
          ≤ (ENNReal.ofReal M + 1) * (ε / (ENNReal.ofReal M + 1)) := by gcongr; simp
        _ = ε := ENNReal.mul_div_cancel (by simp) (by simp)

/-- **Bounded harmonic functions are Poisson integrals.** If `u` is harmonic on the upper
half-plane with `|u| ≤ S` there, then `u(z) = ∫ P(z, x) w(x) dx` on `ℂ₊` for a measurable
`w : ℝ → ℝ` with `|w| ≤ S`. -/
theorem exists_eq_integral_upperHalfPlanePoissonKernel_mul_of_abs_le {u : ℂ → ℝ} {S : ℝ}
    (hu : HarmonicOnNhd u upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, |u z| ≤ S) :
    ∃ w : ℝ → ℝ, Measurable w ∧ (∀ x, |w x| ≤ S) ∧
      ∀ z ∈ upperHalfPlaneSet, u z = ∫ x, upperHalfPlanePoissonKernel z x * w x := by
  -- `v = u + S` is harmonic with values in `[0, 2S]`.
  set v : ℂ → ℝ := fun z ↦ u z + S
  have hvh : HarmonicOnNhd v upperHalfPlaneSet := hu.add (harmonicOnNhd_const S)
  have hv (z : ℂ) (hz : z ∈ upperHalfPlaneSet) : 0 ≤ v z ∧ v z ≤ 2 * S := by
    have := abs_le.1 (hS z hz)
    constructor <;> simp only [v] <;> linarith
  obtain ⟨c, ν, -, hν, hrep⟩ :=
    exists_eq_mul_im_add_upperHalfPlanePoissonIntegral hvh fun z hz ↦ (hv z hz).1
  obtain rfl := coeff_eq_zero_of_le hrep hv
  have := hν.isFiniteMeasureOnCompacts
  -- `ν ≤ 2S · dx`.
  have hle : ν ≤ ENNReal.ofReal (2 * S) • volume := by
    refine Measure.le_iff.2 fun A hA ↦ ?_
    rw [hA.measure_eq_iSup_isCompact ν, smul_apply, smul_eq_mul]
    refine iSup₂_le fun K hKA ↦ iSup_le fun hK ↦ ?_
    exact (measure_le_of_isCompact hvh hν hrep hv hK).trans (by gcongr)
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS I (by simp))
  obtain ⟨h, hmeas, hh0, hh1, hνh⟩ := Measure.exists_eq_withDensity_of_le_smul (by linarith) hle
  refine ⟨fun x ↦ h x - S, hmeas.sub measurable_const, fun x ↦ ?_, fun z hz ↦ ?_⟩
  · have h0 := hh0 x
    have h1 := hh1 x
    rw [abs_le]
    constructor <;> linarith
  · have hz' : 0 < z.im := hz
    have hint : Integrable (upperHalfPlanePoissonKernel z) :=
      isPoissonFinite_volume.integrable_upperHalfPlanePoissonKernel z
    have hhint : Integrable fun x ↦ upperHalfPlanePoissonKernel z x * h x := by
      refine hint.mul_bdd hmeas.aestronglyMeasurable (c := 2 * S) (.of_forall fun x ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x)]
      exact hh1 x
    have hPν : upperHalfPlanePoissonIntegral ν z = ∫ x, upperHalfPlanePoissonKernel z x * h x := by
      rw [upperHalfPlanePoissonIntegral_def, hνh, TauCeti.MeasureTheory.integral_withDensity_ofReal
        hmeas.aemeasurable (.of_forall hh0)]
      simp_rw [smul_eq_mul]
      exact integral_congr_ae (.of_forall fun x ↦ mul_comm _ _)
    have hu' : u z = v z - S := by simp [v]
    rw [hu', hrep z hz, zero_mul, zero_add, hPν]
    simp_rw [mul_sub]
    rw [integral_sub hhint (hint.mul_const S), integral_mul_const,
      integral_upperHalfPlanePoissonKernel hz', one_mul]

/-- **Bounded holomorphic functions are Poisson integrals.** If `F` is holomorphic on the upper
half-plane with `‖F‖ ≤ S` there, then `F = P[w]` on `ℂ₊` for a measurable `w : ℝ → ℂ` whose real
and imaginary parts are bounded by `S`. -/
theorem exists_eq_upperHalfPlanePoissonIntegralFun_of_norm_le {F : ℂ → ℂ} {S : ℝ}
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) :
    ∃ w : ℝ → ℂ, Measurable w ∧ (∀ x, |(w x).re| ≤ S ∧ |(w x).im| ≤ S) ∧
      ∀ z ∈ upperHalfPlaneSet, F z = upperHalfPlanePoissonIntegralFun w z := by
  have hFa : AnalyticOnNhd ℂ F upperHalfPlaneSet :=
    hF.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  obtain ⟨a, ha, haS, hre⟩ := exists_eq_integral_upperHalfPlanePoissonKernel_mul_of_abs_le
    (fun z hz ↦ (hFa z hz).harmonicAt_re) fun z hz ↦ (abs_re_le_norm _).trans (hS z hz)
  obtain ⟨b, hb, hbS, him⟩ := exists_eq_integral_upperHalfPlanePoissonKernel_mul_of_abs_le
    (fun z hz ↦ (hFa z hz).harmonicAt_im) fun z hz ↦ (abs_im_le_norm _).trans (hS z hz)
  set w : ℝ → ℂ := fun x ↦ a x + b x * I
  have hwm : Measurable w := by fun_prop
  have hwre (x : ℝ) : (w x).re = a x := by simp [w]
  have hwim (x : ℝ) : (w x).im = b x := by simp [w]
  refine ⟨w, hwm, fun x ↦ by rw [hwre, hwim]; exact ⟨haS x, hbS x⟩, fun z hz ↦ ?_⟩
  have hw : Integrable w upperHalfPlanePoissonMeasure := by
    refine Integrable.of_bound hwm.aestronglyMeasurable (S + S) (.of_forall fun x ↦ ?_)
    calc ‖w x‖ ≤ |(w x).re| + |(w x).im| := norm_le_abs_re_add_abs_im _
      _ ≤ S + S := by rw [hwre, hwim]; exact add_le_add (haS x) (hbS x)
  refine Complex.ext ?_ ?_
  · rw [re_upperHalfPlanePoissonIntegralFun hw, hre z hz]
    simp only [hwre]
  · rw [im_upperHalfPlanePoissonIntegralFun hw, him z hz]
    simp only [hwim]

end TauCeti
