/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Basic
import Mathlib.Analysis.Complex.Convex
import TauCeti.Analysis.Complex.Harmonic.Conjugate
import TauCeti.Analysis.Convex.SimplyConnected
import TauCeti.Basic.Complex.OfRealSub

/-!
# Nonnegative harmonic functions on the upper half-plane

A nonnegative harmonic function `u` on the upper half-plane `ℂ₊` is

`u(z) = c Im z + P[ν](z)`

for some `c ≥ 0` and some Poisson-finite measure `ν` on `ℝ`, where `P[ν]` is the Poisson integral
`TauCeti.upperHalfPlanePoissonIntegral`
(`TauCeti.exists_eq_mul_im_add_upperHalfPlanePoissonIntegral`).

The proof goes through holomorphic functions. A harmonic `u` on `ℂ₊` is `Re G` for an analytic
`G` on `ℂ₊`, since `ℂ₊` is convex and hence simply connected
(`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_re_eq_of_isSimplyConnected`), so `u = Im F`
for the holomorphic `F = i G`.
Since `Im F ≥ 0`, the Herglotz representation `TauCeti.exists_eq_subtractedResolventKernel_add`
applies to `F`, and its imaginary part is the representation of `u`, because the imaginary part of
the Schwarz kernel is `π` times the Poisson kernel
(`TauCeti.im_integral_subtractedResolventKernel`).

The constants are read off along the imaginary axis. For a Poisson-finite `ν` and `y > 0`,
`π y P[ν](iy) = ∫ y² / (x² + y²) dν(x)`, which is monotone in `y` and tends to `ν(ℝ)` as `y → ∞`
(`TauCeti.tendsto_ofReal_pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I`), while
`P[ν](iy) / y → 0` by the Herglotz linear-coefficient limit
`TauCeti.tendsto_im_div_of_eq_subtractedResolventKernel_add`. So in a representation
`u = c Im + P[ν]`, `π y u(iy) - π c y²` tends to `ν(ℝ)` and `c = lim u(iy) / y`
(`TauCeti.tendsto_div_of_eq_mul_im_add_upperHalfPlanePoissonIntegral`).

## Main results

* `TauCeti.exists_eq_mul_im_add_upperHalfPlanePoissonIntegral`: the representation
  `u = c Im + P[ν]` of a nonnegative harmonic function.
* `TauCeti.pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I`,
  `TauCeti.monotoneOn_pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I` and
  `TauCeti.tendsto_ofReal_pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I`: the mass of `ν` from the
  Poisson integral on the imaginary axis.
* `TauCeti.tendsto_upperHalfPlanePoissonIntegral_mul_I_div`: `P[ν](iy) / y → 0`.
* `TauCeti.tendsto_div_of_eq_mul_im_add_upperHalfPlanePoissonIntegral` and
  `TauCeti.tendsto_ofReal_of_eq_mul_im_add_upperHalfPlanePoissonIntegral`: `c` and `ν(ℝ)` from `u`.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §3.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Set InnerProductSpace
open UpperHalfPlane (upperHalfPlaneSet)
open scoped Topology ENNReal Real

namespace TauCeti

/-! ### The representation -/

/-- **Nonnegative harmonic functions on the upper half-plane.** A nonnegative harmonic function `u`
on `ℂ₊` is `u(z) = c Im z + P[ν](z)` for some `c ≥ 0` and some Poisson-finite measure `ν`. -/
theorem exists_eq_mul_im_add_upperHalfPlanePoissonIntegral {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u upperHalfPlaneSet) (hpos : ∀ z ∈ upperHalfPlaneSet, 0 ≤ u z) :
    ∃ (c : ℝ) (ν : Measure ℝ), 0 ≤ c ∧ IsPoissonFinite ν ∧
      ∀ z ∈ upperHalfPlaneSet, u z = c * z.im + upperHalfPlanePoissonIntegral ν z := by
  obtain ⟨G, hG, hGu⟩ := hu.exists_analyticOnNhd_re_eq_of_isSimplyConnected
    UpperHalfPlane.isOpen_upperHalfPlaneSet
    ((convex_halfSpace_im_gt 0).isSimplyConnected ⟨I, by simp⟩)
  set F : ℂ → ℂ := fun z ↦ I * G z
  have hF : DifferentiableOn ℂ F upperHalfPlaneSet := hG.differentiableOn.const_mul I
  have hFu : EqOn (fun z ↦ (F z).im) u upperHalfPlaneSet := fun z hz ↦ by
    simpa [F] using hGu hz
  obtain ⟨b, ν, hb, hν, hrep⟩ := exists_eq_subtractedResolventKernel_add hF
    fun z hz ↦ (hFu hz).trans_ge (hpos z hz)
  refine ⟨b, ENNReal.ofReal π • ν, hb, ?_, fun z hz ↦ ?_⟩
  · exact ((isPoissonFinite_iff_lintegral_lt_top ν).2 hν).smul_measure ENNReal.ofReal_ne_top
  · rw [← hFu hz]
    dsimp only
    rw [hrep z hz, upperHalfPlanePoissonIntegral_smul_measure,
      ENNReal.toReal_ofReal Real.pi_pos.le, ← im_integral_subtractedResolventKernel]
    simp

/-! ### Reading off the constants on the imaginary axis -/

/-- On the imaginary axis, `π y P(iy, x) = y² / (x² + y²)`. -/
theorem pi_mul_mul_upperHalfPlanePoissonKernel_mul_I (y x : ℝ) :
    π * y * upperHalfPlanePoissonKernel (y * I) x = y ^ 2 / (x ^ 2 + y ^ 2) := by
  simp [upperHalfPlanePoissonKernel_eq, normSq_ofReal_sub]
  field_simp

/-- **The Poisson integral on the imaginary axis.** For a measure `ν` on `ℝ`,
`π y P[ν](iy) = ∫ y² / (x² + y²) dν(x)`. -/
theorem pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I (ν : Measure ℝ) (y : ℝ) :
    π * y * upperHalfPlanePoissonIntegral ν (y * I) = ∫ x, y ^ 2 / (x ^ 2 + y ^ 2) ∂ν := by
  rw [upperHalfPlanePoissonIntegral_def, ← integral_const_mul]
  simp_rw [pi_mul_mul_upperHalfPlanePoissonKernel_mul_I]

/-- For a Poisson-finite `ν`, the imaginary-axis weight `x ↦ t² / (x² + t²)` is `ν`-integrable. -/
theorem IsPoissonFinite.integrable_sq_div_sq_add_sq {ν : Measure ℝ} (hν : IsPoissonFinite ν)
    (t : ℝ) : Integrable (fun x ↦ t ^ 2 / (x ^ 2 + t ^ 2)) ν := by
  simpa only [pi_mul_mul_upperHalfPlanePoissonKernel_mul_I] using
    (hν.integrable_upperHalfPlanePoissonKernel (t * I)).const_mul (π * t)

private theorem monotone_sq_div (x : ℝ) :
    Monotone fun y : ℝ ↦ max y 0 ^ 2 / (x ^ 2 + max y 0 ^ 2) := by
  intro y y' h
  dsimp only
  have hst : max y 0 ^ 2 ≤ max y' 0 ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 h) 2
  rcases (sq_nonneg (max y 0)).eq_or_lt with h0 | h0
  · rw [← h0, zero_div]
    positivity
  · rw [div_le_div_iff₀ (add_pos_of_nonneg_of_pos (sq_nonneg x) h0)
      (add_pos_of_nonneg_of_pos (sq_nonneg x) (h0.trans_le hst))]
    nlinarith [sq_nonneg x]

/-- `π y P[ν](iy)` is monotone in `y > 0`. -/
theorem monotoneOn_pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I (ν : Measure ℝ) :
    MonotoneOn (fun y : ℝ ↦ π * y * upperHalfPlanePoissonIntegral ν (y * I)) (Ioi 0) := by
  by_cases hν : IsPoissonFinite ν
  swap
  · simpa [upperHalfPlanePoissonIntegral_of_not_isPoissonFinite hν] using monotoneOn_const
  intro y hy y' hy' h
  simp only [pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I]
  refine integral_mono (hν.integrable_sq_div_sq_add_sq y) (hν.integrable_sq_div_sq_add_sq y')
    fun x ↦ ?_
  have := monotone_sq_div x h
  simpa [max_eq_left (le_of_lt hy), max_eq_left (le_of_lt (mem_Ioi.mp hy'))] using this

private theorem tendsto_sq_div (x : ℝ) :
    Tendsto (fun y : ℝ ↦ max y 0 ^ 2 / (x ^ 2 + max y 0 ^ 2)) atTop (𝓝 1) := by
  have h : Tendsto (fun y : ℝ ↦ x ^ 2 + y ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h0 := (tendsto_const_nhds (x := x ^ 2)).div_atTop h
  have h1 : Tendsto (fun y : ℝ ↦ 1 - x ^ 2 / (x ^ 2 + y ^ 2)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [max_eq_left hy.le]
  field_simp
  ring

/-- **The mass of a Poisson-finite measure from its Poisson integral.** As `y → ∞`,
`π y P[ν](iy) = ∫ y² / (x² + y²) dν(x)` tends to `ν(ℝ)`, which may be infinite; the convergence is
monotone by `TauCeti.monotoneOn_pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I`. -/
theorem tendsto_ofReal_pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I {ν : Measure ℝ}
    (hν : IsPoissonFinite ν) :
    Tendsto (fun y : ℝ ↦ ENNReal.ofReal (π * y * upperHalfPlanePoissonIntegral ν (y * I))) atTop
      (𝓝 (ν univ)) := by
  -- the truncated weights `f y x = y₊² / (x² + y₊²)`, monotone in `y`
  let f : ℝ → ℝ → ℝ≥0∞ := fun y x ↦ ENNReal.ofReal (max y 0 ^ 2 / (x ^ 2 + max y 0 ^ 2))
  have hfm (y : ℝ) : Measurable (f y) := by fun_prop
  have hmono : Monotone fun y ↦ ∫⁻ x, f y x ∂ν := fun y y' h ↦
    lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (monotone_sq_div x h)
  -- along the integers, monotone convergence gives `ν(ℝ)`
  have hnat : Tendsto (fun n : ℕ ↦ ∫⁻ x, f n x ∂ν) atTop (𝓝 (ν univ)) := by
    rw [← lintegral_one]
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n ↦ (hfm n).aemeasurable)
      (.of_forall fun x n m h ↦ ENNReal.ofReal_le_ofReal (monotone_sq_div x (by exact_mod_cast h)))
      (.of_forall fun x ↦ ?_)
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.tendsto_ofReal (tendsto_sq_div x)).comp tendsto_natCast_atTop_atTop
  have hsup := tendsto_atTop_iSup hmono
  have heq : (⨆ y, ∫⁻ x, f y x ∂ν) = ν univ :=
    tendsto_nhds_unique (hsup.comp tendsto_natCast_atTop_atTop) hnat
  rw [heq] at hsup
  refine hsup.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I, ofReal_integral_eq_lintegral_ofReal
    (hν.integrable_sq_div_sq_add_sq y) (.of_forall fun x ↦ by positivity)]
  simp [f, max_eq_left hy.le]

/-- On the imaginary axis, `P[ν](iy) / y → 0` as `y → ∞`. This holds for every measure `ν`:
when `ν` is not Poisson-finite, `P[ν]` is the junk value `0`. -/
theorem tendsto_upperHalfPlanePoissonIntegral_mul_I_div (ν : Measure ℝ) :
    Tendsto (fun y : ℝ ↦ upperHalfPlanePoissonIntegral ν (y * I) / y) atTop (𝓝 0) := by
  -- The Herglotz function `z ↦ ∫ t, K(z, t) dν(t)` has imaginary part `π P[ν]`
  -- (`im_integral_subtractedResolventKernel`), so its linear-coefficient limit divided by `π`
  -- gives the claim.
  have h := (tendsto_im_div_of_eq_subtractedResolventKernel_add (a := 0) (b := 0) (nu := ν)
    (F := fun z ↦ ∫ t, subtractedResolventKernel z t ∂ν) fun _ _ ↦ by simp).div_const π
  rw [zero_div] at h
  refine h.congr fun y ↦ ?_
  rw [im_integral_subtractedResolventKernel, mul_div_assoc, mul_div_cancel_left₀ _ Real.pi_ne_zero]

section Representation

variable {u : ℂ → ℝ} {c : ℝ} {ν : Measure ℝ}

/-- **The linear coefficient from the imaginary axis.** If `u = c Im + P[ν]` on `ℂ₊`, then
`c = lim u(iy) / y` as `y → ∞`. -/
theorem tendsto_div_of_eq_mul_im_add_upperHalfPlanePoissonIntegral
    (hrep : ∀ z ∈ upperHalfPlaneSet, u z = c * z.im + upperHalfPlanePoissonIntegral ν z) :
    Tendsto (fun y : ℝ ↦ u (y * I) / y) atTop (𝓝 c) := by
  have h := (tendsto_upperHalfPlanePoissonIntegral_mul_I_div ν).const_add c
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [hrep _ (by simpa using hy), mul_I_im, ofReal_re]
  field_simp

/-- **The mass from the imaginary axis.** If `u = c Im + P[ν]` on `ℂ₊` with `ν` Poisson-finite,
then `π y u(iy) - π c y²` tends to `ν(ℝ)` as `y → ∞`. -/
theorem tendsto_ofReal_of_eq_mul_im_add_upperHalfPlanePoissonIntegral (hν : IsPoissonFinite ν)
    (hrep : ∀ z ∈ upperHalfPlaneSet, u z = c * z.im + upperHalfPlanePoissonIntegral ν z) :
    Tendsto (fun y : ℝ ↦ ENNReal.ofReal (π * y * u (y * I) - π * c * y ^ 2)) atTop
      (𝓝 (ν univ)) := by
  refine (tendsto_ofReal_pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I hν).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [hrep _ (by simpa using hy), mul_I_im, ofReal_re]
  ring_nf

end Representation

end TauCeti
