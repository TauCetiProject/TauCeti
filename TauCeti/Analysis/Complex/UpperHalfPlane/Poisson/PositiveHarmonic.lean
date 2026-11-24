/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Basic
import Mathlib.Analysis.Complex.Harmonic.Analytic
import TauCeti.Analysis.Complex.UpperHalfPlane.Primitive

/-!
# Nonnegative harmonic functions on the upper half-plane

A nonnegative harmonic function `u` on the upper half-plane `ℂ₊` is

`u(z) = c Im z + P[ν](z)`

for some `c ≥ 0` and some Poisson-finite measure `ν` on `ℝ`, where `P[ν]` is the Poisson integral
`TauCeti.upperHalfPlanePoissonIntegral`
(`TauCeti.exists_eq_mul_im_add_upperHalfPlanePoissonIntegral`).

The proof goes through holomorphic functions. The complex partial `∂ₓu - i ∂ᵧu` of `u` is
holomorphic on `ℂ₊` (`HarmonicAt.differentiableAt_complex_partial`), so its wedge integral is a
primitive there (`DifferentiableOn.hasDerivAt_wedgeIntegral_upperHalfPlane`); the real part of the
primitive has the gradient of `u`, and `i` times the primitive, suitably normalized, is a
holomorphic `F` with `Im F = u` (`TauCeti.exists_differentiableOn_im_eq_of_harmonicOnNhd`). Since
`Im F ≥ 0`, the Herglotz representation `TauCeti.exists_eq_subtractedResolventKernel_add` applies to
`F`, and its imaginary part is the representation of `u`, because the imaginary part of the Schwarz
kernel is `π` times the Poisson kernel.

The constants are read off along the imaginary axis. For a Poisson-finite `ν` and `y > 0`,
`π y P[ν](iy) = ∫ y² / (x² + y²) dν(x)`, which increases to `ν(ℝ)` as `y → ∞`
(`TauCeti.tendsto_ofReal_pi_mul_mul_upperHalfPlanePoissonIntegral`), while `P[ν](iy) / y → 0`.
So in a representation `u = c Im + P[ν]`, `π y u(iy) - π c y²` increases to `ν(ℝ)` and
`c = lim u(iy) / y` (`TauCeti.tendsto_div_of_eq_mul_im_add_upperHalfPlanePoissonIntegral`).

## Main results

* `TauCeti.exists_differentiableOn_im_eq_of_harmonicOnNhd`: a harmonic function on `ℂ₊` is the
  imaginary part of a holomorphic function on `ℂ₊`.
* `TauCeti.exists_eq_mul_im_add_upperHalfPlanePoissonIntegral`: the representation
  `u = c Im + P[ν]` of a nonnegative harmonic function.
* `TauCeti.pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I`,
  `TauCeti.monotoneOn_pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I` and
  `TauCeti.tendsto_ofReal_pi_mul_mul_upperHalfPlanePoissonIntegral`: the mass of `ν` from the
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

/-! ### Harmonic conjugates on the upper half-plane -/

/-- **A harmonic function on the upper half-plane is the imaginary part of a holomorphic
function.** -/
theorem exists_differentiableOn_im_eq_of_harmonicOnNhd {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u upperHalfPlaneSet) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F upperHalfPlaneSet ∧
      EqOn (fun z ↦ (F z).im) u upperHalfPlaneSet := by
  -- the complex partial `∂ₓu - i ∂ᵧu`, and its wedge-integral primitive `G`
  let g : ℂ → ℂ := fun z ↦ fderiv ℝ u z 1 - I * fderiv ℝ u z I
  have hg : DifferentiableOn ℂ g upperHalfPlaneSet := fun z hz ↦
    (HarmonicAt.differentiableAt_complex_partial (hu z hz)).differentiableWithinAt
  let G : ℂ → ℂ := fun w ↦ wedgeIntegral (UpperHalfPlane.I : ℂ) w g
  have hG (z : ℂ) (hz : z ∈ upperHalfPlaneSet) : HasDerivAt G (g z) z :=
    hg.hasDerivAt_wedgeIntegral_upperHalfPlane UpperHalfPlane.I hz
  have hGd : DifferentiableOn ℂ G upperHalfPlaneSet := fun z hz ↦
    (hG z hz).differentiableAt.differentiableWithinAt
  have hI : (I : ℂ) ∈ upperHalfPlaneSet := by simp
  -- the real part of `G` is `u - u(i)`
  have hre : EqOn (fun z ↦ (G z).re) (fun z ↦ u z - u I) upperHalfPlaneSet := by
    have hopen := UpperHalfPlane.isOpen_upperHalfPlaneSet
    have hGr : DifferentiableOn ℝ G upperHalfPlaneSet := hGd.restrictScalars ℝ
    refine (convex_halfSpace_im_gt 0).eqOn_of_fderivWithin_eq (𝕜 := ℝ) (x := I)
      (reCLM.differentiable.comp_differentiableOn hGr)
      (fun y hy ↦ (((hu y hy).1.differentiableAt two_ne_zero).sub_const
        (u I)).differentiableWithinAt)
      hopen.uniqueDiffOn (fun y hy ↦ ?_) hI ?_
    · have h₄ := (hG y hy).differentiableAt
      have h₅ := h₄.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)
      have hu' := (hu y hy).1.differentiableAt two_ne_zero
      rw [show (fun z ↦ (G z).re) = reCLM ∘ G from rfl, fderivWithin_eq_fderiv
        (hopen.uniqueDiffWithinAt hy) (reCLM.differentiableAt.comp y h₅), fderivWithin_eq_fderiv
        (hopen.uniqueDiffWithinAt hy) (hu'.sub_const (u I)),
        fderiv_comp y (by fun_prop) h₅,
        ContinuousLinearMap.fderiv, h₄.fderiv_restrictScalars (𝕜 := ℝ),
        fderiv_sub_const]
      ext a
      nth_rw 2 [(by simp : a = a.re • (1 : ℂ) + a.im • (I : ℂ))]
      rw [map_add, map_smul, map_smul]
      simp [HasDerivAt.deriv (hG y hy), g]
    · simp [G, wedgeIntegral]
  refine ⟨fun z ↦ I * (G z + u I), (hGd.add_const _).const_mul I, fun z hz ↦ ?_⟩
  have := hre hz
  simp only [mul_im, I_re, zero_mul, I_im, one_mul, zero_add, add_re, ofReal_re] at this ⊢
  linarith

/-! ### The representation -/

/-- **Nonnegative harmonic functions on the upper half-plane.** A nonnegative harmonic function `u`
on `ℂ₊` is `u(z) = c Im z + P[ν](z)` for some `c ≥ 0` and some Poisson-finite measure `ν`. -/
theorem exists_eq_mul_im_add_upperHalfPlanePoissonIntegral {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u upperHalfPlaneSet) (hpos : ∀ z ∈ upperHalfPlaneSet, 0 ≤ u z) :
    ∃ (c : ℝ) (ν : Measure ℝ), 0 ≤ c ∧ IsPoissonFinite ν ∧
      ∀ z ∈ upperHalfPlaneSet, u z = c * z.im + upperHalfPlanePoissonIntegral ν z := by
  obtain ⟨F, hF, hFu⟩ := exists_differentiableOn_im_eq_of_harmonicOnNhd hu
  obtain ⟨b, ν, hb, hν, hrep⟩ := exists_eq_subtractedResolventKernel_add hF
    fun z hz ↦ (hFu hz).trans_ge (hpos z hz)
  refine ⟨b, ENNReal.ofReal π • ν, hb, ?_, fun z hz ↦ ?_⟩
  · exact (isPoissonFinite_iff _).2 (((isPoissonFinite_iff ν).1
      ((isPoissonFinite_iff_lintegral_lt_top ν).2 hν)).smul_measure ENNReal.ofReal_ne_top)
  · have hint := integrable_subtractedResolventKernel hν (ne_of_gt hz)
    rw [← hFu hz]
    dsimp only
    rw [hrep z hz, upperHalfPlanePoissonIntegral_def, integral_smul_measure,
      ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul, ← integral_const_mul]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_mul, zero_add, add_zero]
    rw [show (∫ t, subtractedResolventKernel z t ∂ν).im =
      ∫ t, (subtractedResolventKernel z t).im ∂ν from (integral_im hint).symm]
    simp_rw [subtractedResolventKernel_im_eq_pi_mul_upperHalfPlanePoissonKernel]

/-! ### Reading off the constants on the imaginary axis -/

private theorem normSq_ofReal_sub_mul_I (x y : ℝ) :
    normSq ((x : ℂ) - y * I) = x ^ 2 + y ^ 2 := by
  simp [normSq_apply]
  ring

/-- On the imaginary axis, `π y P(iy, x) = y² / (x² + y²)`. -/
theorem pi_mul_mul_upperHalfPlanePoissonKernel_mul_I (y x : ℝ) :
    π * y * upperHalfPlanePoissonKernel (y * I) x = y ^ 2 / (x ^ 2 + y ^ 2) := by
  rw [upperHalfPlanePoissonKernel_eq, normSq_ofReal_sub_mul_I]
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
  field_simp

/-- **The Poisson integral on the imaginary axis.** For a measure `ν` on `ℝ`,
`π y P[ν](iy) = ∫ y² / (x² + y²) dν(x)`. -/
theorem pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I (ν : Measure ℝ) (y : ℝ) :
    π * y * upperHalfPlanePoissonIntegral ν (y * I) = ∫ x, y ^ 2 / (x ^ 2 + y ^ 2) ∂ν := by
  rw [upperHalfPlanePoissonIntegral_def, ← integral_const_mul]
  simp_rw [pi_mul_mul_upperHalfPlanePoissonKernel_mul_I]

private theorem div_le_div_add_of_le {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s ≤ t) :
    s / (a + s) ≤ t / (a + t) := by
  rcases hs.eq_or_lt with rfl | hs
  · simp only [zero_div]
    exact div_nonneg (hs.trans hst) (by linarith)
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

private theorem monotone_sq_div (x : ℝ) :
    Monotone fun y : ℝ ↦ max y 0 ^ 2 / (x ^ 2 + max y 0 ^ 2) := fun _ _ h ↦
  div_le_div_add_of_le (sq_nonneg x) (sq_nonneg _)
    (pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 h) 2)

/-- `π y P[ν](iy)` is monotone in `y > 0`. -/
theorem monotoneOn_pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I (ν : Measure ℝ) :
    MonotoneOn (fun y : ℝ ↦ π * y * upperHalfPlanePoissonIntegral ν (y * I)) (Ioi 0) := by
  by_cases hν : IsPoissonFinite ν
  swap
  · simpa [upperHalfPlanePoissonIntegral_of_not_isPoissonFinite hν] using monotoneOn_const
  intro y hy y' hy' h
  have hint (t : ℝ) : Integrable (fun x ↦ t ^ 2 / (x ^ 2 + t ^ 2)) ν := by
    have := (hν.integrable_upperHalfPlanePoissonKernel (t * I)).const_mul (π * t)
    simpa only [pi_mul_mul_upperHalfPlanePoissonKernel_mul_I] using this
  simp only [pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I]
  refine integral_mono (hint y) (hint y') fun x ↦ ?_
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
`π y P[ν](iy) = ∫ y² / (x² + y²) dν(x)` increases to `ν(ℝ)`, which may be infinite. -/
theorem tendsto_ofReal_pi_mul_mul_upperHalfPlanePoissonIntegral {ν : Measure ℝ}
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
  have hint : Integrable (fun x ↦ y ^ 2 / (x ^ 2 + y ^ 2)) ν := by
    have := (hν.integrable_upperHalfPlanePoissonKernel (y * I)).const_mul (π * y)
    simpa only [pi_mul_mul_upperHalfPlanePoissonKernel_mul_I] using this
  rw [pi_mul_mul_upperHalfPlanePoissonIntegral_mul_I,
    ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun x ↦ by positivity)]
  simp [f, max_eq_left hy.le]

/-- On the imaginary axis, `P[ν](iy) / y → 0` as `y → ∞`. -/
theorem tendsto_upperHalfPlanePoissonIntegral_mul_I_div (ν : Measure ℝ) :
    Tendsto (fun y : ℝ ↦ upperHalfPlanePoissonIntegral ν (y * I) / y) atTop (𝓝 0) := by
  by_cases hν : IsPoissonFinite ν
  swap
  · simp [upperHalfPlanePoissonIntegral_of_not_isPoissonFinite hν]
  have hlim : Tendsto (fun y : ℝ ↦ ∫ x, (π * (x ^ 2 + y ^ 2))⁻¹ ∂ν) atTop
      (𝓝 (∫ _x, (0 : ℝ) ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ (1 + x ^ 2)⁻¹)
      (.of_forall fun y ↦ by fun_prop) ?_ ((isPoissonFinite_iff ν).1 hν) (.of_forall fun x ↦ ?_)
    · filter_upwards [eventually_ge_atTop 1] with y hy
      refine .of_forall fun x ↦ ?_
      rw [Real.norm_of_nonneg (by positivity)]
      refine inv_anti₀ (by positivity) ?_
      nlinarith [Real.two_le_pi, sq_nonneg x, sq_nonneg y]
    · have h : Tendsto (fun y : ℝ ↦ π * (x ^ 2 + y ^ 2)) atTop atTop :=
        (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)).const_mul_atTop
          Real.pi_pos
      exact h.inv_tendsto_atTop
  rw [integral_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [upperHalfPlanePoissonIntegral_def, div_eq_mul_inv, mul_comm, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  dsimp only
  rw [upperHalfPlanePoissonKernel_eq, normSq_ofReal_sub_mul_I]
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
  field_simp

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
  rw [hrep _ (by simpa using hy)]
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
  field_simp

/-- **The mass from the imaginary axis.** If `u = c Im + P[ν]` on `ℂ₊` with `ν` Poisson-finite,
then `π y u(iy) - π c y²` increases to `ν(ℝ)` as `y → ∞`. -/
theorem tendsto_ofReal_of_eq_mul_im_add_upperHalfPlanePoissonIntegral (hν : IsPoissonFinite ν)
    (hrep : ∀ z ∈ upperHalfPlaneSet, u z = c * z.im + upperHalfPlanePoissonIntegral ν z) :
    Tendsto (fun y : ℝ ↦ ENNReal.ofReal (π * y * u (y * I) - π * c * y ^ 2)) atTop
      (𝓝 (ν univ)) := by
  refine (tendsto_ofReal_pi_mul_mul_upperHalfPlanePoissonIntegral hν).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [hrep _ (by simpa using hy)]
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
  ring_nf

end Representation

end TauCeti
