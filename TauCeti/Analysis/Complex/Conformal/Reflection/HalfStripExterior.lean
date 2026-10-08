/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Infinity
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Topology.MetricSpace.CoboundedImage
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The pre-Schwarzian at an end of opening `2 * π`

Let `f` map the upper half-plane conformally onto a domain `U`, extend to a continuous injection
of the closed upper half-plane, and tend to infinity at infinity.  Suppose that far out `U`
coincides with the exterior of the closed half-strip `{0 ≤ re ζ, 0 ≤ im ζ ≤ π}` in the coordinate
`ζ = (z - c) / b`: the two unbounded sides of `U` are parallel rays pointing in the same
direction, and `U` surrounds the half-strip between them, so its end at infinity has opening
`2 * π`.  Then `z * f''(z) / f'(z) → 1` as `z` tends to infinity in the upper half-plane
(`TauCeti.tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_halfStripExterior`).

Unlike a sector or a half-strip, the exterior of a half-strip has no elementary straightening
coordinate.  Instead `f` is compared with the explicit model map `ζ ↦ ζ ^ 2 / 2 - log ζ + π * I`,
which carries the far part of the closed upper half-plane injectively into that exterior, with
the far positive and negative real axes going to the two sides.  The comparison map
`f⁻¹ ∘ (c + b * model)` fixes infinity, is real on the far real axis, and so is conformal across
infinity by Schwarz reflection; the model has `ζ * model''(ζ) / model'(ζ) → 1`, and
`TauCeti.tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_comp_neg_inv` transfers this limit
to `f`.  For a Schwarz--Christoffel map the limit is the sum of the finite turning exponents.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

/-! ### The model map -/

/-- The model map of an end of opening `2 * π`. -/
private noncomputable def model (ζ : ℂ) : ℂ := ζ ^ 2 / 2 - log ζ + Real.pi * Complex.I

private theorem re_model (ζ : ℂ) :
    (model ζ).re = (ζ.re ^ 2 - ζ.im ^ 2) / 2 - Real.log ‖ζ‖ := by
  simp [model, sq, log_re]

private theorem im_model (ζ : ℂ) : (model ζ).im = ζ.re * ζ.im - ζ.arg + Real.pi := by
  simp [model, sq, log_im]
  ring

/-- On the closed upper half-plane, outside the disc of radius `2`, and to the right of
`re ζ = 1`, the model has imaginary part at least `π`, strictly more off the axis. -/
private theorem im_model_ge {ζ : ℂ} (him : 0 ≤ ζ.im) (hre : 1 ≤ ζ.re) (hζ : 2 ≤ ‖ζ‖) :
    Real.pi + (1 - Real.pi / 4) * ζ.im ≤ (model ζ).im := by
  -- Jordan's inequality `2 / π * arg ζ ≤ sin (arg ζ) = im ζ / ‖ζ‖`.
  have hJ := Real.mul_le_sin (arg_nonneg_iff.mpr him)
    (abs_le.mp (abs_arg_le_pi_div_two_iff.mpr (zero_le_one.trans hre))).2
  rw [sin_arg] at hJ
  have harg : ζ.arg ≤ Real.pi / 2 * (ζ.im / ‖ζ‖) := by
    have := Real.pi_pos
    calc ζ.arg = Real.pi / 2 * (2 / Real.pi * ζ.arg) := by field_simp
      _ ≤ Real.pi / 2 * (ζ.im / ‖ζ‖) := by gcongr
  have : ζ.im / ‖ζ‖ ≤ ζ.im / 2 := div_le_div_of_nonneg_left him two_pos hζ
  have := Real.pi_pos
  rw [im_model]
  nlinarith

/-- To the left of `re ζ = -1` the model has imaginary part at most `0`, strictly less off the
axis. -/
private theorem im_model_le {ζ : ℂ} (him : 0 ≤ ζ.im) (hre : ζ.re ≤ -1) (hζ : 2 ≤ ‖ζ‖) :
    (model ζ).im ≤ -((1 - Real.pi / 4) * ζ.im) := by
  -- Jordan's inequality for `π - arg ζ ∈ [0, π / 2]`, whose sine is `im ζ / ‖ζ‖`.
  have harg : Real.pi / 2 < ζ.arg := by
    have h := mt abs_arg_le_pi_div_two_iff.mp (not_le.mpr (by linarith : ζ.re < 0))
    rwa [not_le, abs_of_nonneg (arg_nonneg_iff.mpr him)] at h
  have hJ := Real.mul_le_sin (by linarith [arg_le_pi ζ] : 0 ≤ Real.pi - ζ.arg)
    (by linarith : Real.pi - ζ.arg ≤ Real.pi / 2)
  rw [Real.sin_pi_sub, sin_arg] at hJ
  have harg' : Real.pi - ζ.arg ≤ Real.pi / 2 * (ζ.im / ‖ζ‖) := by
    have := Real.pi_pos
    calc Real.pi - ζ.arg = Real.pi / 2 * (2 / Real.pi * (Real.pi - ζ.arg)) := by field_simp
      _ ≤ Real.pi / 2 * (ζ.im / ‖ζ‖) := by gcongr
  have : ζ.im / ‖ζ‖ ≤ ζ.im / 2 := div_le_div_of_nonneg_left him two_pos hζ
  have := Real.pi_pos
  rw [im_model]
  nlinarith

/-- In the vertical strip `|re ζ| ≤ 1`, outside the disc of radius `2`, the model has negative
real part. -/
private theorem re_model_neg {ζ : ℂ} (hre : |ζ.re| ≤ 1) (hζ : 2 ≤ ‖ζ‖) : (model ζ).re < 0 := by
  have hsq : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by rw [← normSq_eq_norm_sq, normSq_apply]; ring
  have hre2 : ζ.re ^ 2 ≤ 1 := by nlinarith [abs_nonneg ζ.re, sq_abs ζ.re]
  have hlog : 0 ≤ Real.log ‖ζ‖ := Real.log_nonneg (by linarith)
  rw [re_model]
  nlinarith

/-- The model carries the far part of the open upper half-plane into the exterior of the closed
half-strip `{0 ≤ re, 0 ≤ im ≤ π}`. -/
private theorem model_mem_exterior {ζ : ℂ} (him : 0 < ζ.im) (hζ : 2 ≤ ‖ζ‖) :
    (model ζ).re < 0 ∨ (model ζ).im ∉ Icc 0 Real.pi := by
  have hπ : 0 < 1 - Real.pi / 4 := by linarith [Real.pi_lt_four]
  by_cases h1 : 1 ≤ ζ.re
  · have := im_model_ge him.le h1 hζ
    exact Or.inr fun h => by nlinarith [h.2]
  by_cases h2 : ζ.re ≤ -1
  · have := im_model_le him.le h2 hζ
    exact Or.inr fun h => by nlinarith [h.1]
  exact Or.inl (re_model_neg (abs_le.mpr ⟨by linarith, by linarith⟩) hζ)

/-- The model carries the far real axis into the closed half-strip `{0 ≤ re, 0 ≤ im ≤ π}`. -/
private theorem model_mem_halfStrip {ζ : ℂ} (him : ζ.im = 0) (hζ : 2 ≤ ‖ζ‖) :
    0 ≤ (model ζ).re ∧ (model ζ).im ∈ Icc 0 Real.pi := by
  have hn : ‖ζ‖ = |ζ.re| := by
    have hζr : ζ = (ζ.re : ℂ) := Complex.ext (by simp) (by simp [him])
    conv_lhs => rw [hζr]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hlog := Real.log_le_sub_one_of_pos (zero_lt_two.trans_le hζ)
  have hsq : |ζ.re| ^ 2 = ζ.re ^ 2 := sq_abs _
  refine ⟨?_, ?_, ?_⟩
  · rw [re_model, him, hn]
    rw [hn] at hζ hlog
    nlinarith
  · rw [im_model, him, mul_zero, zero_sub]
    linarith [arg_le_pi ζ]
  · rw [im_model, him, mul_zero, zero_sub]
    linarith [arg_nonneg_iff.mpr him.ge]

/-- The model grows at least linearly. -/
private theorem norm_model_ge {ζ : ℂ} (hζ : 4 ≤ ‖ζ‖) : ‖ζ‖ - 2 * Real.pi ≤ ‖model ζ‖ := by
  have hlog : ‖log ζ‖ ≤ ‖ζ‖ + Real.pi := by
    have h := norm_le_abs_re_add_abs_im (log ζ)
    rw [log_re, log_im, abs_of_nonneg (Real.log_nonneg (by linarith))] at h
    linarith [Real.log_le_self (norm_nonneg ζ), abs_arg_le_pi ζ]
  have hsq : ‖ζ ^ 2 / 2‖ = ‖ζ‖ ^ 2 / 2 := by simp
  have hI : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by simp
  have h := norm_sub_norm_le (ζ ^ 2 / 2) (log ζ - Real.pi * Complex.I)
  have heq : ζ ^ 2 / 2 - (log ζ - Real.pi * Complex.I) = model ζ := by
    simp only [model]
    ring
  rw [heq, hsq] at h
  have h2 := norm_sub_le (log ζ) (Real.pi * Complex.I)
  rw [hI] at h2
  nlinarith

/-- An affine image of the model tends to infinity at infinity. -/
private theorem tendsto_const_add_mul_model {c b : ℂ} (hb : b ≠ 0) :
    Tendsto (fun ζ => c + b * model ζ) (cobounded ℂ) (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have hlin : Tendsto (fun ζ : ℂ => ‖b‖ * (‖ζ‖ - 2 * Real.pi) - ‖c‖) (cobounded ℂ) atTop :=
    tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop (norm_pos_iff.mpr hb)
      (tendsto_atTop_add_const_right _ _ tendsto_norm_cobounded_atTop))
  refine tendsto_atTop_mono' _ ?_ hlin
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop 4] with ζ hζ
  have h := norm_sub_norm_le (b * model ζ) (-c)
  rw [sub_neg_eq_add, add_comm, norm_neg, norm_mul] at h
  nlinarith [norm_model_ge hζ, norm_nonneg b]

/-- The logarithm is `1 / 2`-Lipschitz on the convex set `{4 ≤ re ζ + im ζ, 0 ≤ im ζ}`. -/
private theorem norm_log_sub_log_le_of_re_add_im {z w : ℂ}
    (hz : 4 ≤ z.re + z.im ∧ 0 ≤ z.im) (hw : 4 ≤ w.re + w.im ∧ 0 ≤ w.im) :
    ‖log z - log w‖ ≤ 1 / 2 * ‖z - w‖ := by
  set P := {ζ : ℂ | 4 ≤ ζ.re + ζ.im ∧ 0 ≤ ζ.im}
  have hP : Convex ℝ P := by
    intro x hx y hy a b ha hb hab
    simp only [P, mem_ofPred_eq, add_re, add_im, smul_re, smul_im, smul_eq_mul] at hx hy ⊢
    constructor <;> nlinarith
  have hnorm : ∀ ζ ∈ P, 2 ≤ ‖ζ‖ := fun ζ hζ => by
    have h := hζ.1
    linarith [re_le_norm ζ, im_le_norm ζ]
  have hslit : ∀ ζ ∈ P, ζ ∈ slitPlane := fun ζ hζ => by
    rcases hζ.2.lt_or_eq with h | h
    · exact mem_slitPlane_iff.mpr (Or.inr h.ne')
    · exact mem_slitPlane_iff.mpr (Or.inl (by linarith [hζ.1]))
  refine hP.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun ζ hζ => (Complex.hasDerivAt_log (hslit ζ hζ)).hasDerivWithinAt) (fun ζ hζ => ?_) hw hz
  rw [norm_inv]
  exact inv_le_of_inv_le₀ (by norm_num) (by linarith [hnorm ζ hζ])

/-- The logarithm is `1 / 2`-Lipschitz on the convex set `{4 ≤ im ζ - re ζ, 0 ≤ im ζ}`, where it
is `π * I` plus the holomorphic function `ζ ↦ log (-ζ)`. -/
private theorem norm_log_sub_log_le_of_im_sub_re {z w : ℂ}
    (hz : 4 ≤ z.im - z.re ∧ 0 ≤ z.im) (hw : 4 ≤ w.im - w.re ∧ 0 ≤ w.im) :
    ‖log z - log w‖ ≤ 1 / 2 * ‖z - w‖ := by
  set P := {ζ : ℂ | 4 ≤ ζ.im - ζ.re ∧ 0 ≤ ζ.im}
  have hP : Convex ℝ P := by
    intro x hx y hy a b ha hb hab
    simp only [P, mem_ofPred_eq, add_re, add_im, smul_re, smul_im, smul_eq_mul] at hx hy ⊢
    constructor <;> nlinarith
  have hnorm : ∀ ζ ∈ P, 2 ≤ ‖ζ‖ := fun ζ hζ => by
    have h := hζ.1
    linarith [(neg_le_abs ζ.re).trans (abs_re_le_norm ζ), im_le_norm ζ]
  have hlog : ∀ ζ ∈ P, log ζ = log (-ζ) + Real.pi * Complex.I := fun ζ hζ => by
    have harg : arg (-ζ) = arg ζ - Real.pi := arg_neg_eq_arg_sub_pi_iff.mpr <| by
      rcases hζ.2.lt_or_eq with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h.symm, by linarith [hζ.1]⟩
    apply Complex.ext <;> simp [log_re, log_im, harg]
  have hslit : ∀ ζ ∈ P, -ζ ∈ slitPlane := fun ζ hζ => by
    rcases hζ.2.lt_or_eq with h | h
    · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using h.ne'))
    · exact mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [hζ.1]))
  have hderiv : ∀ ζ ∈ P, HasDerivWithinAt (fun ζ => log (-ζ)) ζ⁻¹ P ζ := fun ζ hζ => by
    have h := (Complex.hasDerivAt_log (hslit ζ hζ)).comp ζ (hasDerivAt_neg ζ)
    rw [inv_neg, neg_mul_neg, mul_one] at h
    exact h.hasDerivWithinAt
  have hbound : ∀ ζ ∈ P, ‖ζ⁻¹‖ ≤ 1 / 2 := fun ζ hζ => by
    rw [norm_inv]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith [hnorm ζ hζ])
  have h := hP.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hw hz
  rwa [hlog z hz, hlog w hw, add_sub_add_right_eq_sub]

/-- **Injectivity of the model.**  The model is injective on the closed upper half-plane outside
the disc of radius `8`: points on opposite sides of the imaginary axis are separated by the
imaginary part, and on each of two overlapping convex half-planes the logarithm is too small to
cancel the quadratic term. -/
private theorem injOn_model : InjOn model {ζ : ℂ | 0 ≤ ζ.im ∧ 8 ≤ ‖ζ‖} := by
  intro z hz w hw heq
  have hπ : 0 < 1 - Real.pi / 4 := by linarith [Real.pi_lt_four]
  -- Each far point lies in one of the half-planes `4 ≤ re + im`, `4 ≤ im - re`; missing one
  -- of them puts it beyond `|re| > 2`, on the side of the other.
  have hside : ∀ ζ ∈ {ζ : ℂ | 0 ≤ ζ.im ∧ 8 ≤ ‖ζ‖},
      (¬ 4 ≤ ζ.im - ζ.re → 2 < ζ.re ∧ 4 ≤ ζ.re + ζ.im) ∧
        (¬ 4 ≤ ζ.re + ζ.im → ζ.re < -2 ∧ 4 ≤ ζ.im - ζ.re) := fun ζ hζ => by
    have h := norm_le_abs_re_add_abs_im ζ
    rw [abs_of_nonneg hζ.1] at h
    have h8 := hζ.2
    constructor <;> intro hn <;> rcases le_or_gt 0 ζ.re with hr | hr
    all_goals first
      | (rw [abs_of_nonneg hr] at h; constructor <;> linarith)
      | (rw [abs_of_neg hr] at h; constructor <;> linarith)
  -- Points on opposite sides have imaginary parts of the model on opposite sides of `[0, π]`.
  have hopp : ∀ {z w : ℂ}, z ∈ {ζ : ℂ | 0 ≤ ζ.im ∧ 8 ≤ ‖ζ‖} →
      w ∈ {ζ : ℂ | 0 ≤ ζ.im ∧ 8 ≤ ‖ζ‖} → 2 < z.re → w.re < -2 → model z ≠ model w := by
    intro z w hz hw hzr hwr h
    have h1 := im_model_ge hz.1 (by linarith) (by linarith [hz.2])
    have h2 := im_model_le hw.1 (by linarith) (by linarith [hw.2])
    have := congrArg Complex.im h
    nlinarith [Real.pi_pos, hz.1, hw.1]
  -- On a common half-plane the difference of logarithms is too small.
  have hclose : ‖log z - log w‖ ≤ 1 / 2 * ‖z - w‖ → 4 ≤ ‖z + w‖ → z = w := by
    intro hlog hsum
    have hq : (z - w) * (z + w) / 2 = log z - log w := by
      have := heq
      simp only [model] at this
      linear_combination this
    rw [← hq, norm_div, norm_mul, Complex.norm_two] at hlog
    have hzw : ‖z - w‖ = 0 := by nlinarith [norm_nonneg (z - w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzw)
  by_cases hp : 4 ≤ z.re + z.im ∧ 4 ≤ w.re + w.im
  · refine hclose (norm_log_sub_log_le_of_re_add_im ⟨hp.1, hz.1⟩ ⟨hp.2, hw.1⟩) ?_
    have h1 := re_le_norm (z + w)
    have h2 := im_le_norm (z + w)
    simp only [add_re, add_im] at h1 h2
    linarith
  by_cases hm : 4 ≤ z.im - z.re ∧ 4 ≤ w.im - w.re
  · refine hclose (norm_log_sub_log_le_of_im_sub_re ⟨hm.1, hz.1⟩ ⟨hm.2, hw.1⟩) ?_
    have h1 := (neg_le_abs (z + w).re).trans (abs_re_le_norm (z + w))
    have h2 := im_le_norm (z + w)
    simp only [add_re, add_im] at h1 h2
    linarith
  exfalso
  obtain ⟨hz₁, hz₂⟩ := hside z hz
  obtain ⟨hw₁, hw₂⟩ := hside w hw
  rw [not_and_or] at hp hm
  rcases hp with hp | hp <;> rcases hm with hm | hm
  · exact absurd (hz₁ hm).2 hp
  · exact hopp hw hz (hw₁ hm).1 (hz₂ hp).1 heq.symm
  · exact hopp hz hw (hz₁ hm).1 (hw₂ hp).1 heq
  · exact absurd (hw₁ hm).2 hp

/-- The model is holomorphic on the slit plane, with derivative `ζ - ζ⁻¹`. -/
private theorem hasDerivAt_model {ζ : ℂ} (hζ : ζ ∈ slitPlane) :
    HasDerivAt model (ζ - ζ⁻¹) ζ := by
  have h1 : HasDerivAt (fun z : ℂ => z ^ 2 / 2) ζ ζ := by
    simpa using (hasDerivAt_pow 2 ζ).div_const 2
  exact (h1.sub (Complex.hasDerivAt_log hζ)).add_const ((Real.pi : ℂ) * Complex.I)

/-- The model is continuous along the closed upper half-plane away from `0`. -/
private theorem continuousWithinAt_model {ζ : ℂ} (hζ : ζ ≠ 0) :
    ContinuousWithinAt model {z : ℂ | 0 ≤ z.im} ζ := by
  have hlog : ContinuousWithinAt log {z : ℂ | 0 ≤ z.im} ζ := by
    by_cases hs : ζ ∈ slitPlane
    · exact (continuousAt_clog hs).continuousWithinAt
    · have hre : ζ.re ≤ 0 ∧ ζ.im = 0 := by simpa [mem_slitPlane_iff, not_or] using hs
      refine continuousWithinAt_log_of_re_neg_of_im_zero (hre.1.lt_of_ne fun h => hζ ?_) hre.2
      exact Complex.ext h hre.2
  exact (((continuous_pow 2).continuousWithinAt.div_const 2).sub hlog).add continuousWithinAt_const

/-- The model's derivative `ζ - ζ⁻¹` vanishes only at `ζ = ±1`, off the upper half-plane. -/
private theorem sq_sub_one_ne_zero {ζ : ℂ} (hζ : 0 < ζ.im) : ζ ^ 2 - 1 ≠ 0 := fun h => by
  have : (ζ - 1) * (ζ + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h <;>
    · have := congrArg Complex.im h
      simp at this
      simp [this] at hζ

/-- The residue asymptotic of the model's pre-Schwarzian: `ζ * model''(ζ) / model'(ζ) → 1`. -/
private theorem tendsto_mul_logDeriv_deriv_const_add_mul_model {c b : ℂ} (hb : b ≠ 0) :
    Tendsto (fun ζ : ℂ => ζ * logDeriv (deriv fun ζ => c + b * model ζ) ζ)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 1) := by
  have hlim : Tendsto (fun ζ : ℂ => (1 + ζ⁻¹ ^ 2) / (1 - ζ⁻¹ ^ 2))
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 1) := by
    have h : Tendsto (fun u : ℂ => (1 + u ^ 2) / (1 - u ^ 2)) (𝓝 0) (𝓝 1) := by
      have hc : ContinuousAt (fun u : ℂ => (1 + u ^ 2) / (1 - u ^ 2)) 0 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
      simpa using hc.tendsto
    exact h.comp (tendsto_inv₀_cobounded.mono_left inf_le_left)
  refine hlim.congr' ?_
  filter_upwards [mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with ζ hζ
  have hζ0 : ζ ≠ 0 := fun h => by simp [h] at hζ
  have hslit : ∀ z ∈ upperHalfPlaneSet, z ∈ slitPlane := fun z hz =>
    mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hz))
  -- `deriv (c + b * model) = b * (ζ - ζ⁻¹)` on the open upper half-plane.
  have hd : deriv (fun ζ => c + b * model ζ) =ᶠ[𝓝 ζ] fun z => b * (z - z⁻¹) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hζ] with z hz
    exact (((hasDerivAt_model (hslit z hz)).const_mul b).const_add c).deriv
  have hdd : HasDerivAt (fun z : ℂ => b * (z - z⁻¹)) (b * (1 + (ζ ^ 2)⁻¹)) ζ := by
    have := ((hasDerivAt_id ζ).sub (hasDerivAt_inv hζ0)).const_mul b
    simpa [sub_neg_eq_add] using this
  have hne := sq_sub_one_ne_zero hζ
  rw [(logDeriv_congr_nhds hd).eq_of_nhds, logDeriv_apply, hdd.deriv]
  field_simp

/-- For `s` in a small punctured ball, `-s⁻¹` lies outside the disc of radius `8` and the
affine image `b * model (-s⁻¹)` exceeds any prescribed bound `D`. -/
private theorem exists_ball_norm_mul_model_gt {b : ℂ} (hb : b ≠ 0) (D : ℝ) :
    ∃ r > 0, ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → 8 ≤ ‖-s⁻¹‖ ∧ D < ‖b * model (-s⁻¹)‖ := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set R := max 8 (D / ‖b‖ + 2 * Real.pi + 1)
  have hR : D / ‖b‖ + 2 * Real.pi + 1 ≤ R := le_max_right _ _
  have hR8 : 8 ≤ R := le_max_left _ _
  refine ⟨R⁻¹, inv_pos.mpr (by linarith), fun s hs hs0 => ?_⟩
  have hζ : R < ‖-s⁻¹‖ := by
    rw [norm_neg, norm_inv]
    rw [mem_ball_zero_iff] at hs
    exact (lt_inv_comm₀ (norm_pos_iff.mpr hs0) (by linarith)).mp hs
  have h8 : 8 ≤ ‖-s⁻¹‖ := hR8.trans hζ.le
  have h := norm_model_ge (ζ := -s⁻¹) (by linarith)
  have hD : D < ‖b‖ * (‖-s⁻¹‖ - 2 * Real.pi) := by
    rw [← div_lt_iff₀' hbpos]
    linarith
  rw [norm_mul]
  exact ⟨h8, by nlinarith⟩

/-! ### The comparison with the model -/

variable {U : Set ℂ} {f : ℂ → ℂ}

/-- **The comparison map.**  Under the hypotheses of
`TauCeti.tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_halfStripExterior`, in the coordinate
`s ↦ -s⁻¹` at infinity the map `f⁻¹ ∘ (c + b * model)` is a function `g` with `g 0 = 0` which is
continuous and injective up to a real segment through `0`, holomorphic and upper half-plane
valued above it, and real on it. -/
private theorem exists_comparison_of_halfStripExterior {ρ : ℝ} {c b : ℂ}
    (hb : b ≠ 0) (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im}) (hfi : InjOn f {z : ℂ | 0 ≤ z.im})
    (hfU : f '' upperHalfPlaneSet = U)
    (hp : Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (cobounded ℂ))
    (hU : ∀ z : ℂ, ρ < ‖z - c‖ →
      (z ∈ U ↔ ((z - c) / b).re < 0 ∨ ((z - c) / b).im ∉ Icc 0 Real.pi)) :
    ∃ r > 0, ∃ g : ℂ → ℂ,
      EqOn (fun s => f (-(g s)⁻¹)) (fun s => c + b * model (-s⁻¹))
        (ball 0 r ∩ upperHalfPlaneSet) ∧ g 0 = 0 ∧
      ContinuousOn g (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      DifferentiableOn ℂ g (ball 0 r ∩ upperHalfPlaneSet) ∧
      (∀ z ∈ ball (0 : ℂ) r, z.im = 0 → (g z).im = 0) ∧
      MapsTo g (ball 0 r ∩ upperHalfPlaneSet) upperHalfPlaneSet ∧
      InjOn g (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) := by
  set A := {z : ℂ | 0 ≤ z.im}
  have hA : IsClosed A := isClosed_le continuous_const continuous_im
  have hH0 : upperHalfPlaneSet ⊆ A := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  have hH : ∀ s ∈ upperHalfPlaneSet, s ≠ 0 := fun s (hs : 0 < s.im) h => by simp [h] at hs
  -- `f` is a closed embedding of `A`; `φ` is its continuous inverse on the closed image.
  set φ := invFunOn f A
  have hfA : IsClosed (f '' A) := isClosed_image_of_tendsto_cobounded hA hfc hp
  have hφc : ContinuousOn φ (f '' A) :=
    continuousOn_of_leftInvOn_of_tendsto_cobounded hA hfc hfi.leftInvOn_invFunOn hp
  have hφA : ∀ y ∈ f '' A, φ y ∈ A ∧ f (φ y) = y := fun y hy => ⟨invFunOn_mem hy, invFunOn_eq hy⟩
  have hφf : ∀ z ∈ A, φ (f z) = z := fun z hz => by
    simpa only [φ] using hfi.leftInvOn_invFunOn hz
  have hφU : ∀ y ∈ U, φ y ∈ upperHalfPlaneSet ∧
      φ y = invFunOn f upperHalfPlaneSet y := by
    intro y hy
    rw [← hfU] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [hφf z (hH0 hz), (hfi.mono hH0).leftInvOn_invFunOn hz]
    exact ⟨hz, rfl⟩
  -- The model values `q (-s⁻¹)` far out: in `U` above the axis, outside `U` on it.
  set q : ℂ → ℂ := fun ζ => c + b * model ζ
  have hqc : ∀ ζ, (q ζ - c) / b = model ζ := fun ζ => by
    simp only [q]
    field_simp
    ring
  obtain ⟨r, hr, hfar⟩ := exists_ball_norm_mul_model_gt hb (max ρ ‖f 0 - c‖)
  have hfar' : ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → max ρ ‖f 0 - c‖ < ‖q (-s⁻¹) - c‖ :=
    fun s hs hs0 => by simpa [q] using (hfar s hs hs0).2
  have hUp : ∀ s ∈ ball (0 : ℂ) r, 0 < s.im → q (-s⁻¹) ∈ U := fun s hs hsim => by
    refine (hU _ ((le_max_left _ _).trans_lt (hfar' s hs (hH s hsim)))).mpr ?_
    rw [hqc]
    exact model_mem_exterior (im_neg_inv_pos.mpr hsim) (by linarith [(hfar s hs (hH s hsim)).1])
  have hUr : ∀ s ∈ ball (0 : ℂ) r, s.im = 0 → s ≠ 0 → q (-s⁻¹) ∉ U := fun s hs hsim hs0 h => by
    have hm := model_mem_halfStrip (ζ := -s⁻¹) (by simp [hsim])
      (by linarith [(hfar s hs hs0).1])
    rw [hU _ ((le_max_left _ _).trans_lt (hfar' s hs hs0)), hqc] at h
    rcases h with h | h
    · linarith [hm.1]
    · exact h hm.2
  have hqcont : ∀ s : ℂ, s ≠ 0 → ContinuousWithinAt (fun s => q (-s⁻¹)) A s := fun s hs0 => by
    have hinv : ContinuousAt (fun s : ℂ => -s⁻¹) s := (continuousAt_inv₀ hs0).neg
    exact continuousWithinAt_const.add (continuousWithinAt_const.mul
      (ContinuousWithinAt.comp (f := fun s : ℂ => -s⁻¹)
        (continuousWithinAt_model (by simpa using hs0)) hinv.continuousWithinAt
        fun z hz => im_neg_inv_nonneg.mpr hz))
  -- Every model value is a value of `f` on `A`: on the axis, approach from above and use that
  -- `f '' A` is closed.
  have hfAq : ∀ s ∈ ball (0 : ℂ) r, 0 ≤ s.im → s ≠ 0 → q (-s⁻¹) ∈ f '' A := by
    intro s hs hsim hs0
    rcases hsim.lt_or_eq with hsim | hsim
    · obtain ⟨z, hz, hzq⟩ := hfU ▸ hUp s hs hsim
      exact ⟨z, hH0 hz, hzq⟩
    have hne : (𝓝[ball (0 : ℂ) r ∩ upperHalfPlaneSet] s).NeBot := by
      have hs' : s = ((s.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hsim])
      rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds
        (isOpen_ball.mem_nhds hs)), hs']
      exact Real.nhdsWithin_upperHalfPlaneSet_neBot s.re
    refine hfA.mem_of_tendsto (f := fun s => q (-s⁻¹)) (b := 𝓝[ball 0 r ∩ upperHalfPlaneSet] s)
      ?_ ?_
    · exact ((hqcont s hs0).mono fun z hz => (le_of_lt hz.2 : 0 ≤ z.im)).tendsto
    · filter_upwards [self_mem_nhdsWithin] with z hz
      obtain ⟨w, hw, hwq⟩ := hfU ▸ hUp z hz.1 hz.2
      exact ⟨w, hH0 hw, hwq⟩
  have hφ0 : ∀ s ∈ ball (0 : ℂ) r, 0 ≤ s.im → s ≠ 0 → φ (q (-s⁻¹)) ≠ 0 := by
    intro s hs hsim hs0 h
    have hfs := (hφA _ (hfAq s hs hsim hs0)).2
    rw [h] at hfs
    have := hfar' s hs hs0
    rw [← hfs] at this
    exact lt_irrefl _ ((le_max_right _ _).trans_lt this)
  -- The comparison map `g = -1 / φ (q (-1 / s))`, filled in by `0` at `0`.
  set g : ℂ → ℂ := update (fun s => -(φ (q (-s⁻¹)))⁻¹) 0 0
  have hg0 : g 0 = 0 := update_self _ _ _
  have hgv : ∀ s, s ≠ 0 → g s = -(φ (q (-s⁻¹)))⁻¹ := fun s hs => update_of_ne hs _ _
  refine ⟨r, hr, g, fun s hs => ?_, hg0, ?_, ?_, fun s hs hsim => ?_, fun s hs => ?_, ?_⟩
  · -- `f (-1 / g s) = q (-1 / s)`
    dsimp only
    rw [hgv s (hH s hs.2), inv_neg, inv_inv, neg_neg]
    exact (hφA _ (hfAq s hs.1 hs.2.le (hH s hs.2))).2
  · -- `g` is continuous up to the axis, and at `0` because `φ` diverges at infinity
    refine continuousOn_update_iff.mpr ⟨fun s hs => ?_, fun _ => ?_⟩
    · have hs0 : s ≠ 0 := hs.2
      have hy := hφc _ (hfAq s hs.1.1 hs.1.2 hs0)
      exact ((ContinuousWithinAt.comp (f := fun s => q (-s⁻¹)) hy
        ((hqcont s hs0).mono fun z (hz : z ∈ (ball 0 r ∩ A) \ {0}) => hz.1.2)
        fun z (hz : z ∈ (ball 0 r ∩ A) \ {0}) => hfAq z hz.1.1 hz.1.2 hz.2).inv₀
          (hφ0 s hs.1.1 hs.1.2 hs0)).neg
    · have hq : Tendsto (fun s => q (-s⁻¹)) (𝓝[(ball 0 r ∩ A) \ {0}] 0)
          (cobounded ℂ ⊓ 𝓟 (f '' A)) := by
        refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
        · exact (tendsto_comp_neg_inv_cobounded ((tendsto_const_add_mul_model hb).mono_left
            inf_le_left)).mono_left
              (nhdsWithin_mono _ (sdiff_subset_sdiff_left inter_subset_right))
        · exact eventually_nhdsWithin_of_forall fun s hs => hfAq s hs.1.1 hs.1.2 hs.2
      simpa using (tendsto_inv₀_cobounded.comp ((tendsto_invFunOn_cobounded hA hfc).comp hq)).neg
  · -- `g` is holomorphic above the axis, where `φ` is the holomorphic inverse of `f` on `U`
    have hψ := (hf.invFunOn isOpen_upperHalfPlaneSet (hfi.mono hH0))
    rw [hfU] at hψ
    have hqd : DifferentiableOn ℂ (fun s => q (-s⁻¹)) (ball 0 r ∩ upperHalfPlaneSet) := by
      intro s hs
      have hs' : -s⁻¹ ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (ne_of_gt
        (im_neg_inv_pos.mpr hs.2)))
      exact ((((hasDerivAt_model hs').const_mul b).const_add c).differentiableAt.comp s
        (differentiableAt_inv (hH s hs.2)).neg).differentiableWithinAt
    refine DifferentiableOn.congr (f := fun s => -(invFunOn f upperHalfPlaneSet (q (-s⁻¹)))⁻¹)
      ?_ fun s hs => ?_
    · refine ((hψ.comp hqd fun s hs => hUp s hs.1 hs.2).inv fun s hs => ?_).neg
      rw [comp_apply, ← (hφU _ (hUp s hs.1 hs.2)).2]
      exact hφ0 s hs.1 hs.2.le (hH s hs.2)
    · rw [hgv s (hH s hs.2), (hφU _ (hUp s hs.1 hs.2)).2]
  · -- `g` is real on the axis: the frontier values of the model come from real points
    by_cases hs0 : s = 0
    · rw [hs0, hg0, zero_im]
    have hmem := hφA _ (hfAq s hs hsim.ge hs0)
    have hreal : (φ (q (-s⁻¹))).im = 0 := by
      refine le_antisymm (not_lt.mp fun hlt => hUr s hs hsim hs0 ?_) hmem.1
      rw [← hmem.2, ← hfU]
      exact mem_image_of_mem f hlt
    rw [hgv s hs0]
    simp [inv_im, hreal]
  · -- `g` maps the upper half-plane to itself
    rw [hgv s (hH s hs.2)]
    exact im_neg_inv_pos.mpr (hφU _ (hUp s hs.1 hs.2)).1
  · -- `g` is injective: `φ` is injective on `f '' A` and the model is injective far out
    intro s₁ hs₁ s₂ hs₂ h
    have hne : ∀ s ∈ ball (0 : ℂ) r ∩ A, s ≠ 0 → g s ≠ 0 := fun s hs hs0 => by
      rw [hgv s hs0]
      exact neg_ne_zero.mpr (inv_ne_zero (hφ0 s hs.1 hs.2 hs0))
    by_cases h₁ : s₁ = 0 <;> by_cases h₂ : s₂ = 0
    · rw [h₁, h₂]
    · rw [h₁, hg0] at h
      exact absurd h.symm (hne s₂ hs₂ h₂)
    · rw [h₂, hg0] at h
      exact absurd h (hne s₁ hs₁ h₁)
    · rw [hgv s₁ h₁, hgv s₂ h₂, neg_inj, inv_inj] at h
      have hq : q (-s₁⁻¹) = q (-s₂⁻¹) := by
        rw [← (hφA _ (hfAq s₁ hs₁.1 hs₁.2 h₁)).2, h, (hφA _ (hfAq s₂ hs₂.1 hs₂.2 h₂)).2]
      have hm : model (-s₁⁻¹) = model (-s₂⁻¹) := by
        rw [← hqc, ← hqc, hq]
      have hmem : ∀ s ∈ ball (0 : ℂ) r ∩ A, s ≠ 0 → -s⁻¹ ∈ {ζ : ℂ | 0 ≤ ζ.im ∧ 8 ≤ ‖ζ‖} :=
        fun s hs hs0 => ⟨im_neg_inv_nonneg.mpr hs.2, (hfar s hs.1 hs0).1⟩
      simpa using injOn_model (hmem s₁ hs₁ h₁) (hmem s₂ hs₂ h₂) hm

/-- **The pre-Schwarzian at an end of opening `2 * π`.**  Let `f` map the upper half-plane
holomorphically onto `U`, extend to a continuous injection of the closed upper half-plane, and
tend to infinity at infinity, and let `U` coincide far from `c` with the exterior of the closed
half-strip `{0 ≤ re ((z - c) / b), 0 ≤ im ((z - c) / b) ≤ π}`.  Then `z * f''(z) / f'(z) → 1` as
`z` tends to infinity in the upper half-plane.

So the two parallel unbounded sides of `U` bound a vertex at infinity of opening `2 * π`, and for
a Schwarz--Christoffel map the finite turning exponents then sum to `1`. -/
theorem tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_halfStripExterior {ρ : ℝ} {c b : ℂ}
    (hb : b ≠ 0) (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im}) (hfi : InjOn f {z : ℂ | 0 ≤ z.im})
    (hfU : f '' upperHalfPlaneSet = U)
    (hp : Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (cobounded ℂ))
    (hU : ∀ z : ℂ, ρ < ‖z - c‖ →
      (z ∈ U ↔ ((z - c) / b).re < 0 ∨ ((z - c) / b).im ∉ Icc 0 Real.pi)) :
    Tendsto (fun z => z * logDeriv (deriv f) z) (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 1) := by
  have hH0 : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  have hslit : ∀ ζ ∈ upperHalfPlaneSet, ζ ∈ slitPlane := fun ζ hζ =>
    mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hζ))
  obtain ⟨r, hr, g, hgq, hg0, hcont, hholo, hreal, hupper, hinj⟩ :=
    exists_comparison_of_halfStripExterior hb hf hfc hfi hfU hp hU
  refine tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_comp_neg_inv
    (q := fun ζ => c + b * model ζ) hr hf
    (fun z hz => deriv_ne_zero_of_injOn hf isOpen_upperHalfPlaneSet (hfi.mono hH0) hz)
    (fun ζ hζ => (((hasDerivAt_model (hslit ζ hζ)).const_mul b).const_add c).differentiableAt
      |>.differentiableWithinAt) (fun ζ hζ => ?_)
    (tendsto_mul_logDeriv_deriv_const_add_mul_model hb) hgq hg0 hcont hholo hreal hupper hinj
  -- The model's derivative `b * (ζ - ζ⁻¹)` does not vanish on the upper half-plane.
  rw [(((hasDerivAt_model (hslit ζ hζ)).const_mul b).const_add c).deriv]
  have hζ0 : ζ ≠ 0 := fun h => by simp [h] at hζ
  refine mul_ne_zero hb fun h => sq_sub_one_ne_zero hζ ?_
  field_simp at h
  linear_combination h

end TauCeti
