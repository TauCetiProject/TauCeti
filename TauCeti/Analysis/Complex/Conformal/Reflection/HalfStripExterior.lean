/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Infinity
import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
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

The comparison only uses `f` far out, so it applies equally to an end of opening `2 * π` at a
finite real prevertex `x`.  If `f` tends to infinity at `x` and far out the image of a small upper
half-disc about `x` is the exterior of the half-strip, then reading `f` in the coordinate
`ζ ↦ x - ζ⁻¹` gives an end at infinity of the same kind, and the pre-Schwarzian residue at `x` is
`(z - x) * f''(z) / f'(z) → -3`
(`TauCeti.tendsto_sub_mul_logDeriv_deriv_nhdsWithin_of_halfStripExterior`).

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
  -- Jordan's inequality `arg ζ ≤ π / 2 * sin (arg ζ)`, with `sin (arg ζ) = im ζ / ‖ζ‖`.
  have harg : ζ.arg ≤ Real.pi / 2 * (ζ.im / ‖ζ‖) :=
    (le_pi_div_two_mul_sin (arg_nonneg_iff.mpr him)
      (abs_le.mp (abs_arg_le_pi_div_two_iff.mpr (zero_le_one.trans hre))).2).trans_eq
      (by rw [sin_arg])
  have : ζ.im / ‖ζ‖ ≤ ζ.im / 2 := div_le_div_of_nonneg_left him two_pos hζ
  have := Real.pi_pos
  rw [im_model]
  nlinarith

/-- To the left of `re ζ = -1` the model has imaginary part at most `0`, strictly less off the
axis. -/
private theorem im_model_le {ζ : ℂ} (him : 0 ≤ ζ.im) (hre : ζ.re ≤ -1) (hζ : 2 ≤ ‖ζ‖) :
    (model ζ).im ≤ -((1 - Real.pi / 4) * ζ.im) := by
  have harg : Real.pi / 2 < ζ.arg := by
    have h := mt abs_arg_le_pi_div_two_iff.mp (not_le.mpr (by linarith : ζ.re < 0))
    rwa [not_le, abs_of_nonneg (arg_nonneg_iff.mpr him)] at h
  -- Jordan's inequality for `π - arg ζ ∈ [0, π / 2]`, whose sine is `im ζ / ‖ζ‖`.
  have harg' : Real.pi - ζ.arg ≤ Real.pi / 2 * (ζ.im / ‖ζ‖) :=
    (le_pi_div_two_mul_sin (by linarith [arg_le_pi ζ]) (by linarith)).trans_eq
      (by rw [Real.sin_pi_sub, sin_arg])
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

/-- The model values `c + b * model (-s⁻¹)` are continuous in `s ≠ 0` on the closed upper
half-plane. -/
private theorem continuousWithinAt_const_add_mul_model_neg_inv {c b s : ℂ} (hs : s ≠ 0) :
    ContinuousWithinAt (fun s : ℂ => c + b * model (-s⁻¹)) {z : ℂ | 0 ≤ z.im} s := by
  have hinv : ContinuousAt (fun s : ℂ => -s⁻¹) s := (continuousAt_inv₀ hs).neg
  exact continuousWithinAt_const.add (continuousWithinAt_const.mul
    (ContinuousWithinAt.comp (f := fun s : ℂ => -s⁻¹)
      (continuousWithinAt_model (by simpa using hs)) hinv.continuousWithinAt
      fun z hz => im_neg_inv_nonneg.mpr hz))

/-- If the model values `c + b * model (-s⁻¹)` above the real axis lie in a closed set `S`, then
so do the model values on the real axis, by approaching from above. -/
private theorem const_add_mul_model_neg_inv_mem_of_isClosed {c b : ℂ} {S : Set ℂ} {r : ℝ}
    (hS : IsClosed S)
    (hUp : ∀ s ∈ ball (0 : ℂ) r, 0 < s.im → c + b * model (-s⁻¹) ∈ S) :
    ∀ s ∈ ball (0 : ℂ) r, 0 ≤ s.im → s ≠ 0 → c + b * model (-s⁻¹) ∈ S := by
  intro s hs hsim hs0
  rcases hsim.lt_or_eq with hsim | hsim
  · exact hUp s hs hsim
  have hne : (𝓝[ball (0 : ℂ) r ∩ upperHalfPlaneSet] s).NeBot := by
    have hs' : s = ((s.re : ℝ) : ℂ) := Complex.ext rfl (by simp [← hsim])
    rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds
      (isOpen_ball.mem_nhds hs)), hs']
    exact Real.nhdsWithin_upperHalfPlaneSet_neBot s.re
  refine hS.mem_of_tendsto (f := fun s => c + b * model (-s⁻¹))
    (b := 𝓝[ball 0 r ∩ upperHalfPlaneSet] s) ?_ ?_
  · exact ((continuousWithinAt_const_add_mul_model_neg_inv hs0).mono
      fun z (hz : z ∈ ball 0 r ∩ upperHalfPlaneSet) => (le_of_lt hz.2 : 0 ≤ z.im)).tendsto
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact hUp z hz.1 hz.2

/-- Near `s = 0`, on the punctured ball `‖-s⁻¹‖ ≥ 8`, and for `s` in the closed upper half-disc the
model values `c + b * model (-s⁻¹)` are values of `f` on the part of the upper half-plane outside
the disc of radius `R` exactly when `0 < s.im`: they are in the image for `0 < s.im` and not in
it for `s.im = 0`, `s ≠ 0`. They are never values of `f` on the closed far part within the
closed disc of radius `R`. -/
private theorem exists_ball_model_values {R ρ : ℝ} {c b : ℂ} (hb : b ≠ 0)
    (hfc : ContinuousOn f ({z : ℂ | 0 ≤ z.im} ∩ {z | R ≤ ‖z‖}))
    (hU : ∀ z : ℂ, ρ < ‖z - c‖ → (z ∈ f '' (upperHalfPlaneSet ∩ {z | R < ‖z‖}) ↔
      ((z - c) / b).re < 0 ∨ ((z - c) / b).im ∉ Icc 0 Real.pi)) :
    ∃ r > 0, (∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → 8 ≤ ‖-s⁻¹‖) ∧
      (∀ s ∈ ball (0 : ℂ) r, 0 < s.im →
        c + b * model (-s⁻¹) ∈ f '' (upperHalfPlaneSet ∩ {z | R < ‖z‖})) ∧
      (∀ s ∈ ball (0 : ℂ) r, s.im = 0 → s ≠ 0 →
        c + b * model (-s⁻¹) ∉ f '' (upperHalfPlaneSet ∩ {z | R < ‖z‖})) ∧
      ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → ∀ z ∈ {z : ℂ | 0 ≤ z.im} ∩ {z | R ≤ ‖z‖}, ‖z‖ ≤ R →
        f z ≠ c + b * model (-s⁻¹) := by
  have hA : IsClosed ({z : ℂ | 0 ≤ z.im} ∩ {z | R ≤ ‖z‖}) :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le continuous_const continuous_norm)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) R).inter_left hA).exists_bound_of_continuousOn
    (f := fun z => f z - c) ((hfc.mono inter_subset_left).sub continuousOn_const)
  have hqc : ∀ ζ, (c + b * model ζ - c) / b = model ζ := fun ζ => by
    field_simp
    ring
  obtain ⟨r, hr, hfar⟩ := exists_ball_norm_mul_model_gt hb (max ρ M)
  have hfar' : ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → max ρ M < ‖c + b * model (-s⁻¹) - c‖ :=
    fun s hs hs0 => by simpa using (hfar s hs hs0).2
  have hH : ∀ s : ℂ, 0 < s.im → s ≠ 0 := fun s hs h => by simp [h] at hs
  refine ⟨r, hr, fun s hs hs0 => (hfar s hs hs0).1, fun s hs hsim => ?_,
    fun s hs hsim hs0 h => ?_, fun s hs hs0 z hz hzR hzq => ?_⟩
  · refine (hU _ ((le_max_left _ _).trans_lt (hfar' s hs (hH s hsim)))).mpr ?_
    rw [hqc]
    exact model_mem_exterior (im_neg_inv_pos.mpr hsim) (by linarith [(hfar s hs (hH s hsim)).1])
  · have hm := model_mem_halfStrip (ζ := -s⁻¹) (by simp [hsim])
      (by linarith [(hfar s hs hs0).1])
    rw [hU _ ((le_max_left _ _).trans_lt (hfar' s hs hs0)), hqc] at h
    rcases h with h | h
    · linarith [hm.1]
    · exact h hm.2
  · have hbd : ‖f z - c‖ ≤ M := hM z ⟨hz, mem_closedBall_zero_iff.mpr hzR⟩
    rw [hzq] at hbd
    exact lt_irrefl _ ((hbd.trans (le_max_right _ _)).trans_lt (hfar' s hs hs0))

/-- The comparison map `s ↦ -(f⁻¹ (c + b * model (-s⁻¹)))⁻¹`, filled in by `0` at `0`, is
continuous on the closed upper half-disc `ball 0 r ∩ {0 ≤ im}`, where `A` is closed, `f` is
continuous on `A`, `f⁻¹ = invFunOn f A` is continuous on `f '' A`, and the model values for
`s ≠ 0` lie in `f '' A` with nonzero preimage. Continuity at `0` uses that `f⁻¹` diverges at
infinity, which follows from `A` closed and `f` continuous. -/
private theorem continuousOn_update_neg_inv_invFunOn {A : Set ℂ} {c b : ℂ} {r : ℝ}
    (hb : b ≠ 0) (hA : IsClosed A) (hfc : ContinuousOn f A)
    (hφc : ContinuousOn (invFunOn f A) (f '' A))
    (hfAq : ∀ s ∈ ball (0 : ℂ) r, 0 ≤ s.im → s ≠ 0 → c + b * model (-s⁻¹) ∈ f '' A)
    (hφ0 : ∀ s ∈ ball (0 : ℂ) r, 0 ≤ s.im → s ≠ 0 → invFunOn f A (c + b * model (-s⁻¹)) ≠ 0) :
    ContinuousOn (update (fun s : ℂ => -(invFunOn f A (c + b * model (-s⁻¹)))⁻¹) 0 0)
      (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) := by
  refine continuousOn_update_iff.mpr ⟨fun s hs => ?_, fun _ => ?_⟩
  · have hs0 : s ≠ 0 := hs.2
    have hy := hφc _ (hfAq s hs.1.1 hs.1.2 hs0)
    exact ((ContinuousWithinAt.comp (f := fun s => c + b * model (-s⁻¹)) hy
      ((continuousWithinAt_const_add_mul_model_neg_inv hs0).mono
        fun z (hz : z ∈ (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) \ {0}) => hz.1.2)
      fun z (hz : z ∈ (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) \ {0}) =>
        hfAq z hz.1.1 hz.1.2 hz.2).inv₀ (hφ0 s hs.1.1 hs.1.2 hs0)).neg
  · have hq : Tendsto (fun s => c + b * model (-s⁻¹))
        (𝓝[(ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) \ {0}] 0) (cobounded ℂ ⊓ 𝓟 (f '' A)) := by
      refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
      · exact (tendsto_comp_neg_inv_cobounded ((tendsto_const_add_mul_model hb).mono_left
          inf_le_left)).mono_left
            (nhdsWithin_mono _ (sdiff_subset_sdiff_left inter_subset_right))
      · exact eventually_nhdsWithin_of_forall fun s hs => hfAq s hs.1.1 hs.1.2 hs.2
    have hφ := (tendsto_invFunOn_cobounded_cocompact hA hfc).mono_right cobounded_eq_cocompact.ge
    simpa using (tendsto_inv₀_cobounded.comp (hφ.comp hq)).neg

/-- The comparison map is holomorphic on the open upper half-disc, where `f⁻¹` agrees with the
holomorphic inverse of `f` on the open set `T`. -/
private theorem differentiableOn_update_neg_inv_invFunOn {A T : Set ℂ} {c b : ℂ} {r : ℝ}
    (hT : IsOpen T) (hf : DifferentiableOn ℂ f T) (hfi : InjOn f T)
    (hφU : ∀ y ∈ f '' T, invFunOn f A y ∈ T ∧ invFunOn f A y = invFunOn f T y)
    (hUp : ∀ s ∈ ball (0 : ℂ) r, 0 < s.im → c + b * model (-s⁻¹) ∈ f '' T)
    (hφ0 : ∀ s ∈ ball (0 : ℂ) r, 0 ≤ s.im → s ≠ 0 → invFunOn f A (c + b * model (-s⁻¹)) ≠ 0) :
    DifferentiableOn ℂ (update (fun s : ℂ => -(invFunOn f A (c + b * model (-s⁻¹)))⁻¹) 0 0)
      (ball 0 r ∩ upperHalfPlaneSet) := by
  have hH : ∀ s ∈ upperHalfPlaneSet, s ≠ 0 := fun s (hs : 0 < s.im) h => by simp [h] at hs
  have hψ := hf.invFunOn hT hfi
  have hqd : DifferentiableOn ℂ (fun s => c + b * model (-s⁻¹)) (ball 0 r ∩ upperHalfPlaneSet) := by
    intro s hs
    have hs' : -s⁻¹ ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inr (ne_of_gt
      (im_neg_inv_pos.mpr hs.2)))
    exact ((((hasDerivAt_model hs').const_mul b).const_add c).differentiableAt.comp s
      (differentiableAt_inv (hH s hs.2)).neg).differentiableWithinAt
  refine DifferentiableOn.congr (f := fun s => -(invFunOn f T (c + b * model (-s⁻¹)))⁻¹)
    ?_ fun s hs => ?_
  · refine ((hψ.comp hqd fun s hs => hUp s hs.1 hs.2).inv fun s hs => ?_).neg
    rw [comp_apply, ← (hφU _ (hUp s hs.1 hs.2)).2]
    exact hφ0 s hs.1 hs.2.le (hH s hs.2)
  · rw [update_of_ne (hH s hs.2), (hφU _ (hUp s hs.1 hs.2)).2]

/-- The comparison map is injective on the closed upper half-disc: `f⁻¹` is injective on the
image of `A` and the model is injective far out. -/
private theorem injOn_update_neg_inv_invFunOn {A : Set ℂ} {c b : ℂ} {r : ℝ} (hb : b ≠ 0)
    (hfar : ∀ s ∈ ball (0 : ℂ) r, s ≠ 0 → 8 ≤ ‖-s⁻¹‖)
    (hfAq : ∀ s ∈ ball (0 : ℂ) r, 0 ≤ s.im → s ≠ 0 → c + b * model (-s⁻¹) ∈ f '' A)
    (hφ0 : ∀ s ∈ ball (0 : ℂ) r, 0 ≤ s.im → s ≠ 0 → invFunOn f A (c + b * model (-s⁻¹)) ≠ 0) :
    InjOn (update (fun s : ℂ => -(invFunOn f A (c + b * model (-s⁻¹)))⁻¹) 0 0)
      (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) := by
  intro s₁ hs₁ s₂ hs₂ h
  have hne : ∀ s ∈ ball (0 : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}, s ≠ 0 →
      update (fun s : ℂ => -(invFunOn f A (c + b * model (-s⁻¹)))⁻¹) 0 0 s ≠ 0 :=
    fun s hs hs0 => by
      rw [update_of_ne hs0]
      exact neg_ne_zero.mpr (inv_ne_zero (hφ0 s hs.1 hs.2 hs0))
  by_cases h₁ : s₁ = 0 <;> by_cases h₂ : s₂ = 0
  · rw [h₁, h₂]
  · rw [h₁, update_self] at h
    exact absurd h.symm (hne s₂ hs₂ h₂)
  · rw [h₂, update_self] at h
    exact absurd h (hne s₁ hs₁ h₁)
  · rw [update_of_ne h₁, update_of_ne h₂, neg_inj, inv_inj] at h
    have hq : c + b * model (-s₁⁻¹) = c + b * model (-s₂⁻¹) := by
      rw [← invFunOn_eq (hfAq s₁ hs₁.1 hs₁.2 h₁), h, invFunOn_eq (hfAq s₂ hs₂.1 hs₂.2 h₂)]
    have hmem : ∀ s ∈ ball (0 : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}, s ≠ 0 →
        -s⁻¹ ∈ {ζ : ℂ | 0 ≤ ζ.im ∧ 8 ≤ ‖ζ‖} :=
      fun s hs hs0 => ⟨im_neg_inv_nonneg.mpr hs.2, hfar s hs.1 hs0⟩
    simpa using injOn_model (hmem s₁ hs₁ h₁) (hmem s₂ hs₂ h₂)
      (mul_left_cancel₀ hb (add_left_cancel hq))

/-- **The comparison map.**  Let `f` be holomorphic on the part of the upper half-plane outside
the closed disc of radius `R ≥ 0`, continuous and injective on the closure of that part, and tend
to infinity at infinity, and let its image coincide far from `c` with the exterior of the closed
half-strip `{0 ≤ re ((z - c) / b), 0 ≤ im ((z - c) / b) ≤ π}`.  In the coordinate `s ↦ -s⁻¹` at
infinity the map `f⁻¹ ∘ (c + b * model)` is then a function `g` with `g 0 = 0` which is continuous
and injective up to a real segment through `0`, holomorphic and upper half-plane valued above it,
and real on it.

Only the far part of `f` matters, so the same comparison serves a map of the whole upper half-plane
(`R = 0`) and a map near a finite prevertex, read in the coordinate `z ↦ x - z⁻¹`. -/
private theorem exists_comparison_of_halfStripExterior {R ρ : ℝ} {c b : ℂ} (hR : 0 ≤ R)
    (hb : b ≠ 0) (hf : DifferentiableOn ℂ f (upperHalfPlaneSet ∩ {z | R < ‖z‖}))
    (hfc : ContinuousOn f ({z : ℂ | 0 ≤ z.im} ∩ {z | R ≤ ‖z‖}))
    (hfi : InjOn f ({z : ℂ | 0 ≤ z.im} ∩ {z | R ≤ ‖z‖}))
    (hp : Tendsto f (cobounded ℂ ⊓ 𝓟 ({z : ℂ | 0 ≤ z.im} ∩ {z | R ≤ ‖z‖})) (cobounded ℂ))
    (hU : ∀ z : ℂ, ρ < ‖z - c‖ → (z ∈ f '' (upperHalfPlaneSet ∩ {z | R < ‖z‖}) ↔
      ((z - c) / b).re < 0 ∨ ((z - c) / b).im ∉ Icc 0 Real.pi)) :
    ∃ r > 0, ∃ g : ℂ → ℂ,
      EqOn (fun s => f (-(g s)⁻¹)) (fun s => c + b * model (-s⁻¹))
        (ball 0 r ∩ upperHalfPlaneSet) ∧ g 0 = 0 ∧
      ContinuousOn g (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      DifferentiableOn ℂ g (ball 0 r ∩ upperHalfPlaneSet) ∧
      (∀ z ∈ ball (0 : ℂ) r, z.im = 0 → (g z).im = 0) ∧
      MapsTo g (ball 0 r ∩ upperHalfPlaneSet) upperHalfPlaneSet ∧
      InjOn g (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) := by
  set A := {z : ℂ | 0 ≤ z.im} ∩ {z | R ≤ ‖z‖}
  set T := upperHalfPlaneSet ∩ {z : ℂ | R < ‖z‖}
  have hA : IsClosed A :=
    (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le continuous_const continuous_norm)
  have hT : IsOpen T :=
    isOpen_upperHalfPlaneSet.inter (isOpen_lt continuous_const continuous_norm)
  have hH0 : T ⊆ A := inter_subset_inter (ofPred_subset_ofPred.mpr fun _ => le_of_lt)
    (ofPred_subset_ofPred.mpr fun _ => le_of_lt)
  have hH : ∀ s ∈ upperHalfPlaneSet, s ≠ 0 := fun s (hs : 0 < s.im) h => by simp [h] at hs
  -- `f` is a closed embedding of `A`; `φ` is its continuous inverse on the closed image.
  set φ := invFunOn f A
  have hp' : Tendsto f (cocompact ℂ ⊓ 𝓟 A) (cobounded ℂ) := by rwa [← cobounded_eq_cocompact]
  have hfA : IsClosed (f '' A) := isClosed_image_of_tendsto_cobounded hA hfc hp'
  have hφc : ContinuousOn φ (f '' A) :=
    continuousOn_of_leftInvOn_of_tendsto_cobounded hA hfc hfi.leftInvOn_invFunOn hp'
  have hφA : ∀ y ∈ f '' A, φ y ∈ A ∧ f (φ y) = y := fun y hy => ⟨invFunOn_mem hy, invFunOn_eq hy⟩
  have hφU : ∀ y ∈ f '' T, φ y ∈ T ∧ φ y = invFunOn f T y := by
    rintro y ⟨z, hz, rfl⟩
    have hφf : φ (f z) = z := by simpa only [φ] using hfi.leftInvOn_invFunOn (hH0 hz)
    rw [hφf, (hfi.mono hH0).leftInvOn_invFunOn hz]
    exact ⟨hz, rfl⟩
  -- The far model values `c + b * model (-s⁻¹)` are values of `f` on `A`, but not inside the disc.
  obtain ⟨r, hr, hfar, hUp, hUr, hout⟩ := exists_ball_model_values hb hfc hU
  have hfAq := const_add_mul_model_neg_inv_mem_of_isClosed hfA
    fun s hs hsim => image_mono hH0 (hUp s hs hsim)
  have hφR : ∀ s ∈ ball (0 : ℂ) r, 0 ≤ s.im → s ≠ 0 → R < ‖φ (c + b * model (-s⁻¹))‖ :=
    fun s hs hsim hs0 => not_le.mp fun hle => hout s hs hs0 _ (hφA _ (hfAq s hs hsim hs0)).1 hle
      (hφA _ (hfAq s hs hsim hs0)).2
  have hφ0 : ∀ s ∈ ball (0 : ℂ) r, 0 ≤ s.im → s ≠ 0 → φ (c + b * model (-s⁻¹)) ≠ 0 :=
    fun s hs hsim hs0 => norm_pos_iff.mp (hR.trans_lt (hφR s hs hsim hs0))
  -- The comparison map `g = -1 / φ (c + b * model (-1 / s))`, filled in by `0` at `0`.
  refine ⟨r, hr, update (fun s => -(φ (c + b * model (-s⁻¹)))⁻¹) 0 0, fun s hs => ?_,
    update_self _ _ _, continuousOn_update_neg_inv_invFunOn hb hA hfc hφc hfAq hφ0,
    differentiableOn_update_neg_inv_invFunOn hT hf (hfi.mono hH0) hφU hUp hφ0,
    fun s hs hsim => ?_, fun s hs => ?_, injOn_update_neg_inv_invFunOn hb hfar hfAq hφ0⟩
  · -- `f (-1 / g s) = c + b * model (-1 / s)`
    dsimp only
    rw [update_of_ne (hH s hs.2), inv_neg, inv_inv, neg_neg]
    exact (hφA _ (hfAq s hs.1 hs.2.le (hH s hs.2))).2
  · -- `g` is real on the axis: the frontier values of the model come from real points
    by_cases hs0 : s = 0
    · rw [hs0, update_self, zero_im]
    have hmem := hφA _ (hfAq s hs hsim.ge hs0)
    have hreal : (φ (c + b * model (-s⁻¹))).im = 0 := by
      refine le_antisymm (not_lt.mp fun hlt => hUr s hs hsim hs0 ?_) hmem.1.1
      rw [← hmem.2]
      exact mem_image_of_mem f ⟨hlt, hφR s hs hsim.ge hs0⟩
    rw [update_of_ne hs0]
    simp [inv_im, hreal]
  · -- `g` maps the upper half-plane to itself
    rw [update_of_ne (hH s hs.2)]
    exact im_neg_inv_pos.mpr (hφU _ (hUp s hs.1 hs.2)).1.1

/-- The model's derivative `b * (ζ - ζ⁻¹)` does not vanish on the upper half-plane. -/
private theorem deriv_const_add_mul_model_ne_zero {c b : ℂ} (hb : b ≠ 0) {ζ : ℂ}
    (hζ : ζ ∈ upperHalfPlaneSet) : deriv (fun ζ => c + b * model ζ) ζ ≠ 0 := by
  rw [(((hasDerivAt_model (mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hζ)))).const_mul b).const_add
    c).deriv]
  have hζ0 : ζ ≠ 0 := fun h => by simp [h] at hζ
  refine mul_ne_zero hb fun h => sq_sub_one_ne_zero hζ ?_
  field_simp at h
  linear_combination h

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
  -- With inner radius `0`, the far parts of the half-planes are the half-planes themselves.
  have hT : upperHalfPlaneSet ∩ {z : ℂ | 0 < ‖z‖} = upperHalfPlaneSet :=
    inter_eq_left.mpr fun z (hz : 0 < z.im) => norm_pos_iff.mpr fun h => by simp [h] at hz
  have hA : {z : ℂ | 0 ≤ z.im} ∩ {z : ℂ | 0 ≤ ‖z‖} = {z : ℂ | 0 ≤ z.im} :=
    inter_eq_left.mpr fun z _ => norm_nonneg z
  obtain ⟨r, hr, g, hgq, hg0, hcont, hholo, hreal, hupper, hinj⟩ :=
    exists_comparison_of_halfStripExterior le_rfl hb (by rwa [hT]) (by rwa [hA]) (by rwa [hA])
      (by rwa [hA]) (fun z hz => by rw [hT, hfU]; exact hU z hz)
  exact tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_comp_neg_inv hr
    (fun z hz => deriv_ne_zero_of_injOn hf isOpen_upperHalfPlaneSet (hfi.mono hH0) hz)
    (fun ζ hζ => deriv_const_add_mul_model_ne_zero hb hζ)
    (tendsto_mul_logDeriv_deriv_const_add_mul_model hb) hgq hg0 hcont hholo hreal hupper hinj

/-- The coordinate change `ζ ↦ x - ζ⁻¹` carries the far part of the closed upper half-plane into
the closed upper half-disc about `x` with `x` removed, and the open far parts onto the open
upper half-disc. It is continuous and injective on the closed far part, holomorphic on the open
far part, and sends infinity to `x` within the closed upper half-plane. -/
private theorem sub_inv_coordinate_change {x r : ℝ} (hr : 0 < r) :
    MapsTo (fun ζ : ℂ => (x : ℂ) - ζ⁻¹) ({z : ℂ | 0 ≤ z.im} ∩ {z | r⁻¹ ≤ ‖z‖})
      ((closedBall (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) \ {(x : ℂ)}) ∧
    (fun ζ : ℂ => (x : ℂ) - ζ⁻¹) '' (upperHalfPlaneSet ∩ {z : ℂ | r⁻¹ < ‖z‖}) =
      ball (x : ℂ) r ∩ upperHalfPlaneSet ∧
    ContinuousOn (fun ζ : ℂ => (x : ℂ) - ζ⁻¹) ({z : ℂ | 0 ≤ z.im} ∩ {z | r⁻¹ ≤ ‖z‖}) ∧
    DifferentiableOn ℂ (fun ζ : ℂ => (x : ℂ) - ζ⁻¹) (upperHalfPlaneSet ∩ {z : ℂ | r⁻¹ < ‖z‖}) ∧
    InjOn (fun ζ : ℂ => (x : ℂ) - ζ⁻¹) ({z : ℂ | 0 ≤ z.im} ∩ {z | r⁻¹ ≤ ‖z‖}) ∧
    Tendsto (fun ζ : ℂ => (x : ℂ) - ζ⁻¹)
      (cobounded ℂ ⊓ 𝓟 ({z : ℂ | 0 ≤ z.im} ∩ {z | r⁻¹ ≤ ‖z‖}))
      (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ)) := by
  set m : ℂ → ℂ := fun ζ => (x : ℂ) - ζ⁻¹
  set A := {z : ℂ | 0 ≤ z.im} ∩ {z | r⁻¹ ≤ ‖z‖}
  set T := upperHalfPlaneSet ∩ {z : ℂ | r⁻¹ < ‖z‖}
  have him : ∀ ζ : ℂ, (m ζ).im = (-ζ⁻¹).im := fun ζ => by simp [m, sub_eq_add_neg]
  have hdist : ∀ ζ : ℂ, dist (m ζ) x = ‖ζ‖⁻¹ := fun ζ => by simp [m]
  have hA0 : ∀ ζ ∈ A, 0 < ‖ζ‖ := fun ζ hζ => (inv_pos.mpr hr).trans_le hζ.2
  have hmA : MapsTo m A ((closedBall (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) \ {(x : ℂ)}) :=
    fun ζ hζ => ⟨⟨by rw [mem_closedBall, hdist]; exact (inv_le_comm₀ hr (hA0 ζ hζ)).mp hζ.2,
      (im_neg_inv_nonneg.mpr hζ.1).trans_eq (him ζ).symm⟩,
      fun h => by simp [m, norm_pos_iff.mp (hA0 ζ hζ)] at h⟩
  have hmT : m '' T = ball (x : ℂ) r ∩ upperHalfPlaneSet := by
    ext z
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      have hζ0 : 0 < ‖ζ‖ := (inv_pos.mpr hr).trans hζ.2
      exact ⟨by rw [mem_ball, hdist]; exact (inv_lt_comm₀ hr hζ0).mp hζ.2,
        (im_neg_inv_pos.mpr hζ.1).trans_eq (him ζ).symm⟩
    · rintro ⟨hz, hzH⟩
      have hzx : 0 < ‖z - x‖ := norm_pos_iff.mpr fun h => by
        have : z = x := sub_eq_zero.mp h
        simp [this] at hzH
      refine ⟨-(z - x)⁻¹, ⟨im_neg_inv_pos.mpr (by simpa using hzH), ?_⟩, by simp [m]⟩
      have hlt : r⁻¹ < ‖-(z - x)⁻¹‖ := by
        rw [norm_neg, norm_inv]
        exact inv_lt_inv₀ hr hzx |>.mpr (by rwa [mem_ball, dist_eq_norm] at hz)
      exact hlt
  have hmc : ContinuousOn m A := continuousOn_const.sub
    (continuousOn_inv₀.mono fun ζ hζ => norm_pos_iff.mp (hA0 ζ hζ))
  have hmd : DifferentiableOn ℂ m T := (differentiableOn_const _).sub
    (differentiableOn_inv.mono fun ζ hζ => norm_pos_iff.mp ((inv_pos.mpr hr).trans hζ.2))
  have hmi : InjOn m A := fun ζ₁ _ ζ₂ _ h => inv_injective (sub_right_injective (b := (x : ℂ)) h)
  have hmp : Tendsto m (cobounded ℂ ⊓ 𝓟 A) (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa [m] using ((tendsto_const_nhds (x := (x : ℂ))).sub
        (tendsto_inv₀_cobounded (α := ℂ))).mono_left (inf_le_left (b := 𝓟 A))
    · filter_upwards [mem_inf_of_right (mem_principal_self A)] with ζ hζ
      exact ⟨(hmA hζ).1.2, (hmA hζ).2⟩
  exact ⟨hmA, hmT, hmc, hmd, hmi, hmp⟩

/-- **The pre-Schwarzian residue at a finite prevertex of an end of opening `2 * π`.**  Let `f`
be holomorphic on the upper half of the disc of radius `r` about a real point `x`, continuous and
injective on the closed upper half-disc with `x` removed, and tend to infinity at `x`.  Suppose
that far from `c` the image of the open upper half-disc coincides with the exterior of the closed
half-strip `{0 ≤ re ((z - c) / b), 0 ≤ im ((z - c) / b) ≤ π}`.  Then
`(z - x) * f''(z) / f'(z) → -3` as `z` tends to `x` in the upper half-plane.

So the prevertex `x` represents a vertex at infinity of opening `2 * π`, and its turning exponent
is `-3`.  This is the finite-prevertex counterpart of
`TauCeti.tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_halfStripExterior`. -/
theorem tendsto_sub_mul_logDeriv_deriv_nhdsWithin_of_halfStripExterior {x r ρ : ℝ} {c b : ℂ}
    (hr : 0 < r) (hb : b ≠ 0) (hf : DifferentiableOn ℂ f (ball (x : ℂ) r ∩ upperHalfPlaneSet))
    (hfc : ContinuousOn f ((closedBall (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) \ {(x : ℂ)}))
    (hfi : InjOn f ((closedBall (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) \ {(x : ℂ)}))
    (hp : Tendsto f (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ)) (cobounded ℂ))
    (hU : ∀ w : ℂ, ρ < ‖w - c‖ → (w ∈ f '' (ball (x : ℂ) r ∩ upperHalfPlaneSet) ↔
      ((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)) :
    Tendsto (fun z => (z - x) * logDeriv (deriv f) z) (𝓝[upperHalfPlaneSet] (x : ℂ))
      (𝓝 (-3)) := by
  -- In the coordinate `m ζ = x - ζ⁻¹`, the end at `x` becomes an end at infinity, and the
  -- closed upper half-disc about `x` corresponds to the far part of the closed upper half-plane.
  set m : ℂ → ℂ := fun ζ => (x : ℂ) - ζ⁻¹
  set A := {z : ℂ | 0 ≤ z.im} ∩ {z | r⁻¹ ≤ ‖z‖}
  set T := upperHalfPlaneSet ∩ {z : ℂ | r⁻¹ < ‖z‖}
  obtain ⟨hmA, hmT, hmc, hmd, hmi, hmp⟩ := sub_inv_coordinate_change (x := x) hr
  obtain ⟨r₀, hr₀, g, hgq, hg0, hcont, hholo, hreal, hupper, hinj⟩ :=
    exists_comparison_of_halfStripExterior (f := fun ζ => f (m ζ)) (inv_pos.mpr hr).le hb
      (hf.comp hmd (hmT ▸ mapsTo_image m T)) (hfc.comp hmc hmA) (hfi.comp hmi hmA) (hp.comp hmp)
      (fun w hw => by rw [← image_image, hmT]; exact hU w hw)
  -- Since `m (-(g s)⁻¹) = x + g s`, the translate `w ↦ f (x + w)` is compared with the model.
  have hlim := tendsto_mul_logDeriv_deriv_nhdsWithin_of_eqOn_comp (F := fun w => f (x + w))
    hr₀ (fun ζ hζ => deriv_const_add_mul_model_ne_zero hb hζ)
    (tendsto_mul_logDeriv_deriv_const_add_mul_model hb)
    (fun s hs => by simpa [m, sub_eq_add_neg] using hgq hs) hg0 hcont hholo hreal hupper hinj
  have hshift : Tendsto (fun z : ℂ => z - x) (𝓝[upperHalfPlaneSet] (x : ℂ))
      (𝓝[upperHalfPlaneSet] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
    · simpa using ((continuous_sub_right (x : ℂ)).tendsto (x : ℂ)).mono_left
        (nhdsWithin_le_nhds (s := upperHalfPlaneSet))
    · simpa using hz
  have hderiv : deriv (fun w => f (x + w)) = fun w => deriv f (x + w) :=
    funext fun _ => deriv_comp_const_add _ _ _
  norm_num at hlim
  refine (hlim.comp hshift).congr fun z => ?_
  simp only [comp_apply, hderiv, logDeriv_apply, deriv_comp_const_add, add_sub_cancel]

end TauCeti
