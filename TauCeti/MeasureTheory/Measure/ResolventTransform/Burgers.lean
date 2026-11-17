/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.ODE.Gronwall

/-!
# Uniqueness for the Burgers equation of resolvent transforms

Let `t ↦ μ t`, for `t : ℝ≥0`, be a family of probability measures on `ℝ` with resolvent
transforms `m_t(z) = ∫ (x - z)⁻¹ dμ_t(x)` (Mathlib's `MeasureTheory.resolventTransform`). This
file studies the complex Burgers equation `∂_t m_t = m_t ∂_z m_t` on the upper half-plane, in
the integrated form
`m_t(z) = m_0(z) + ∫₀ᵗ m_s(z) m_s'(z) ds` for `Im z > 0`.
For the transform `G_t = -m_t` with kernel `(z - x)⁻¹` it reads `∂_t G_t + G_t ∂_z G_t = 0`.
This is the equation characterizing the limit of the empirical eigenvalue measures of Dyson
Brownian motion; from `μ 0 = δ_a` it is solved by the semicircle family
`TauCeti.Probability.semicircleReal a t` (AGZ, Exercise 4.3.18).

The equation is solved by characteristics. Along `s ↦ z - s m_0(z)` the transform `m_s` stays
equal to `m_0(z)` as long as the characteristic remains at height at least `Im z / 2`, which holds
up to time `t` when `2t < (Im z)²`. Since the characteristic map `z ↦ z - t m_0(z)` is a local
diffeomorphism for `Im z` large, `m_t` is determined by `m_0` on an open set, hence on the whole
upper half-plane by analytic continuation, and so `μ t` is determined by `μ 0`.

## Main results

* `TauCeti.resolventTransform_sub_mul_resolventTransform_of_burgers`: the transform is constant
  along characteristics, `m_t(z - t m_0(z)) = m_0(z)` for `Im z > 0` and `2t < (Im z)²`. Writing
  `w = z - t m_0(z)`, this is the subordination equation `m_t(w) = m_0(w + t m_t(w))`.
* `TauCeti.eq_of_resolventTransform_burgers`: two solutions with the same initial measure agree
  at every time.

## Implementation notes

The hypotheses ask the integrand `s ↦ m_s(z) m_s'(z)` to be interval integrable. Lean's interval
integral of a non-integrable function is `0`, so without this hypothesis the integrated equation
would not express the differential one.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.2.
-/

public section

noncomputable section

open MeasureTheory Complex Filter Set Topology Metric Asymptotics
open scoped NNReal

namespace TauCeti

section Bounds

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {y : ℝ} {w w' : ℂ}

/-- The transform of a probability measure is bounded by `y⁻¹` at height at least `y`. -/
private lemma norm_resolventTransform_le_inv (hy : 0 < y) (hw : y ≤ w.im) :
    ‖resolventTransform ρ w‖ ≤ y⁻¹ := by
  have hw0 : 0 < w.im := hy.trans_le hw
  refine (norm_resolventTransform_le hw0.ne').trans ?_
  rw [probReal_univ, mul_one, abs_of_pos hw0]
  exact inv_anti₀ hy hw

/-- The derivative of the transform is bounded by `y⁻²` at height at least `y`. -/
private lemma norm_deriv_resolventTransform_le_inv (hy : 0 < y) (hw : y ≤ w.im) :
    ‖deriv (resolventTransform ρ) w‖ ≤ y⁻¹ ^ 2 := by
  have hw0 : 0 < w.im := hy.trans_le hw
  refine (norm_deriv_resolventTransform_le hw0.ne').trans ?_
  rw [probReal_univ, mul_one, abs_of_pos hw0]
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hy hw) 2

/-- The product `m m'` is `3 y⁻⁴`-Lipschitz at height at least `y`. -/
private lemma norm_mul_deriv_resolventTransform_sub_le (hy : 0 < y) (hw : y ≤ w.im)
    (hw' : y ≤ w'.im) :
    ‖resolventTransform ρ w * deriv (resolventTransform ρ) w -
      resolventTransform ρ w' * deriv (resolventTransform ρ) w'‖ ≤ 3 * y⁻¹ ^ 4 * ‖w - w'‖ := by
  have h0 : 0 < w.im := hy.trans_le hw
  have h0' : 0 < w'.im := hy.trans_le hw'
  have hi : w.im⁻¹ ≤ y⁻¹ := inv_anti₀ hy hw
  have hi' : w'.im⁻¹ ≤ y⁻¹ := inv_anti₀ hy hw'
  have hm : ‖resolventTransform ρ w - resolventTransform ρ w'‖ ≤ y⁻¹ ^ 2 * ‖w - w'‖ := by
    refine (norm_resolventTransform_sub_le h0.ne' h0'.ne').trans ?_
    rw [probReal_univ, mul_one, abs_of_pos h0, abs_of_pos h0', div_eq_mul_inv, mul_inv]
    calc ‖w - w'‖ * (w.im⁻¹ * w'.im⁻¹) ≤ ‖w - w'‖ * (y⁻¹ * y⁻¹) := by gcongr
      _ = _ := by ring
  have hd : ‖deriv (resolventTransform ρ) w - deriv (resolventTransform ρ) w'‖ ≤
      2 * y⁻¹ ^ 3 * ‖w - w'‖ := by
    refine (norm_deriv_resolventTransform_sub_le h0.ne' h0'.ne').trans ?_
    rw [probReal_univ, mul_one, abs_of_pos h0, abs_of_pos h0']
    calc ‖w - w'‖ * (w.im⁻¹ * w'.im⁻¹ * (w.im⁻¹ + w'.im⁻¹)) ≤
        ‖w - w'‖ * (y⁻¹ * y⁻¹ * (y⁻¹ + y⁻¹)) := by gcongr
      _ = _ := by ring
  rw [show ∀ a b c d : ℂ, a * b - c * d = (a - c) * b + c * (b - d) from fun _ _ _ _ ↦ by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  calc _ ≤ y⁻¹ ^ 2 * ‖w - w'‖ * y⁻¹ ^ 2 + y⁻¹ * (2 * y⁻¹ ^ 3 * ‖w - w'‖) := by
        gcongr
        · exact norm_deriv_resolventTransform_le_inv hy hw
        · exact norm_resolventTransform_le_inv hy hw'
    _ = _ := by ring

/-- The characteristic point `z - s m(z)` stays at height at least `Im z / 2` while
`2 s < (Im z)²`, since `Im m(z) ≤ (Im z)⁻¹`. -/
private lemma half_im_le_im_sub_mul_resolventTransform {z : ℂ} (hz : 0 < z.im) {s : ℝ}
    (hs : 0 ≤ s) (hsz : 2 * s < z.im ^ 2) :
    z.im / 2 ≤ (z - s * resolventTransform ρ z).im := by
  have hc : (resolventTransform ρ z).im ≤ z.im⁻¹ :=
    (im_le_norm _).trans (norm_resolventTransform_le_inv hz le_rfl)
  have h1 : s * (resolventTransform ρ z).im ≤ s * z.im⁻¹ := mul_le_mul_of_nonneg_left hc hs
  have h2 : s * z.im⁻¹ ≤ z.im / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hz]
    nlinarith
  simp only [sub_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
  linarith

/-- For `T ≥ 0`, the characteristic map `Φ(z) = z - T m(z)` is a local homeomorphism at some point
`z₁` with `2T < (Im z₁)²`: on the imaginary axis high enough, `‖T m'(z₁)‖ < 1`, so the inverse
function theorem applies. -/
private lemma exists_map_nhds_sub_mul_resolventTransform {T : ℝ} (hT : 0 ≤ T) :
    ∃ z₁ : ℂ, 0 < z₁.im ∧ 2 * T < z₁.im ^ 2 ∧ 0 < (z₁ - T * resolventTransform ρ z₁).im ∧
      map (fun z : ℂ ↦ z - T * resolventTransform ρ z) (𝓝 z₁) =
        𝓝 (z₁ - T * resolventTransform ρ z₁) := by
  set Y : ℝ := √(2 * T) + 1
  have hY : 0 < Y := by positivity
  have hYT : 2 * T < Y ^ 2 := by
    have := Real.sq_sqrt (show 0 ≤ 2 * T by positivity)
    nlinarith [Real.sqrt_nonneg (2 * T)]
  set z₁ : ℂ := Y * I
  have hz₁ : z₁.im = Y := by simp [z₁]
  have hd : ‖(T : ℂ) * deriv (resolventTransform ρ) z₁‖ < 1 := by
    rw [norm_mul, norm_real, Real.norm_of_nonneg hT]
    calc T * ‖deriv (resolventTransform ρ) z₁‖ ≤ T * Y⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_left (norm_deriv_resolventTransform_le_inv hY hz₁.ge) hT
      _ < 1 := by
        rw [inv_pow, ← div_eq_mul_inv, div_lt_one (by positivity)]
        linarith
  have han : AnalyticAt ℂ (resolventTransform ρ) z₁ :=
    analyticOnNhd_resolventTransform z₁ (by simp [hz₁, hY.ne'])
  have hΦ : HasStrictDerivAt (fun z : ℂ ↦ z - T * resolventTransform ρ z)
      (1 - T * deriv (resolventTransform ρ) z₁) z₁ :=
    (hasStrictDerivAt_id z₁).sub (han.hasStrictDerivAt.const_mul (T : ℂ))
  have hΦ' : 1 - (T : ℂ) * deriv (resolventTransform ρ) z₁ ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hd
    exact lt_irrefl _ hd
  have him := half_im_le_im_sub_mul_resolventTransform (ρ := ρ) (z := z₁) (by simpa [hz₁]) hT
    (by simpa [hz₁])
  rw [hz₁] at him
  exact ⟨z₁, hz₁ ▸ hY, hz₁ ▸ hYT, (half_pos hY).trans_le him, hΦ.map_nhds_eq hΦ'⟩

end Bounds

section Burgers

variable {μ : ℝ≥0 → Measure ℝ} [∀ t, IsProbabilityMeasure (μ t)]

variable
    (hint : ∀ z : ℂ, 0 < z.im → ∀ t : ℝ≥0, IntervalIntegrable (fun s : ℝ ↦
      resolventTransform (μ s.toNNReal) z * deriv (resolventTransform (μ s.toNNReal)) z)
      volume 0 t)
    (heq : ∀ z : ℂ, 0 < z.im → ∀ t : ℝ≥0, resolventTransform (μ t) z =
      resolventTransform (μ 0) z + ∫ s in (0 : ℝ)..t,
        resolventTransform (μ s.toNNReal) z * deriv (resolventTransform (μ s.toNNReal)) z)

include hint heq

omit [∀ t, IsProbabilityMeasure (μ t)] in
/-- Under the Burgers equation, the increment of `m_s(w)` between two times is the integral of
`m_r(w) m_r'(w)` between them. -/
private lemma resolventTransform_sub_eq_integral {w : ℂ} (hw : 0 < w.im) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) :
    IntervalIntegrable (fun r : ℝ ↦ resolventTransform (μ r.toNNReal) w *
        deriv (resolventTransform (μ r.toNNReal)) w) volume s t ∧
      resolventTransform (μ t.toNNReal) w - resolventTransform (μ s.toNNReal) w =
        ∫ r in s..t, resolventTransform (μ r.toNNReal) w *
          deriv (resolventTransform (μ r.toNNReal)) w := by
  have key (u : ℝ) := And.intro (hint w hw u.toNNReal) (heq w hw u.toNNReal)
  obtain ⟨hit, het⟩ := key t
  obtain ⟨his, hes⟩ := key s
  rw [Real.coe_toNNReal t ht] at hit het
  rw [Real.coe_toNNReal s hs] at his hes
  refine ⟨his.symm.trans hit, ?_⟩
  rw [het, hes, add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left hit his]

/-- Under the Burgers equation, `s ↦ m_s(w)` is `y⁻³`-Lipschitz at height at least `y`. -/
private lemma norm_resolventTransform_sub_le_time {y : ℝ} (hy : 0 < y) {w : ℂ} (hw : y ≤ w.im)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖resolventTransform (μ t.toNNReal) w - resolventTransform (μ s.toNNReal) w‖ ≤
      y⁻¹ ^ 3 * |t - s| := by
  rw [(resolventTransform_sub_eq_integral hint heq (hy.trans_le hw) hs ht).2]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun r _ ↦ ?_
  rw [norm_mul, pow_succ']
  exact mul_le_mul (norm_resolventTransform_le_inv hy hw)
    (norm_deriv_resolventTransform_le_inv hy hw) (norm_nonneg _) (by positivity)

/-- Under the Burgers equation, `s ↦ m_s'(w)` is `16 y⁻⁴`-Lipschitz at height at least `y`, by
the Cauchy estimate on the disc of radius `y / 2` about `w`. -/
private lemma norm_deriv_resolventTransform_sub_le_time {y : ℝ} (hy : 0 < y) {w : ℂ}
    (hw : y ≤ w.im) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖deriv (resolventTransform (μ t.toNNReal)) w - deriv (resolventTransform (μ s.toNNReal)) w‖ ≤
      16 * y⁻¹ ^ 4 * |t - s| := by
  have hy2 : 0 < y / 2 := by positivity
  have hball (p : ℂ) (hp : p ∈ closedBall w (y / 2)) : y / 2 ≤ p.im := by
    have := (abs_im_le_norm (p - w)).trans (mem_closedBall_iff_norm.1 hp)
    rw [sub_im] at this
    linarith [(abs_le.1 this).1]
  have hdiff (u : ℝ) :
      DifferentiableOn ℂ (resolventTransform (μ u.toNNReal)) (closedBall w (y / 2)) :=
    fun p hp ↦ (hasDerivAt_resolventTransform_of_im_ne_zero
      (hy2.trans_le (hball p hp)).ne').differentiableAt.differentiableWithinAt
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hy2
    (((hdiff t).sub (hdiff s)).diffContOnCl_ball subset_rfl) fun p hp ↦
      norm_resolventTransform_sub_le_time hint heq hy2 (hball p (sphere_subset_closedBall hp))
        hs ht
  rw [deriv_sub ((hdiff t).differentiableAt (closedBall_mem_nhds w hy2))
    ((hdiff s).differentiableAt (closedBall_mem_nhds w hy2))] at hcauchy
  refine hcauchy.trans_eq ?_
  field_simp
  ring

/-- Under the Burgers equation, the drift `s ↦ m_s(w) m_s'(w)` is `17 y⁻⁵`-Lipschitz at height at
least `y`. -/
private lemma norm_mul_deriv_resolventTransform_sub_le_time {y : ℝ} (hy : 0 < y) {w : ℂ}
    (hw : y ≤ w.im) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖resolventTransform (μ t.toNNReal) w * deriv (resolventTransform (μ t.toNNReal)) w -
      resolventTransform (μ s.toNNReal) w * deriv (resolventTransform (μ s.toNNReal)) w‖ ≤
      17 * y⁻¹ ^ 5 * |t - s| := by
  rw [show ∀ a b c d : ℂ, a * b - c * d = (a - c) * b + c * (b - d) from fun _ _ _ _ ↦ by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  calc _ ≤ y⁻¹ ^ 3 * |t - s| * y⁻¹ ^ 2 + y⁻¹ * (16 * y⁻¹ ^ 4 * |t - s|) := by
        gcongr
        · exact norm_resolventTransform_sub_le_time hint heq hy hw hs ht
        · exact norm_deriv_resolventTransform_le_inv hy hw
        · exact norm_resolventTransform_le_inv hy hw
        · exact norm_deriv_resolventTransform_sub_le_time hint heq hy hw hs ht
    _ = _ := by ring

/-- Under the Burgers equation, along a path `r ↦ z - r c` staying at height at least `y` for
`r ∈ [0, T]`, the temporal increment `r ↦ m_r(z - r c) - m_s(z - r c)` has derivative
`m_s(z - s c) m_s'(z - s c)` at `s`: its error is `O((r - s)²)` by the Lipschitz bounds on the
drift `m m'` in time and space. -/
private lemma hasDerivWithinAt_resolventTransform_sub_resolventTransform {y T : ℝ} (hy : 0 < y)
    {z c : ℂ} (him : ∀ s ∈ Icc 0 T, y ≤ (z - s * c).im) {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasDerivWithinAt (fun r : ℝ ↦ resolventTransform (μ r.toNNReal) (z - r * c) -
        resolventTransform (μ s.toNNReal) (z - r * c))
      (resolventTransform (μ s.toNNReal) (z - s * c) *
        deriv (resolventTransform (μ s.toNNReal)) (z - s * c)) (Icc 0 T) s := by
  set p : ℝ → ℂ := fun r ↦ z - r * c with hp_def
  set F : ℝ → ℂ → ℂ := fun r w ↦
    resolventTransform (μ r.toNNReal) w * deriv (resolventTransform (μ r.toNNReal)) w
  set K := 3 * y⁻¹ ^ 4 * ‖c‖ + 17 * y⁻¹ ^ 5
  have hbound (r : ℝ) (hr : r ∈ Icc 0 T) :
      ‖resolventTransform (μ r.toNNReal) (p r) - resolventTransform (μ s.toNNReal) (p r) -
        (resolventTransform (μ s.toNNReal) (p s) - resolventTransform (μ s.toNNReal) (p s)) -
        (r - s) • F s (p s)‖ ≤ K * ‖‖r - s‖ ^ 2‖ := by
    obtain ⟨hi, he⟩ := resolventTransform_sub_eq_integral hint heq
      (hy.trans_le (him r hr)) hs.1 hr.1
    rw [sub_self, sub_zero, he, ← intervalIntegral.integral_const,
      ← intervalIntegral.integral_sub hi intervalIntegrable_const, norm_pow, norm_norm,
      Real.norm_eq_abs, sq, ← mul_assoc]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu ↦ ?_
    have hu' : u ∈ uIcc s r := uIoc_subset_uIcc hu
    have huT : u ∈ Icc 0 T := uIcc_subset_Icc hs hr hu'
    have hus : |u - s| ≤ |r - s| := abs_sub_left_of_mem_uIcc hu'
    have hpr : ‖p r - p s‖ = |r - s| * ‖c‖ := by
      simp only [hp_def, sub_sub_sub_cancel_left, ← sub_mul, norm_mul, ← ofReal_sub, norm_real,
        Real.norm_eq_abs, abs_sub_comm]
    rw [show F u (p r) - F s (p s) = (F u (p r) - F u (p s)) + (F u (p s) - F s (p s)) by ring]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ 3 * y⁻¹ ^ 4 * ‖p r - p s‖ + 17 * y⁻¹ ^ 5 * |u - s| := by
          gcongr
          · exact norm_mul_deriv_resolventTransform_sub_le hy (him r hr) (him s hs)
          · exact norm_mul_deriv_resolventTransform_sub_le_time hint heq hy (him s hs) hs.1 huT.1
      _ ≤ 3 * y⁻¹ ^ 4 * (|r - s| * ‖c‖) + 17 * y⁻¹ ^ 5 * |r - s| := by
          rw [hpr]
          gcongr
      _ = K * |r - s| := by ring
  rw [hasDerivWithinAt_iff_isLittleO]
  exact (IsBigO.of_bound K (eventually_nhdsWithin_of_forall hbound)).trans_isLittleO
    ((isLittleO_pow_sub_sub s one_lt_two).mono nhdsWithin_le_nhds)

/-- Under the Burgers equation, along a path `s ↦ z - s c` staying at height at least `y` for
`s ∈ [0, T]`, the transform `φ(s) = m_s(z - s c)` satisfies `φ' = m_s'(z - s c) (φ - c)`. -/
private lemma hasDerivWithinAt_resolventTransform_sub_mul {y T : ℝ} (hy : 0 < y) {z c : ℂ}
    (him : ∀ s ∈ Icc 0 T, y ≤ (z - s * c).im) {s : ℝ} (hs : s ∈ Icc 0 T) :
    HasDerivWithinAt (fun r : ℝ ↦ resolventTransform (μ r.toNNReal) (z - r * c))
      (deriv (resolventTransform (μ s.toNNReal)) (z - s * c) *
        (resolventTransform (μ s.toNNReal) (z - s * c) - c)) (Icc 0 T) s := by
  have hp : HasDerivAt (fun r : ℝ ↦ z - r * c) (-c) s := by
    simpa using (((hasDerivAt_id s).ofReal_comp).mul_const c).const_sub z
  -- The spatial part `r ↦ m_s(z - r c)`, by the chain rule.
  have hA : HasDerivAt (fun r : ℝ ↦ resolventTransform (μ s.toNNReal) (z - r * c))
      (deriv (resolventTransform (μ s.toNNReal)) (z - s * c) * -c) s :=
    ((hasDerivAt_resolventTransform_of_im_ne_zero
      (hy.trans_le (him s hs)).ne').differentiableAt.hasDerivAt).comp s hp
  convert hA.hasDerivWithinAt.add
    (hasDerivWithinAt_resolventTransform_sub_resolventTransform hint heq hy him hs) using 1
  · funext r
    simp only [Pi.add_apply]
    ring
  · ring

/-- **Characteristics for the Burgers equation of resolvent transforms.** Let `μ` be a family of
probability measures whose resolvent transforms satisfy
`m_t(z) = m_0(z) + ∫₀ᵗ m_s(z) m_s'(z) ds` on the upper half-plane. Then `m_t` is constant along
the characteristic `s ↦ z - s m_0(z)`: `m_t(z - t m_0(z)) = m_0(z)` whenever `0 < Im z` and
`2t < (Im z)²`. -/
theorem resolventTransform_sub_mul_resolventTransform_of_burgers (t : ℝ≥0) {z : ℂ}
    (hz : 0 < z.im) (htz : 2 * (t : ℝ) < z.im ^ 2) :
    resolventTransform (μ t) (z - (t : ℝ) * resolventTransform (μ 0) z) =
      resolventTransform (μ 0) z := by
  set c := resolventTransform (μ 0) z
  set T : ℝ := (t : ℝ)
  have hy : 0 < z.im / 2 := by positivity
  have him (s : ℝ) (hs : s ∈ Icc 0 T) : z.im / 2 ≤ (z - s * c).im :=
    half_im_le_im_sub_mul_resolventTransform hz hs.1 (by linarith [hs.2])
  have hderiv (s : ℝ) (hs : s ∈ Icc 0 T) :=
    (hasDerivWithinAt_resolventTransform_sub_mul hint heq hy him hs).sub_const c
  -- Grönwall's inequality for `ψ(s) = m_s(z - s c) - c`, which vanishes at `s = 0`.
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0) (ε := 0)
    (K := (z.im / 2)⁻¹ ^ 2) (fun s hs ↦ (hderiv s hs).continuousWithinAt)
    (fun s hs ↦ (hderiv s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs))
    (by simp [c]) (fun s hs ↦ by
      rw [add_zero, norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_deriv_resolventTransform_le_inv hy
        (him s (Ico_subset_Icc_self hs))) (norm_nonneg _)) T ⟨t.2, le_rfl⟩
  rw [gronwallBound_ε0_δ0, norm_le_zero_iff, sub_eq_zero, Real.toNNReal_coe] at hgron
  exact hgron

/-- **Uniqueness for the Burgers equation of resolvent transforms.** Two families of probability
measures on `ℝ` whose resolvent transforms satisfy `m_t(z) = m_0(z) + ∫₀ᵗ m_s(z) m_s'(z) ds` on the
upper half-plane, with interval integrable integrands, and which agree at time `0`, agree at
every time. -/
theorem eq_of_resolventTransform_burgers {ν : ℝ≥0 → Measure ℝ} [∀ t, IsProbabilityMeasure (ν t)]
    (hintν : ∀ z : ℂ, 0 < z.im → ∀ t : ℝ≥0, IntervalIntegrable (fun s : ℝ ↦
      resolventTransform (ν s.toNNReal) z * deriv (resolventTransform (ν s.toNNReal)) z)
      volume 0 t)
    (heqν : ∀ z : ℂ, 0 < z.im → ∀ t : ℝ≥0, resolventTransform (ν t) z =
      resolventTransform (ν 0) z + ∫ s in (0 : ℝ)..t,
        resolventTransform (ν s.toNNReal) z * deriv (resolventTransform (ν s.toNNReal)) z)
    (h0 : μ 0 = ν 0) : μ = ν := by
  funext t
  set T : ℝ := (t : ℝ)
  set m₀ : ℂ → ℂ := resolventTransform (μ 0)
  obtain ⟨z₁, hz₁, hz₁T, hΦU, hΦ⟩ :=
    exists_map_nhds_sub_mul_resolventTransform (ρ := μ 0) (show 0 ≤ T from t.2)
  -- Near `Φ(z₁)`, both transforms at time `t` agree, since both are `m₀ ∘ Φ⁻¹` there.
  have hV : ∀ᶠ z in 𝓝 z₁, 0 < z.im ∧ 2 * T < z.im ^ 2 :=
    (continuousAt_const.eventually_lt continuous_im.continuousAt hz₁).and
      (continuousAt_const.eventually_lt (continuous_im.pow 2).continuousAt hz₁T)
  have hagree : ∀ᶠ w in 𝓝 (z₁ - T * m₀ z₁),
      resolventTransform (μ t) w = resolventTransform (ν t) w := by
    rw [← hΦ, eventually_map]
    filter_upwards [hV] with z ⟨hz, hzT⟩
    rw [resolventTransform_sub_mul_resolventTransform_of_burgers hint heq t hz hzT]
    simp only [h0]
    rw [resolventTransform_sub_mul_resolventTransform_of_burgers hintν heqν t hz hzT]
  -- Analytic continuation over the upper half-plane, then Stieltjes inversion.
  have han (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
      AnalyticOnNhd ℂ (resolventTransform ρ) {w : ℂ | 0 < w.im} :=
    analyticOnNhd_resolventTransform.mono fun _ hw ↦ ne_of_gt hw
  have heqOn := (han (μ t)).eqOn_of_preconnected_of_eventuallyEq (han (ν t))
    (convex_halfSpace_im_gt 0).isPreconnected hΦU hagree
  exact Measure.ext_of_resolventTransform fun w hw ↦ heqOn hw

end Burgers

end TauCeti
