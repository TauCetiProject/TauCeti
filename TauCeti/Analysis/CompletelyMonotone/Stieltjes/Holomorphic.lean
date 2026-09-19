/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import TauCeti.Analysis.CompletelyMonotone.Stieltjes.CompleteBernstein
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected

/-!
# The holomorphic extension of a Stieltjes function

A Stieltjes representation

`f(t) = a / t + b + ∫ x, (t + x)⁻¹ ∂μ`

makes sense for every complex `z` off the closed negative half-axis: on the slit plane
`ℂ ∖ (-∞, 0]` the kernel `(z + x)⁻¹` is dominated by a multiple of the Stieltjes weight
`(1 + x)⁻¹`, locally uniformly in `z`.  The resulting complex Stieltjes transform
`TauCeti.stieltjesExtension μ a b` is holomorphic on the slit plane, restricts to `f` on
`(0, ∞)`, is symmetric under complex conjugation, and has imaginary part

`Im F(z) = -Im z * (a / |z|² + ∫ x, |z + x|⁻² ∂μ)`,

so that `Im z * Im F(z) ≤ 0`: a Stieltjes function extends to a holomorphic function mapping the
upper half-plane into the closed lower half-plane.  Multiplying by `z`, a complete Bernstein
function extends holomorphically to the slit plane with `0 ≤ Im z * Im G(z)`, i.e. to a Pick
function.  These are the forward halves of the analytic characterizations of Stieltjes and
complete Bernstein functions.  By the identity theorem, the extension is the only holomorphic
function on the slit plane that agrees with `f` on `(0, ∞)`.

## Main declarations

* `TauCeti.stieltjesExtension`: the complex Stieltjes transform of representing data.
* `TauCeti.integrable_inv_add_of_mem_slitPlane`: the complex Stieltjes kernel is integrable at
  every point of the slit plane.
* `TauCeti.hasDerivAt_stieltjesExtension` and `TauCeti.analyticOnNhd_stieltjesExtension`: the
  transform is holomorphic on the slit plane, with derivative `-a / z² - ∫ x, (z + x)⁻² ∂μ`.
* `TauCeti.stieltjesExtension_conj`: the transform commutes with complex conjugation.
* `TauCeti.im_stieltjesExtension` and `TauCeti.im_mul_im_stieltjesExtension_nonpos`: the
  imaginary part and its sign; `TauCeti.im_mul_stieltjesExtension` and
  `TauCeti.im_mul_im_mul_stieltjesExtension_nonneg` do the same for `z ↦ z F(z)`.
* `TauCeti.RepresentsStieltjes.stieltjesExtension_ofReal` and
  `TauCeti.RepresentsStieltjes.eqOn_stieltjesExtension`: the transform extends the represented
  function, and is its only holomorphic extension to the slit plane.
* `TauCeti.IsStieltjesFunction.exists_analyticOnNhd_slitPlane`: a Stieltjes function extends
  holomorphically to the slit plane with `Im z * Im F(z) ≤ 0`.
* `TauCeti.IsCompleteBernsteinFunction.exists_analyticOnNhd_slitPlane`: a complete Bernstein
  function extends holomorphically to the slit plane with `0 ≤ Im z * Im G(z)`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  de Gruyter, 2nd ed. (2012), Theorem 6.2 and Chapter 7.
-/

public section

noncomputable section

open MeasureTheory Set Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace TauCeti

/-- On a small ball around a point of the slit plane, the distance from `w` to the point `-x`
of the closed negative half-axis is bounded below by a fixed multiple of `1 + x`.  This is the
locally uniform comparison of the complex Stieltjes kernel with the Stieltjes weight. -/
theorem exists_pos_forall_mem_ball_mul_one_add_le_norm_add {z : ℂ} (hz : z ∈ slitPlane) :
    ∃ c > 0, ∀ w ∈ Metric.ball z c, ∀ x : ℝ≥0, c * (1 + (x : ℝ)) ≤ ‖w + ((x : ℝ) : ℂ)‖ := by
  -- First a bound at `z` itself, then halve the constant to absorb the displacement `w - z`.
  obtain ⟨c, hc, hzc⟩ : ∃ c > 0, ∀ x : ℝ, 0 ≤ x → c * (1 + x) ≤ ‖z + (x : ℂ)‖ := by
    have hre (x : ℝ) : z.re + x ≤ ‖z + (x : ℂ)‖ := by
      simpa using Complex.re_le_norm (z + (x : ℂ))
    rcases mem_slitPlane_iff.mp hz with hpos | him
    · refine ⟨min z.re 1, lt_min hpos one_pos, fun x hx => (hre x).trans' ?_⟩
      nlinarith [min_le_left z.re 1, min_le_right z.re 1,
        mul_nonneg (sub_nonneg.2 (min_le_right z.re 1)) hx]
    · have hy : 0 < |z.im| := abs_pos.mpr him
      have hu : 0 ≤ |z.re| := abs_nonneg _
      refine ⟨min (|z.im| / (2 * |z.re| + 2)) (1 / 4), lt_min (by positivity) (by norm_num),
        fun x hx => ?_⟩
      rcases le_or_gt x (2 * |z.re| + 1) with hxu | hxu
      · have him_le : |z.im| ≤ ‖z + (x : ℂ)‖ := by
          simpa using Complex.abs_im_le_norm (z + (x : ℂ))
        calc min (|z.im| / (2 * |z.re| + 2)) (1 / 4) * (1 + x)
            ≤ |z.im| / (2 * |z.re| + 2) * (2 * |z.re| + 2) :=
              mul_le_mul (min_le_left _ _) (by linarith) (by linarith) (by positivity)
          _ = |z.im| := div_mul_cancel₀ _ (by positivity)
          _ ≤ ‖z + (x : ℂ)‖ := him_le
      · refine (hre x).trans' ?_
        nlinarith [min_le_right (|z.im| / (2 * |z.re| + 2)) (1 / 4), neg_abs_le z.re,
          lt_min_iff.mp (lt_min (by positivity : (0 : ℝ) < |z.im| / (2 * |z.re| + 2))
            (by norm_num : (0 : ℝ) < 1 / 4))]
  refine ⟨c / 2, half_pos hc, fun w hw x => ?_⟩
  have hwz : ‖z - w‖ < c / 2 := by rw [← dist_eq_norm, dist_comm]; exact hw
  have htri : ‖z + ((x : ℝ) : ℂ)‖ ≤ ‖w + ((x : ℝ) : ℂ)‖ + ‖z - w‖ := by
    rw [show z + ((x : ℝ) : ℂ) = (w + ((x : ℝ) : ℂ)) + (z - w) by ring]
    exact norm_add_le _ _
  nlinarith [hzc x x.coe_nonneg, x.coe_nonneg]

variable {μ : Measure ℝ≥0} {a b : ℝ≥0} {f : ℝ → ℝ} {z : ℂ}

/-- The complex Stieltjes kernel `(z + x)⁻¹` is integrable against a measure carrying an
integrable Stieltjes weight, at every point `z` of the slit plane. -/
theorem integrable_inv_add_of_mem_slitPlane (hμ : Integrable stieltjesWeight μ)
    (hz : z ∈ slitPlane) : Integrable (fun x : ℝ≥0 => (z + ((x : ℝ) : ℂ))⁻¹) μ := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz
  refine (hμ.const_mul c⁻¹).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  have h1x : 0 < 1 + (x : ℝ) := by positivity
  rw [norm_inv, stieltjesWeight_apply, ← mul_inv]
  exact inv_anti₀ (by positivity) (hbound z (Metric.mem_ball_self hc) x)

/-- The complex Stieltjes integral is complex differentiable on the slit plane, with derivative
`-∫ x, (z + x)⁻² ∂μ`. -/
theorem hasDerivAt_integral_inv_add (hμ : Integrable stieltjesWeight μ) (hz : z ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => ∫ x, (w + ((x : ℝ) : ℂ))⁻¹ ∂μ)
      (-∫ x, ((z + ((x : ℝ) : ℂ)) ^ 2)⁻¹ ∂μ) z := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz
  have hne (w : ℂ) (hw : w ∈ Metric.ball z c) (x : ℝ≥0) : w + ((x : ℝ) : ℂ) ≠ 0 := by
    rw [← norm_pos_iff]
    exact lt_of_lt_of_le (by positivity) (hbound w hw x)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (x : ℝ≥0) => (w + ((x : ℝ) : ℂ))⁻¹)
    (F' := fun (w : ℂ) (x : ℝ≥0) => -((w + ((x : ℝ) : ℂ)) ^ 2)⁻¹)
    (bound := fun x => (c ^ 2)⁻¹ * stieltjesWeight x) (μ := μ)
    (Metric.ball_mem_nhds z hc) (Eventually.of_forall fun _ => by fun_prop)
    (integrable_inv_add_of_mem_slitPlane hμ hz) (by fun_prop)
    (ae_of_all _ fun x w hw => ?_) (hμ.const_mul _)
    (ae_of_all _ fun x w hw => ?_)
  · simpa only [integral_neg] using key.2
  · have h1x : 1 ≤ 1 + (x : ℝ) := by simp
    have hle := hbound w hw x
    rw [norm_neg, norm_inv, norm_pow, stieltjesWeight_apply, ← mul_inv]
    refine inv_anti₀ (by positivity) ?_
    calc c ^ 2 * (1 + (x : ℝ)) ≤ (c * (1 + (x : ℝ))) ^ 2 := by nlinarith [sq_nonneg c]
      _ ≤ ‖w + ((x : ℝ) : ℂ)‖ ^ 2 := by gcongr
  · exact (((hasDerivAt_id w).add_const ((x : ℝ) : ℂ)).inv (hne w hw x)).congr_deriv
      (by simp [div_eq_mul_inv])

/-- The **complex Stieltjes transform** of representing data `μ, a, b`:
`z ↦ a / z + b + ∫ x, (z + x)⁻¹ ∂μ`.  It is meaningful on the slit plane `ℂ ∖ (-∞, 0]`, where it
is the holomorphic extension of the Stieltjes function represented by `μ, a, b`. -/
def stieltjesExtension (μ : Measure ℝ≥0) (a b : ℝ≥0) (z : ℂ) : ℂ :=
  ((a : ℝ) : ℂ) / z + ((b : ℝ) : ℂ) + ∫ x, (z + ((x : ℝ) : ℂ))⁻¹ ∂μ

/-- The defining formula of the complex Stieltjes transform. -/
theorem stieltjesExtension_apply (μ : Measure ℝ≥0) (a b : ℝ≥0) (z : ℂ) :
    stieltjesExtension μ a b z =
      ((a : ℝ) : ℂ) / z + ((b : ℝ) : ℂ) + ∫ x, (z + ((x : ℝ) : ℂ))⁻¹ ∂μ :=
  (rfl)

/-- The complex Stieltjes transform is complex differentiable at every point of the slit plane,
with derivative `-a / z² - ∫ x, (z + x)⁻² ∂μ`. -/
theorem hasDerivAt_stieltjesExtension (hμ : Integrable stieltjesWeight μ) (hz : z ∈ slitPlane) :
    HasDerivAt (stieltjesExtension μ a b)
      (-((a : ℝ) : ℂ) / z ^ 2 - ∫ x, ((z + ((x : ℝ) : ℂ)) ^ 2)⁻¹ ∂μ) z := by
  have hdiv : HasDerivAt (fun w : ℂ => ((a : ℝ) : ℂ) / w) (-((a : ℝ) : ℂ) / z ^ 2) z := by
    simpa [div_eq_mul_inv, neg_mul] using
      (hasDerivAt_inv (slitPlane_ne_zero hz)).const_mul ((a : ℝ) : ℂ)
  rw [show stieltjesExtension μ a b = _ from funext (stieltjesExtension_apply μ a b),
    sub_eq_add_neg]
  exact (hdiv.add_const ((b : ℝ) : ℂ)).add (hasDerivAt_integral_inv_add hμ hz)

/-- The complex Stieltjes transform is complex differentiable on the slit plane. -/
theorem differentiableOn_stieltjesExtension (hμ : Integrable stieltjesWeight μ) :
    DifferentiableOn ℂ (stieltjesExtension μ a b) slitPlane := fun _ hz =>
  (hasDerivAt_stieltjesExtension hμ hz).differentiableAt.differentiableWithinAt

/-- The complex Stieltjes transform is holomorphic on the slit plane. -/
theorem analyticOnNhd_stieltjesExtension (hμ : Integrable stieltjesWeight μ) :
    AnalyticOnNhd ℂ (stieltjesExtension μ a b) slitPlane :=
  (differentiableOn_stieltjesExtension hμ).analyticOnNhd isOpen_slitPlane

/-- The complex Stieltjes transform commutes with complex conjugation. -/
theorem stieltjesExtension_conj (μ : Measure ℝ≥0) (a b : ℝ≥0) (z : ℂ) :
    stieltjesExtension μ a b (conj z) = conj (stieltjesExtension μ a b z) := by
  simp only [stieltjesExtension_apply, map_add, map_div₀, conj_ofReal, ← integral_conj,
    map_inv₀]

/-- **The imaginary part of the complex Stieltjes transform**:
`Im F(z) = -Im z * (a / |z|² + ∫ x, |z + x|⁻² ∂μ)` on the slit plane. -/
theorem im_stieltjesExtension (hμ : Integrable stieltjesWeight μ) (hz : z ∈ slitPlane) :
    (stieltjesExtension μ a b z).im =
      -z.im * ((a : ℝ) / normSq z + ∫ x, (normSq (z + ((x : ℝ) : ℂ)))⁻¹ ∂μ) := by
  have hint : (∫ x, (z + ((x : ℝ) : ℂ))⁻¹ ∂μ).im =
      -z.im * ∫ x, (normSq (z + ((x : ℝ) : ℂ)))⁻¹ ∂μ := by
    rw [← integral_const_mul, ← RCLike.im_to_complex,
      ← integral_im (integrable_inv_add_of_mem_slitPlane hμ hz)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [div_eq_mul_inv, neg_mul]
  rw [stieltjesExtension_apply, add_im, add_im, hint, div_eq_mul_inv, im_ofReal_mul, inv_im,
    ofReal_im]
  ring

/-- **A Stieltjes transform maps the upper half-plane into the closed lower half-plane**, and the
lower half-plane into the closed upper one: `Im z * Im F(z) ≤ 0` on the slit plane. -/
theorem im_mul_im_stieltjesExtension_nonpos (hμ : Integrable stieltjesWeight μ)
    (hz : z ∈ slitPlane) : z.im * (stieltjesExtension μ a b z).im ≤ 0 := by
  have hP : 0 ≤ (a : ℝ) / normSq z + ∫ x, (normSq (z + ((x : ℝ) : ℂ)))⁻¹ ∂μ :=
    add_nonneg (div_nonneg a.coe_nonneg (normSq_nonneg z))
      (integral_nonneg fun x => inv_nonneg.mpr (normSq_nonneg _))
  rw [im_stieltjesExtension hμ hz]
  nlinarith [mul_nonneg (sq_nonneg z.im) hP]

/-- The imaginary part of `z` times the complex Stieltjes transform:
`Im (z F(z)) = Im z * (b + ∫ x, x / |z + x|² ∂μ)` on the slit plane. -/
theorem im_mul_stieltjesExtension (hμ : Integrable stieltjesWeight μ) (hz : z ∈ slitPlane) :
    (z * stieltjesExtension μ a b z).im =
      z.im * ((b : ℝ) + ∫ x, (x : ℝ) / normSq (z + ((x : ℝ) : ℂ)) ∂μ) := by
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨c, hc, hbound⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz
  have hint : (z * ∫ x, (z + ((x : ℝ) : ℂ))⁻¹ ∂μ).im =
      z.im * ∫ x, (x : ℝ) / normSq (z + ((x : ℝ) : ℂ)) ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul, ← RCLike.im_to_complex,
      ← integral_im ((integrable_inv_add_of_mem_slitPlane hμ hz).const_mul z)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hne : z + ((x : ℝ) : ℂ) ≠ 0 := by
      rw [← norm_pos_iff]
      exact lt_of_lt_of_le (by positivity) (hbound z (Metric.mem_ball_self hc) x)
    have hsplit : z * (z + ((x : ℝ) : ℂ))⁻¹ = 1 - ((x : ℝ) : ℂ) * (z + ((x : ℝ) : ℂ))⁻¹ := by
      field_simp
      ring
    simp only [RCLike.im_to_complex, hsplit, sub_im, one_im, im_ofReal_mul, inv_im, add_im,
      ofReal_im, add_zero]
    ring
  rw [stieltjesExtension_apply, mul_add, mul_add, mul_div_cancel₀ _ hz0, add_im, add_im, hint,
    ofReal_im, mul_comm z, im_ofReal_mul]
  ring

/-- `Im z * Im (z F(z)) ≥ 0` on the slit plane: `z ↦ z F(z)` maps the upper half-plane into the
closed upper half-plane. -/
theorem im_mul_im_mul_stieltjesExtension_nonneg (hμ : Integrable stieltjesWeight μ)
    (hz : z ∈ slitPlane) : 0 ≤ z.im * (z * stieltjesExtension μ a b z).im := by
  have hP : 0 ≤ (b : ℝ) + ∫ x, (x : ℝ) / normSq (z + ((x : ℝ) : ℂ)) ∂μ :=
    add_nonneg b.coe_nonneg
      (integral_nonneg fun x => div_nonneg x.coe_nonneg (normSq_nonneg _))
  rw [im_mul_stieltjesExtension hμ hz, ← mul_assoc]
  exact mul_nonneg (mul_self_nonneg _) hP

namespace RepresentsStieltjes

/-- The complex Stieltjes transform of a Stieltjes representation of `f` extends `f`: it agrees
with `f` on `(0, ∞)`. -/
theorem stieltjesExtension_ofReal (h : RepresentsStieltjes μ a b f) {t : ℝ} (ht : 0 < t) :
    stieltjesExtension μ a b t = f t := by
  rw [h.eq_div_add_add_integral_inv_add ht, stieltjesExtension_apply]
  push_cast [← integral_complex_ofReal]
  congr 1

/-- **Uniqueness of the holomorphic extension.**  A function holomorphic on the slit plane that
agrees on `(0, ∞)` with a represented Stieltjes function is its complex Stieltjes transform. -/
theorem eqOn_stieltjesExtension (h : RepresentsStieltjes μ a b f) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F slitPlane) (hFf : ∀ t : ℝ, 0 < t → F t = f t) :
    EqOn F (stieltjesExtension μ a b) slitPlane := by
  have hpre : IsPreconnected slitPlane :=
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
  refine hF.eqOn_of_preconnected_of_frequently_eq
    (analyticOnNhd_stieltjesExtension h.integrable_weight) hpre one_mem_slitPlane ?_
  -- The two functions agree at the real points `1 + 1 / (n + 1)`, which tend to `1`.
  have htend : Tendsto (fun n : ℕ => (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
      (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
      simpa [Function.comp_def] using (continuous_ofReal.tendsto 1).comp h1
    · simp only [mem_compl_iff, mem_singleton_iff, ← ofReal_one, ofReal_inj]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  exact htend.frequently (Frequently.of_forall fun n => by
    rw [hFf _ (by positivity), h.stieltjesExtension_ofReal (by positivity)])

end RepresentsStieltjes

/-- **A Stieltjes function extends holomorphically to the slit plane** `ℂ ∖ (-∞, 0]`, and the
extension satisfies `Im z * Im F(z) ≤ 0`: it maps the upper half-plane into the closed lower
half-plane. -/
theorem IsStieltjesFunction.exists_analyticOnNhd_slitPlane (hf : IsStieltjesFunction f) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F slitPlane ∧ (∀ t : ℝ, 0 < t → F t = f t) ∧
      ∀ z ∈ slitPlane, z.im * (F z).im ≤ 0 := by
  obtain ⟨a, b, μ, h⟩ := isStieltjesFunction_iff.mp hf
  exact ⟨stieltjesExtension μ a b, analyticOnNhd_stieltjesExtension h.integrable_weight,
    fun t ht => h.stieltjesExtension_ofReal ht,
    fun z hz => im_mul_im_stieltjesExtension_nonpos h.integrable_weight hz⟩

/-- On `(0, ∞)` a complete Bernstein function is `t` times the complex Stieltjes transform of its
representing data. -/
theorem RepresentsCompleteBernstein.ofReal_mul_stieltjesExtension
    (h : RepresentsCompleteBernstein μ a b f) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) * stieltjesExtension μ a b t = f t := by
  rw [h.representsStieltjes_div.stieltjesExtension_ofReal ht, ← ofReal_mul,
    mul_div_cancel₀ _ ht.ne']

/-- **A complete Bernstein function extends holomorphically to the slit plane** `ℂ ∖ (-∞, 0]`,
and the extension satisfies `0 ≤ Im z * Im G(z)`: it maps the upper half-plane into the closed
upper half-plane. -/
theorem IsCompleteBernsteinFunction.exists_analyticOnNhd_slitPlane
    (hf : IsCompleteBernsteinFunction f) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G slitPlane ∧ (∀ t : ℝ, 0 < t → G t = f t) ∧
      ∀ z ∈ slitPlane, 0 ≤ z.im * (G z).im := by
  obtain ⟨a, b, μ, h⟩ := isCompleteBernsteinFunction_iff.mp hf
  exact ⟨fun z => z * stieltjesExtension μ a b z,
    analyticOnNhd_id.mul (analyticOnNhd_stieltjesExtension h.integrable_weight),
    fun t ht => h.ofReal_mul_stieltjesExtension ht,
    fun z hz => im_mul_im_mul_stieltjesExtension_nonneg h.integrable_weight hz⟩

end TauCeti

end
