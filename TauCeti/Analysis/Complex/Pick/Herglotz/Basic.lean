/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Nevanlinna
import TauCeti.Basic.Complex.Basic
import TauCeti.Basic.Complex.OfRealSub

/-!
# The Herglotz representation on the upper half-plane in resolvent convention

A Pick function `F`, holomorphic on the upper half-plane with `0 ≤ Im F`, has the Nevanlinna
representation `F z = Re F(i) + b z + ∫ (1 + t z) / (t - z) dρ(t)` with `b ≥ 0` and `ρ` a
finite measure (`TauCeti.exists_isFiniteMeasure_eq_nevanlinnaKernel_add`).  Spectral theory uses
instead the subtracted resolvent kernel

`(t - z)⁻¹ - t / (1 + t ^ 2)`,

whose leading term is the resolvent `(A - z)⁻¹` evaluated on the spectrum.  Since
`(1 + t z) / (t - z) = (1 + t ^ 2) ((t - z)⁻¹ - t / (1 + t ^ 2))`, the two representations differ
by the density change `dν = (1 + t ^ 2) dρ`.  The measure `ν` is in general infinite, but its
weighted mass `∫ (1 + t ^ 2)⁻¹ dν` is the total mass of `ρ`.

This file proves the density conversion, the existence of the representation
`F z = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` with `a = Re F(i)`, `b ≥ 0` and
`∫ (1 + t ^ 2)⁻¹ dν < ∞`, and the uniqueness of the triple `(a, b, ν)`.  The constant `a` is read
off at `z = i` and `b` is the limit of `Im F(i y) / y` as `y → ∞`.  For the measure, the
Nevanlinna integral of a finite measure `ρ` is `ρ(ℝ) z + (1 + z ^ 2) m_ρ(z)` for `Im z ≠ 0`,
where `m_ρ` is the resolvent transform, so Stieltjes inversion determines `ρ`
(`MeasureTheory.Measure.ext_of_integral_nevanlinnaKernel`, in
`TauCeti.Analysis.Complex.Pick.Nevanlinna`), and `ν` is recovered from
`ρ = (1 + t ^ 2)⁻¹ ν`.

## Main declarations

* `TauCeti.subtractedResolventKernel`: the kernel `(t - z)⁻¹ - t / (1 + t ^ 2)`.
* `TauCeti.norm_subtractedResolventKernel_le`: on the upper half-plane the kernel is bounded by a
  multiple of `(1 + t ^ 2)⁻¹`.
* `MeasureTheory.Measure.integral_subtractedResolventKernel_withDensity`: under the density change
  `dν = (1 + t ^ 2) dρ` the subtracted resolvent kernel integrates to the Nevanlinna kernel.
* `MeasureTheory.Measure.lintegral_inv_one_add_sq_withDensity`: the weighted-mass identity
  `∫ (1 + t ^ 2)⁻¹ dν = ρ(ℝ)`.
* `TauCeti.lintegral_inv_one_add_sq_lt_top`: every finite measure has finite weighted mass.
* `TauCeti.integrable_subtractedResolventKernel_iff`,
  `TauCeti.integrable_im_subtractedResolventKernel_iff`: at a nonreal point the kernel, or its
  imaginary part, is `ν`-integrable exactly when `ν` has finite weighted mass.
* `TauCeti.exists_eq_subtractedResolventKernel_add`: the Herglotz representation of a Pick function.
* `TauCeti.re_eq_of_eq_subtractedResolventKernel_add`,
  `TauCeti.tendsto_im_div_of_eq_subtractedResolventKernel_add`: the constant term is `Re F(i)`, and
  the linear coefficient is the limit of `Im F(i y) / y`.
* `TauCeti.eq_and_eq_of_eq_subtractedResolventKernel_add`: uniqueness of the constants.
* `MeasureTheory.Measure.integral_subtractedResolventKernel_eq_integral_nevanlinnaKernel`: the
  density conversion read from an arbitrary measure `ν`.
* `TauCeti.eq_of_eq_subtractedResolventKernel_add`: uniqueness of the measure.
* `TauCeti.existsUnique_eq_subtractedResolventKernel_add`: the Herglotz representation of a Pick
  function, with a unique triple `(a, b, ν)`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, §3.4, Theorem 3.20.
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  2nd ed., Chapter 6.
-/

public section

noncomputable section

open Complex ComplexConjugate MeasureTheory Filter Topology

namespace TauCeti

/-- The subtracted resolvent kernel `(t - z)⁻¹ - t / (1 + t ^ 2)` of the Herglotz representation
on the upper half-plane.  The subtracted term makes it integrable against measures `ν` with
`∫ (1 + t ^ 2)⁻¹ dν < ∞`, while its leading term follows the resolvent convention `(A - z)⁻¹`. -/
def subtractedResolventKernel (z : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) - z)⁻¹ - t / (1 + t ^ 2)

/-- The subtracted resolvent kernel is `(t - z)⁻¹ - t / (1 + t ^ 2)`. -/
theorem subtractedResolventKernel_def (z : ℂ) (t : ℝ) :
    subtractedResolventKernel z t = ((t : ℂ) - z)⁻¹ - t / (1 + t ^ 2) := by
  rw [subtractedResolventKernel]

/-- The subtracted resolvent kernel is measurable in its real variable. -/
@[fun_prop]
theorem measurable_subtractedResolventKernel (z : ℂ) :
    Measurable (subtractedResolventKernel z) := by
  unfold subtractedResolventKernel
  fun_prop

/-- Away from its pole, the Nevanlinna kernel is `1 + t ^ 2` times the subtracted resolvent
kernel. -/
theorem nevanlinnaKernel_eq_one_add_sq_mul_subtractedResolventKernel {z : ℂ} {t : ℝ}
    (h : (t : ℂ) - z ≠ 0) :
    nevanlinnaKernel z t = (1 + (t : ℂ) ^ 2) * subtractedResolventKernel z t := by
  rw [nevanlinnaKernel_def, subtractedResolventKernel_def]
  field_simp [one_add_ofReal_sq_ne_zero t]
  ring

/-- At a point of the upper half-plane, the subtracted resolvent kernel is bounded by a multiple of
`(1 + t ^ 2)⁻¹`, with the constant of `TauCeti.norm_nevanlinnaKernel_le`. -/
theorem norm_subtractedResolventKernel_le {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ‖subtractedResolventKernel z t‖ ≤
      (‖z + I‖ + ‖z - I‖) / (‖z + I‖ - ‖z - I‖) * (1 + t ^ 2)⁻¹ := by
  have h := nevanlinnaKernel_eq_one_add_sq_mul_subtractedResolventKernel
    (ofReal_sub_ne_zero_of_im_ne_zero hz.ne' t)
  have hcast : 1 + (t : ℂ) ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖nevanlinnaKernel z t‖ = (1 + t ^ 2) * ‖subtractedResolventKernel z t‖ := by
    rw [h, hcast, norm_mul, norm_real, Real.norm_of_nonneg (by positivity)]
  calc ‖subtractedResolventKernel z t‖ = ‖nevanlinnaKernel z t‖ * (1 + t ^ 2)⁻¹ := by
        rw [hnorm, mul_comm, inv_mul_cancel_left₀ (by positivity)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (norm_nevanlinnaKernel_le hz t) (by positivity)

/-- At `z = i` the subtracted resolvent kernel is `i / (1 + t ^ 2)`. -/
@[simp]
theorem subtractedResolventKernel_I (t : ℝ) :
    subtractedResolventKernel I t = I * (((1 + t ^ 2)⁻¹ : ℝ) : ℂ) := by
  have h : (t : ℂ) - I ≠ 0 := ofReal_sub_ne_zero_of_im_ne_zero (by simp) t
  have h' : (t : ℂ) + I ≠ 0 := by
    simpa using ofReal_sub_ne_zero_of_im_ne_zero (z := -I) (by simp) t
  have hsq : 1 + (t : ℂ) ^ 2 = ((t : ℂ) - I) * ((t : ℂ) + I) := by
    ring_nf
    rw [I_sq]
    ring
  rw [subtractedResolventKernel_def]
  push_cast
  rw [hsq]
  field_simp
  ring

private theorem toReal_smul_subtractedResolventKernel {z : ℂ} (hz : z.im ≠ 0) (t : ℝ) :
    (ENNReal.ofReal (1 + t ^ 2)).toReal • subtractedResolventKernel z t = nevanlinnaKernel z t := by
  rw [ENNReal.toReal_ofReal (by positivity), real_smul,
    nevanlinnaKernel_eq_one_add_sq_mul_subtractedResolventKernel
      (ofReal_sub_ne_zero_of_im_ne_zero hz t)]
  push_cast
  rfl

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

/-- **Density conversion.** Under the density change `dν = (1 + t ^ 2) dρ`, the integral of the
subtracted resolvent kernel against `ν` is the integral of the Nevanlinna kernel against `ρ`. -/
theorem integral_subtractedResolventKernel_withDensity (rho : Measure ℝ) {z : ℂ}
    (hz : z.im ≠ 0) :
    ∫ t, subtractedResolventKernel z t ∂rho.withDensity (fun t ↦ ENNReal.ofReal (1 + t ^ 2)) =
      ∫ t, nevanlinnaKernel z t ∂rho := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [toReal_smul_subtractedResolventKernel hz]

/-- Under the density change `dν = (1 + t ^ 2) dρ`, the subtracted resolvent kernel is
`ν`-integrable exactly when the Nevanlinna kernel is `ρ`-integrable. -/
theorem integrable_subtractedResolventKernel_withDensity_iff (rho : Measure ℝ) {z : ℂ}
    (hz : z.im ≠ 0) :
    Integrable (subtractedResolventKernel z)
        (rho.withDensity fun t ↦ ENNReal.ofReal (1 + t ^ 2)) ↔
      Integrable (nevanlinnaKernel z) rho := by
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [toReal_smul_subtractedResolventKernel hz]

/-- **Weighted-mass identity.** Under the density change `dν = (1 + t ^ 2) dρ`, the weighted mass
`∫ (1 + t ^ 2)⁻¹ dν` is the total mass of `ρ`. -/
theorem lintegral_inv_one_add_sq_withDensity (rho : Measure ℝ) :
    ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂rho.withDensity (fun t ↦ ENNReal.ofReal (1 + t ^ 2)) =
      rho Set.univ := by
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (by fun_prop), ← lintegral_one]
  refine lintegral_congr fun t ↦ ?_
  have ht : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul ht.le, mul_inv_cancel₀ ht.ne', ENNReal.ofReal_one]

/-- Reweighting by `(1 + t ^ 2)⁻¹` and then by `1 + t ^ 2` recovers the original measure, so
every measure on `ℝ` arises from the density change `dν = (1 + t ^ 2) dρ`. -/
theorem withDensity_inv_one_add_sq_withDensity (nu : Measure ℝ) :
    (nu.withDensity fun t ↦ ENNReal.ofReal (1 + t ^ 2)⁻¹).withDensity
        (fun t ↦ ENNReal.ofReal (1 + t ^ 2)) = nu := by
  convert withDensity_inv_same (μ := nu) (f := fun t ↦ ENNReal.ofReal (1 + t ^ 2)⁻¹)
    (by fun_prop) (.of_forall fun t ↦ (ENNReal.ofReal_pos.2 (by positivity)).ne')
    (.of_forall fun _ ↦ ENNReal.ofReal_ne_top) using 2
  funext t
  rw [ENNReal.ofReal_inv_of_pos (by positivity), inv_inv]

end MeasureTheory.Measure

namespace TauCeti

/-- Conjugating the parameter conjugates the subtracted resolvent kernel. -/
@[simp]
theorem subtractedResolventKernel_conj (z : ℂ) (t : ℝ) :
    subtractedResolventKernel (conj z) t = conj (subtractedResolventKernel z t) := by
  simp only [subtractedResolventKernel_def, map_sub, map_inv₀, map_div₀, map_add, map_one,
    map_pow, conj_ofReal]

/-- The imaginary part of the subtracted resolvent kernel is `Im z / |t - z| ^ 2`. -/
@[simp]
theorem subtractedResolventKernel_im (z : ℂ) (t : ℝ) :
    (subtractedResolventKernel z t).im = z.im / normSq ((t : ℂ) - z) := by
  have : (t : ℂ) / (1 + (t : ℂ) ^ 2) = ((t / (1 + t ^ 2) : ℝ) : ℂ) := by push_cast; rfl
  rw [subtractedResolventKernel_def, sub_im, this, ofReal_im, sub_zero, inv_im, sub_im,
    ofReal_im, zero_sub, neg_neg]

/-- On the imaginary axis, the imaginary part of the subtracted resolvent kernel is
`y / (t ^ 2 + y ^ 2)`. -/
theorem subtractedResolventKernel_ofReal_mul_I_im (y t : ℝ) :
    (subtractedResolventKernel (y * I) t).im = y / (t ^ 2 + y ^ 2) := by
  rw [subtractedResolventKernel_im, normSq_apply]
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, sub_re, sub_im]
  ring

/-- Every finite measure `ν` has finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν`, since the weight is at
most `1`. -/
theorem lintegral_inv_one_add_sq_lt_top (nu : Measure ℝ) [IsFiniteMeasure nu] :
    ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤ :=
  (lintegral_mono fun t ↦ ENNReal.ofReal_le_one.2 (inv_le_one_of_one_le₀
    (by nlinarith [sq_nonneg t]))).trans_lt (lintegral_one.trans_lt (measure_lt_top nu _))

/-- The subtracted resolvent kernel at a nonreal point is integrable against every measure `ν` of
finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν`. -/
theorem integrable_subtractedResolventKernel {nu : Measure ℝ}
    (hnu : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (subtractedResolventKernel z) nu := by
  have := isFiniteMeasure_withDensity hnu.ne
  have hH {w : ℂ} (hw : w ∈ UpperHalfPlane.upperHalfPlaneSet) :
      Integrable (subtractedResolventKernel w) nu := by
    rw [← nu.withDensity_inv_one_add_sq_withDensity,
      Measure.integrable_subtractedResolventKernel_withDensity_iff _ (ne_of_gt hw)]
    exact integrable_nevanlinnaKernel hw _
  rcases hz.lt_or_gt with hz | hz
  · have h := (conjCLE : ℂ →L[ℝ] ℂ).integrable_comp (hH (w := conj z) (by simpa using hz))
    simpa [subtractedResolventKernel_conj] using h
  · exact hH hz

/-- At a nonreal point, the absolute imaginary part `|Im z| / |t - z| ^ 2` of the subtracted
resolvent kernel dominates the weight `(1 + t ^ 2)⁻¹` up to a constant. -/
theorem inv_one_add_sq_le_mul_abs_im_subtractedResolventKernel {z : ℂ} (hz : z.im ≠ 0)
    (t : ℝ) :
    (1 + t ^ 2)⁻¹ ≤ 2 * (1 + ‖z‖ ^ 2) / |z.im| * |(subtractedResolventKernel z t).im| := by
  have : 0 < |z.im| := abs_pos.2 hz
  have hns : normSq ((t : ℂ) - z) ≤ 2 * (1 + ‖z‖ ^ 2) * (1 + t ^ 2) := by
    have hre := (normSq_eq_norm_sq z).symm
    rw [normSq_apply] at hre ⊢
    simp only [sub_re, ofReal_re, sub_im, ofReal_im] at *
    nlinarith [sq_nonneg (t + z.re), sq_nonneg t, sq_nonneg z.re, sq_nonneg z.im,
      sq_nonneg (t * z.re), sq_nonneg (t * z.im)]
  have hpos : 0 < normSq ((t : ℂ) - z) :=
    normSq_pos.2 (ofReal_sub_ne_zero_of_im_ne_zero hz t)
  rw [subtractedResolventKernel_im, abs_div, abs_of_pos hpos]
  calc (1 + t ^ 2)⁻¹ = 2 * (1 + ‖z‖ ^ 2) / |z.im| *
        (|z.im| / (2 * (1 + ‖z‖ ^ 2) * (1 + t ^ 2))) := by field_simp
    _ ≤ _ := by gcongr

/-- If the imaginary part of the subtracted resolvent kernel at a nonreal point is `ν`-integrable,
then `ν` has finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν`. -/
theorem lintegral_lt_top_of_integrable_im {nu : Measure ℝ} {z : ℂ} (hz : z.im ≠ 0)
    (h : Integrable (fun t ↦ (subtractedResolventKernel z t).im) nu) :
    ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤ := by
  refine Integrable.lintegral_lt_top ?_
  refine (h.norm.const_mul (2 * (1 + ‖z‖ ^ 2) / |z.im|)).mono' (by fun_prop)
    (.of_forall fun t ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
  exact inv_one_add_sq_le_mul_abs_im_subtractedResolventKernel hz t

/-- At a nonreal point, the imaginary part of the subtracted resolvent kernel is `ν`-integrable
exactly when `ν` has finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν`. -/
theorem integrable_im_subtractedResolventKernel_iff {nu : Measure ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun t ↦ (subtractedResolventKernel z t).im) nu ↔
      ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤ :=
  ⟨lintegral_lt_top_of_integrable_im hz, fun h ↦ (integrable_subtractedResolventKernel h hz).im⟩

/-- At a nonreal point, the subtracted resolvent kernel is `ν`-integrable exactly when `ν` has
finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν`. -/
theorem integrable_subtractedResolventKernel_iff {nu : Measure ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (subtractedResolventKernel z) nu ↔
      ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤ :=
  ⟨fun h ↦ lintegral_lt_top_of_integrable_im hz h.im,
    fun h ↦ integrable_subtractedResolventKernel h hz⟩

/-- At a nonreal point, the integral of the subtracted resolvent kernel against a measure `ν`
without finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν` is `0`, since the kernel is not integrable. -/
theorem integral_subtractedResolventKernel_eq_zero {nu : Measure ℝ}
    (hnu : ¬∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤) {z : ℂ} (hz : z.im ≠ 0) :
    ∫ t, subtractedResolventKernel z t ∂nu = 0 :=
  integral_undef (mt (integrable_subtractedResolventKernel_iff hz).1 hnu)

/-- At a nonreal point, the integral of the imaginary part of the subtracted resolvent kernel
against a measure `ν` without finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν` is `0`, since it is not
integrable. -/
theorem integral_im_subtractedResolventKernel_eq_zero {nu : Measure ℝ}
    (hnu : ¬∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤) {z : ℂ} (hz : z.im ≠ 0) :
    ∫ t, (subtractedResolventKernel z t).im ∂nu = 0 :=
  integral_undef (mt (integrable_im_subtractedResolventKernel_iff hz).1 hnu)

/-- **Herglotz representation of a Pick function.** A function holomorphic on the upper
half-plane with nonnegative imaginary part is `F z = Re F(i) + b z + ∫ ((t - z)⁻¹ -
t / (1 + t ^ 2)) dν(t)`, with `b ≥ 0` and `ν` a positive measure of finite weighted mass
`∫ (1 + t ^ 2)⁻¹ dν`. -/
theorem exists_eq_subtractedResolventKernel_add {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (him : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im) :
    ∃ (b : ℝ) (nu : Measure ℝ), 0 ≤ b ∧ ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤ ∧
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        F z = (F I).re + b * z + ∫ t, subtractedResolventKernel z t ∂nu := by
  obtain ⟨rho, b, hrho, hb, hrep⟩ := exists_isFiniteMeasure_eq_nevanlinnaKernel_add hF him
  refine ⟨b, rho.withDensity fun t ↦ ENNReal.ofReal (1 + t ^ 2), hb, ?_, fun z hz ↦ ?_⟩
  · rw [Measure.lintegral_inv_one_add_sq_withDensity]
    exact measure_lt_top rho _
  · rw [rho.integral_subtractedResolventKernel_withDensity (ne_of_gt hz), hrep z hz]
    ring

/-- **The constant term of a Herglotz representation.** In any representation
`F z = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` on the upper half-plane with real `a`
and `b`, the constant term is `a = Re F(i)`. -/
theorem re_eq_of_eq_subtractedResolventKernel_add {F : ℂ → ℂ} {a b : ℝ} {nu : Measure ℝ}
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu) :
    a = (F I).re := by
  rw [hrep I (by simp)]
  simp_rw [subtractedResolventKernel_I]
  rw [integral_const_mul, integral_complex_ofReal]
  simp

private theorem tendsto_im_div_of_eq_subtractedResolventKernel_add_of_lt_top {F : ℂ → ℂ} {a b : ℝ}
    {nu : Measure ℝ} (hnu : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu) :
    Tendsto (fun y : ℝ ↦ (F (y * I)).im / y) atTop (𝓝 b) := by
  set rho := nu.withDensity fun t ↦ ENNReal.ofReal (1 + t ^ 2)⁻¹
  have := isFiniteMeasure_withDensity hnu.ne
  have hnu' : rho.withDensity (fun t ↦ ENNReal.ofReal (1 + t ^ 2)) = nu :=
    nu.withDensity_inv_one_add_sq_withDensity
  let g : ℝ → ℝ → ℝ := fun y t ↦ (1 + t ^ 2) / (t ^ 2 + y ^ 2)
  have heq : ∀ᶠ y : ℝ in atTop, b + ∫ t, g y t ∂rho = (F (y * I)).im / y := by
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hz : (y : ℂ) * I ∈ UpperHalfPlane.upperHalfPlaneSet := by simpa using hy
    rw [hrep _ hz, ← hnu', rho.integral_subtractedResolventKernel_withDensity (ne_of_gt hz)]
    have him : (∫ t, nevanlinnaKernel (y * I) t ∂rho).im = ∫ t, y * g y t ∂rho := by
      rw [← RCLike.im_to_complex, ← integral_im (integrable_nevanlinnaKernel hz rho)]
      refine integral_congr_ae (.of_forall fun t ↦ ?_)
      simp only [RCLike.im_to_complex, nevanlinnaKernel_im, mul_im, ofReal_re, I_im,
        ofReal_im, I_re, normSq_apply, sub_re, sub_im, mul_re, g]
      ring
    rw [add_im, add_im, him, integral_const_mul]
    simp only [ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, add_zero, zero_add, mul_one]
    field_simp
    ring
  have h0 : Tendsto (fun y ↦ ∫ t, g y t ∂rho) atTop (𝓝 0) := by
    rw [← integral_zero ℝ ℝ (μ := rho)]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1) ?_ ?_
      (integrable_const 1) (.of_forall fun t ↦ ?_)
    · exact .of_forall fun y ↦ (by fun_prop : Measurable (g y)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with y hy
      refine .of_forall fun t ↦ ?_
      have hden : 0 < t ^ 2 + y ^ 2 := by positivity
      rw [Real.norm_of_nonneg (by positivity), div_le_one hden]
      nlinarith
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero))
  simpa only [add_zero] using (tendsto_const_nhds (x := b)).add h0 |>.congr' heq

/-- **The linear coefficient of a Herglotz representation.** In any representation
`F z = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` on the upper half-plane with real `a`
and `b`, the linear coefficient is the limit of `Im F(i y) / y` as `y → ∞`.  No finiteness is
assumed: if `∫ (1 + t ^ 2)⁻¹ dν` is infinite, the kernel is not integrable and the integral term
vanishes. -/
theorem tendsto_im_div_of_eq_subtractedResolventKernel_add {F : ℂ → ℂ} {a b : ℝ}
    {nu : Measure ℝ}
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu) :
    Tendsto (fun y : ℝ ↦ (F (y * I)).im / y) atTop (𝓝 b) := by
  by_cases hnu : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤
  · exact tendsto_im_div_of_eq_subtractedResolventKernel_add_of_lt_top hnu hrep
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  have hz : (y : ℂ) * I ∈ UpperHalfPlane.upperHalfPlaneSet := by simpa using hy
  rw [hrep _ hz, integral_subtractedResolventKernel_eq_zero hnu (ne_of_gt hz)]
  simp only [add_zero, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one,
    zero_mul, zero_add]
  field_simp

/-- **Uniqueness of the constants of a Herglotz representation.** Two representations
`F z = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` of the same function on the upper
half-plane have the same constant term and the same linear coefficient. -/
theorem eq_and_eq_of_eq_subtractedResolventKernel_add {F : ℂ → ℂ} {a a' b b' : ℝ}
    {nu nu' : Measure ℝ}
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu)
    (hrep' : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a' + b' * z + ∫ t, subtractedResolventKernel z t ∂nu') :
    a = a' ∧ b = b' :=
  ⟨(re_eq_of_eq_subtractedResolventKernel_add hrep).trans
      (re_eq_of_eq_subtractedResolventKernel_add hrep').symm,
    tendsto_nhds_unique (tendsto_im_div_of_eq_subtractedResolventKernel_add hrep)
      (tendsto_im_div_of_eq_subtractedResolventKernel_add hrep')⟩

end TauCeti

namespace MeasureTheory.Measure

open TauCeti

/-- Off the real axis, integrals of the subtracted resolvent kernel against any measure `ν` are
Nevanlinna integrals against `(1 + t ^ 2)⁻¹ ν`, which is a finite measure exactly when `ν` has
finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν`. This is
`MeasureTheory.Measure.integral_subtractedResolventKernel_withDensity` read from `ν`. -/
theorem integral_subtractedResolventKernel_eq_integral_nevanlinnaKernel (nu : Measure ℝ) {z : ℂ}
    (hz : z.im ≠ 0) :
    ∫ t, subtractedResolventKernel z t ∂nu =
      ∫ t, nevanlinnaKernel z t ∂nu.withDensity fun t ↦ ENNReal.ofReal (1 + t ^ 2)⁻¹ := by
  conv_lhs => rw [← nu.withDensity_inv_one_add_sq_withDensity]
  exact Measure.integral_subtractedResolventKernel_withDensity _ hz

end MeasureTheory.Measure

namespace TauCeti

/-- **Uniqueness of the measure of a Herglotz representation.** Two representations
`F z = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` of the same function on the upper
half-plane, with measures of finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν`, have the same measure.
The finiteness is needed: for measures of infinite weighted mass the integral term vanishes. -/
theorem eq_of_eq_subtractedResolventKernel_add {F : ℂ → ℂ} {a a' b b' : ℝ}
    {nu nu' : Measure ℝ} (hnu : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu < ⊤)
    (hnu' : ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂nu' < ⊤)
    (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a + b * z + ∫ t, subtractedResolventKernel z t ∂nu)
    (hrep' : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      F z = a' + b' * z + ∫ t, subtractedResolventKernel z t ∂nu') :
    nu = nu' := by
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_eq_subtractedResolventKernel_add hrep hrep'
  have := isFiniteMeasure_withDensity hnu.ne
  have := isFiniteMeasure_withDensity hnu'.ne
  suffices h : nu.withDensity (fun t ↦ ENNReal.ofReal (1 + t ^ 2)⁻¹) =
      nu'.withDensity (fun t ↦ ENNReal.ofReal (1 + t ^ 2)⁻¹) by
    rw [← nu.withDensity_inv_one_add_sq_withDensity, h,
      nu'.withDensity_inv_one_add_sq_withDensity]
  refine Measure.ext_of_integral_nevanlinnaKernel fun z hz ↦ ?_
  have := (hrep z hz).symm.trans (hrep' z hz)
  rwa [add_right_inj,
    nu.integral_subtractedResolventKernel_eq_integral_nevanlinnaKernel (ne_of_gt hz),
    nu'.integral_subtractedResolventKernel_eq_integral_nevanlinnaKernel (ne_of_gt hz)] at this

/-- **The Herglotz representation theorem.** A function holomorphic on the upper half-plane with
nonnegative imaginary part has a unique representation
`F z = a + b z + ∫ ((t - z)⁻¹ - t / (1 + t ^ 2)) dν(t)` with `b ≥ 0` and `ν` a positive measure
of finite weighted mass `∫ (1 + t ^ 2)⁻¹ dν`. The constant term of this representation is
`Re F(i)`, by `TauCeti.re_eq_of_eq_subtractedResolventKernel_add`. -/
theorem existsUnique_eq_subtractedResolventKernel_add {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F UpperHalfPlane.upperHalfPlaneSet)
    (him : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, 0 ≤ (F z).im) :
    ∃! p : ℝ × ℝ × Measure ℝ, 0 ≤ p.2.1 ∧ ∫⁻ t, ENNReal.ofReal (1 + t ^ 2)⁻¹ ∂p.2.2 < ⊤ ∧
      ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
        F z = p.1 + p.2.1 * z + ∫ t, subtractedResolventKernel z t ∂p.2.2 := by
  obtain ⟨b, nu, hb, hnu, hrep⟩ := exists_eq_subtractedResolventKernel_add hF him
  refine ⟨((F I).re, b, nu), ⟨hb, hnu, hrep⟩, fun ⟨a', b', nu'⟩ ⟨_, hnu', hrep'⟩ ↦ ?_⟩
  obtain rfl := eq_of_eq_subtractedResolventKernel_add hnu' hnu hrep' hrep
  obtain ⟨rfl, rfl⟩ := eq_and_eq_of_eq_subtractedResolventKernel_add hrep' hrep
  rfl

end TauCeti

end
