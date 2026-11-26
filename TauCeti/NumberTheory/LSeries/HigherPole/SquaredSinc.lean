/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Fourier.SincSq
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.SincSq
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# The normalised squared-sinc kernel

For real `λ` and `v` this file defines the kernel

`K_λ(v) = squaredSinc λ v = (λ / π) * sinc (λ v) ^ 2`,

with Mathlib's `Real.sinc` (so `sinc 0 = 1`). For `λ > 0` it is a continuous probability density
on `ℝ`, and it is the inverse Fourier transform, in angular frequency, of the triangle
`1 - |y| / (2λ)` supported on `[-2λ, 2λ]`:

`K_λ(v) = (1 / 2π) ∫_{-2λ}^{2λ} (1 - |y| / (2λ)) e^{i y v} dy`.

As `λ → ∞` its mass concentrates at the origin. These are the properties a Tauberian argument
needs from a smoothing kernel: positivity and concentration let monotonicity remove the smoothing,
while the triangle formula, an integral over the compact frequency range `[-2λ, 2λ]`, means that
the smoothed function is controlled by boundary values of a Laplace transform on a compact segment
only.

## Main definitions

* `TauCeti.HigherPoleTauberian.squaredSinc`: the kernel `K_λ(v)`, total in `λ` and `v`.

## Main results

* `squaredSinc_nonneg`, `squaredSinc_le`, `squaredSinc_le_inv_mul_sq`, `squaredSinc_neg_right`,
  `continuous_squaredSinc`, `integrable_squaredSinc`: positivity, the bounds `K_λ ≤ λ / π` and
  `K_λ(v) ≤ (π λ v ^ 2)⁻¹`, evenness, continuity and integrability.
* `squaredSinc_intCast_mul_pi_div`, `squaredSinc_pi_div`: `K_λ` vanishes at the nonzero multiples
  of `π / λ`.
* `squaredSinc_mass`: `∫ v, K_λ v = 1` for `λ > 0`.
* `squaredSinc_fourier`, `integral_squaredSinc_mul_cos`, `integral_cos_mul_squaredSinc_sub`,
  `integral_cos_mul_squaredSinc_eq_zero`: the inverse Fourier representation, forward cosine
  transform `∫ v, K_λ(v) cos (ξ v) = max (1 - |ξ| / (2λ)) 0`, shifted cosine convolution, and
  band-limit vanishing for `2λ ≤ |ξ|`.
* `integral_squaredSinc_tail_le`, `tendsto_intervalIntegral_squaredSinc`,
  `tendsto_integral_squaredSinc_tail`, `integral_Icc_squaredSinc_shift`,
  `setIntegral_abs_sub_ge_squaredSinc`, `setIntegral_Iio_squaredSinc_le`,
  `mul_intervalIntegral_squaredSinc_le_setIntegral_Ici`, `setIntegral_Ici_mul_squaredSinc_le`:
  the quantitative tail bound `≤ 2 / (π λ h)`, concentration on `[-h, h]` as `λ → ∞`, shifted
  window and tail integrals, and two-sided half-line window-and-tail comparisons.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242: §3.3.3–3.3.5, pp. 224–226 (a continuous weight on `[-2λ, 2λ]`, its Fourier
  transform, and the choice of the triangle), and §3.4, pp. 227–228 (positivity of the kernel, its
  mass near the origin and its tails). Delange's kernel is the unnormalised transform of the same
  triangle, `π K_λ`.
-/

public section

noncomputable section

open MeasureTheory Filter Set Real
open scoped FourierTransform Topology

namespace TauCeti.HigherPoleTauberian

/-- **The normalised squared-sinc kernel** `K_λ(v) = (λ / π) * sinc (λ v) ^ 2`, written
`squaredSinc ell v` with `ell = λ`.

The definition is total. For `λ > 0` it is a probability density on `ℝ` (`squaredSinc_mass`), and
for `λ ≥ 0` it is the inverse Fourier transform, in angular frequency, of the triangle
`1 - |y| / (2λ)` on `[-2λ, 2λ]` (`squaredSinc_fourier`). -/
def squaredSinc (ell v : ℝ) : ℝ :=
  ell / π * sinc (ell * v) ^ 2

variable {ell h : ℝ}

/-- The defining formula of `squaredSinc`. -/
theorem squaredSinc_def (ell v : ℝ) : squaredSinc ell v = ell / π * sinc (ell * v) ^ 2 := (rfl)

/-- The value at the origin is `λ / π`. -/
@[simp]
theorem squaredSinc_zero_right (ell : ℝ) : squaredSinc ell 0 = ell / π := by
  simp [squaredSinc_def]

/-- The kernel of bandwidth `0` vanishes. -/
@[simp]
theorem squaredSinc_zero_left (v : ℝ) : squaredSinc 0 v = 0 := by
  simp [squaredSinc_def]

/-- The kernel is even. -/
@[simp]
theorem squaredSinc_neg_right (ell v : ℝ) : squaredSinc ell (-v) = squaredSinc ell v := by
  simp [squaredSinc_def]

/-- The kernel is nonnegative for a nonnegative bandwidth. -/
theorem squaredSinc_nonneg (hell : 0 ≤ ell) (v : ℝ) : 0 ≤ squaredSinc ell v := by
  rw [squaredSinc_def]
  positivity

/-- The kernel is bounded by its value `λ / π` at the origin. -/
theorem squaredSinc_le (hell : 0 ≤ ell) (v : ℝ) : squaredSinc ell v ≤ ell / π := by
  rw [squaredSinc_def]
  exact mul_le_of_le_one_right (by positivity)
    ((sq_le_one_iff_abs_le_one _).2 (abs_sinc_le_one _))

/-- Away from the origin, the kernel satisfies the inverse-square bound
`K_λ(v) ≤ (π λ v ^ 2)⁻¹` for `λ ≥ 0`. -/
theorem squaredSinc_le_inv_mul_sq {v : ℝ} (hell : 0 ≤ ell) (hv : v ≠ 0) :
    squaredSinc ell v ≤ (π * ell * v ^ 2)⁻¹ := by
  rcases hell.eq_or_lt with rfl | hell
  · simp
  rw [squaredSinc_def, sinc_of_ne_zero (mul_ne_zero hell.ne' hv), div_pow]
  calc ell / π * (sin (ell * v) ^ 2 / (ell * v) ^ 2)
      ≤ ell / π * (1 / (ell * v) ^ 2) := by
        gcongr
        exact sin_sq_le_one _
    _ = (π * ell * v ^ 2)⁻¹ := by
        field_simp

/-- The kernel vanishes at every nonzero integer multiple of `π / λ`. -/
theorem squaredSinc_intCast_mul_pi_div (ell : ℝ) {n : ℤ} (hn : n ≠ 0) :
    squaredSinc ell (n * π / ell) = 0 := by
  rcases eq_or_ne ell 0 with rfl | hell
  · simp
  have harg : ell * (n * π / ell) = n * π := by field_simp
  have hne : (n : ℝ) * π ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hn) pi_ne_zero
  simp [squaredSinc_def, harg, sinc_of_ne_zero hne, sin_int_mul_pi]

/-- The kernel vanishes at `π / λ`. -/
@[simp]
theorem squaredSinc_pi_div (ell : ℝ) : squaredSinc ell (π / ell) = 0 := by
  simpa using squaredSinc_intCast_mul_pi_div ell one_ne_zero

/-- The kernel is continuous for every bandwidth. -/
@[fun_prop]
theorem continuous_squaredSinc (ell : ℝ) : Continuous (squaredSinc ell) := by
  rw [funext (squaredSinc_def ell)]
  fun_prop

/-- The kernel is Lebesgue integrable on `ℝ` for every bandwidth. -/
theorem integrable_squaredSinc (ell : ℝ) : Integrable (squaredSinc ell) := by
  rcases eq_or_ne ell 0 with rfl | hell
  · simp_rw [funext squaredSinc_zero_left]
    exact integrable_zero _ _ _
  rw [funext (squaredSinc_def ell)]
  exact (integrable_sinc_sq.comp_mul_left' hell).const_mul _

/-- **The kernel has total mass one.** -/
theorem squaredSinc_mass (hell : 0 < ell) : ∫ v, squaredSinc ell v = 1 := by
  simp_rw [squaredSinc_def]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun w ↦ sinc w ^ 2) ell,
    integral_sinc_sq, smul_eq_mul, abs_of_pos (inv_pos.2 hell)]
  field_simp

/-! ### Concentration at the origin -/

/-- The mass of `[-h, h]` is `(1 / π) ∫_{-λh}^{λh} sinc²`. -/
private theorem intervalIntegral_squaredSinc (hell : 0 < ell) (h : ℝ) :
    ∫ v in -h..h, squaredSinc ell v = π⁻¹ * ∫ w in -(ell * h)..ell * h, sinc w ^ 2 := by
  simp_rw [squaredSinc_def]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun w ↦ sinc w ^ 2) hell.ne', smul_eq_mul, mul_neg]
  field_simp

/-- **Concentration**: for `h > 0`, the mass of `K_λ` on `[-h, h]` tends to `1` as `λ → ∞`. -/
theorem tendsto_intervalIntegral_squaredSinc (hh : 0 < h) :
    Tendsto (fun ell ↦ ∫ v in -h..h, squaredSinc ell v) atTop (𝓝 1) := by
  have hb : Tendsto (fun ell : ℝ ↦ ell * h) atTop atTop := tendsto_id.atTop_mul_const hh
  have hlim := (intervalIntegral_tendsto_integral integrable_sinc_sq
    (tendsto_neg_atTop_atBot.comp hb) hb).const_mul π⁻¹
  rw [integral_sinc_sq, inv_mul_cancel₀ pi_ne_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ell hell
  exact (intervalIntegral_squaredSinc hell h).symm

/-- **Quantitative tail bound**: for `λ ≥ 0` and `h > 0`, the mass of `K_λ` on `{v | h ≤ |v|}`
is at most `2 / (π λ h)`. -/
theorem integral_squaredSinc_tail_le (hell : 0 ≤ ell) (hh : 0 < h) :
    ∫ v in {v : ℝ | h ≤ |v|}, squaredSinc ell v ≤ 2 / (π * ell * h) := by
  rcases hell.eq_or_lt with rfl | hell
  · simp [squaredSinc_zero_left]
  have hae : ({v : ℝ | h ≤ |v|} : Set ℝ) =ᵐ[volume] {v : ℝ | h < |v|} := by
    have h1 : {v : ℝ | h ≤ |v|} = (Ioo (-h) h)ᶜ := by ext; simp [← not_lt, abs_lt]
    have h2 : {v : ℝ | h < |v|} = (Icc (-h) h)ᶜ := by ext; simp [← not_le, abs_le]
    rw [h1, h2]
    exact Ioo_ae_eq_Icc.compl
  have hint : IntegrableOn (fun v : ℝ ↦ (v ^ 2)⁻¹) {v : ℝ | h < |v|} :=
    Integrable.of_integral_ne_zero <| by
      rw [TauCeti.integral_lt_abs_inv_sq hh.le]
      exact div_ne_zero two_ne_zero hh.ne'
  rw [setIntegral_congr_set hae]
  calc ∫ v in {v : ℝ | h < |v|}, squaredSinc ell v
      ≤ ∫ v in {v : ℝ | h < |v|}, (π * ell)⁻¹ * (v ^ 2)⁻¹ := by
        refine setIntegral_mono_on (integrable_squaredSinc ell).integrableOn
          (hint.const_mul _) (measurableSet_lt measurable_const continuous_abs.measurable)
          fun v (hv : h < |v|) ↦ ?_
        exact (squaredSinc_le_inv_mul_sq hell.le (abs_pos.mp (hh.trans hv))).trans_eq (by ring)
    _ = 2 / (π * ell * h) := by
        rw [integral_const_mul, TauCeti.integral_lt_abs_inv_sq hh.le]
        ring

/-- **Tail concentration**: for `h > 0`, the mass of `K_λ` on `{v | h ≤ |v|}` tends to `0` as
`λ → ∞`. -/
theorem tendsto_integral_squaredSinc_tail (hh : 0 < h) :
    Tendsto (fun ell ↦ ∫ v in {v | h ≤ |v|}, squaredSinc ell v) atTop (𝓝 0) := by
  have hs : MeasurableSet {v : ℝ | h ≤ |v|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hcompl : {v : ℝ | h ≤ |v|}ᶜ = Ioo (-h) h := by
    ext v
    simp [abs_lt]
  have hlim := (tendsto_intervalIntegral_squaredSinc hh).const_sub 1
  rw [sub_self] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with ell hell
  rw [← squaredSinc_mass hell, ← integral_add_compl hs (integrable_squaredSinc ell), hcompl,
    intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
    add_sub_cancel_right]

/-- For `h ≥ 0`, the mass of `t ↦ K_λ(t - T₀)` on `[T₀ - h, T₀ + h]` equals
`∫_{-h}^h K_λ(v) dv`. -/
theorem integral_Icc_squaredSinc_shift {T₀ : ℝ} (hh : 0 ≤ h) :
    ∫ t in Icc (T₀ - h) (T₀ + h), squaredSinc ell (t - T₀) =
      ∫ v in (-h)..h, squaredSinc ell v := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_right (squaredSinc ell) T₀,
    sub_sub_cancel_left, add_sub_cancel_left]

/-- The tail integral of `t ↦ K_λ(t - T₀)` over `{t | h ≤ |t - T₀|}` equals
`∫_{h ≤ |v|} K_λ(v) dv`. -/
theorem setIntegral_abs_sub_ge_squaredSinc (ell T₀ h : ℝ) :
    ∫ t in {t : ℝ | h ≤ |t - T₀|}, squaredSinc ell (t - T₀) =
      ∫ v in {v : ℝ | h ≤ |v|}, squaredSinc ell v :=
  (measurePreserving_sub_right volume T₀).setIntegral_preimage_emb
    (measurableEmbedding_subRight T₀) (squaredSinc ell) {v : ℝ | h ≤ |v|}

/-- For `λ ≥ 0`, the left tail of `t ↦ K_λ(t - T)` over `(-∞, t₀)` is at most the symmetric tail
mass over `{v | T - t₀ ≤ |v|}`. -/
theorem setIntegral_Iio_squaredSinc_le {t₀ T : ℝ} (hell : 0 ≤ ell) :
    ∫ t in Iio t₀, squaredSinc ell (t - T) ≤
      ∫ v in {v : ℝ | T - t₀ ≤ |v|}, squaredSinc ell v := by
  have hpre : (· - T) ⁻¹' Iio (t₀ - T) = Iio t₀ := by ext; simp
  rw [← hpre, (measurePreserving_sub_right volume T).setIntegral_preimage_emb
    (measurableEmbedding_subRight T) (squaredSinc ell) (Iio (t₀ - T))]
  refine setIntegral_mono_set (integrable_squaredSinc ell).integrableOn
    (ae_of_all _ fun v ↦ squaredSinc_nonneg hell v) (Eventually.of_forall fun v hv ↦ ?_)
  exact le_trans (by linarith [mem_Iio.mp hv]) (neg_le_abs v)

/-- **Lower window comparison on `[0, ∞)`.** For `λ ≥ 0`, `h ≥ 0`, and `T₀ - h ≥ 0`, if `J` is
nonnegative on `[0, ∞)` and bounded below by `c` on `[T₀ - h, T₀ + h]`, and
`t ↦ J t * K_λ(t - T₀)` is integrable on `[0, ∞)`, then
`c * ∫_{-h}^h K_λ(v) dv ≤ ∫_0^∞ J(t) K_λ(t - T₀) dt`. -/
theorem mul_intervalIntegral_squaredSinc_le_setIntegral_Ici {J : ℝ → ℝ} {T₀ c : ℝ}
    (hell : 0 ≤ ell) (hh : 0 ≤ h) (hT₀ : 0 ≤ T₀ - h)
    (hJ0 : ∀ t ∈ Ici (0 : ℝ), 0 ≤ J t)
    (hint : IntegrableOn (fun t : ℝ ↦ J t * squaredSinc ell (t - T₀)) (Ici 0))
    (hlow : ∀ t ∈ Icc (T₀ - h) (T₀ + h), c ≤ J t) :
    c * ∫ v in (-h)..h, squaredSinc ell v ≤
      ∫ t in Ici (0 : ℝ), J t * squaredSinc ell (t - T₀) := by
  have hsub : Icc (T₀ - h) (T₀ + h) ⊆ Ici (0 : ℝ) := fun t ht ↦ le_trans hT₀ ht.1
  have hcont : IntegrableOn (fun t : ℝ ↦ c * squaredSinc ell (t - T₀)) (Icc (T₀ - h) (T₀ + h)) :=
    (by fun_prop : Continuous fun t : ℝ ↦ c * squaredSinc ell (t - T₀)).integrableOn_Icc
  calc c * ∫ v in (-h)..h, squaredSinc ell v
      = ∫ t in Icc (T₀ - h) (T₀ + h), c * squaredSinc ell (t - T₀) := by
          rw [integral_const_mul, integral_Icc_squaredSinc_shift hh]
    _ ≤ ∫ t in Icc (T₀ - h) (T₀ + h), J t * squaredSinc ell (t - T₀) :=
          setIntegral_mono_on hcont (hint.mono_set hsub) measurableSet_Icc fun t ht ↦
            mul_le_mul_of_nonneg_right (hlow t ht) (squaredSinc_nonneg hell _)
    _ ≤ ∫ t in Ici (0 : ℝ), J t * squaredSinc ell (t - T₀) :=
          setIntegral_mono_set hint
            (ae_restrict_of_forall_mem measurableSet_Ici fun t ht ↦
              mul_nonneg (hJ0 t ht) (squaredSinc_nonneg hell _))
            (Eventually.of_forall hsub)

/-- **Upper window-and-tail comparison on `[0, ∞)`.** For `λ ≥ 0`, `U ≥ 0`, and `M ≥ 0`, if
`J ≤ M` on `[0, ∞)`, `J ≤ U` on `[T₀ - h, T₀ + h]`, and `t ↦ J t * K_λ(t - T₀)` is integrable on
`[0, ∞)`, then `∫_0^∞ J(t) K_λ(t - T₀) dt ≤ U + M * ∫_{h ≤ |v|} K_λ(v) dv`. -/
theorem setIntegral_Ici_mul_squaredSinc_le {J : ℝ → ℝ} {T₀ U M : ℝ}
    (hell : 0 ≤ ell) (hU : 0 ≤ U) (hM : 0 ≤ M)
    (hJM : ∀ t ∈ Ici (0 : ℝ), J t ≤ M)
    (hint : IntegrableOn (fun t : ℝ ↦ J t * squaredSinc ell (t - T₀)) (Ici 0))
    (hhigh : ∀ t ∈ Icc (T₀ - h) (T₀ + h), J t ≤ U) :
    ∫ t in Ici (0 : ℝ), J t * squaredSinc ell (t - T₀) ≤
      U + M * ∫ v in {v : ℝ | h ≤ |v|}, squaredSinc ell v := by
  rcases hell.eq_or_lt with rfl | hell
  · simp [hU]
  let S : Set ℝ := Icc (T₀ - h) (T₀ + h)
  have hsplit := integral_add_compl (μ := volume.restrict (Ici (0 : ℝ))) (s := S)
    measurableSet_Icc hint
  rw [Measure.restrict_restrict measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc.compl] at hsplit
  have hKshift : Integrable (fun t : ℝ ↦ squaredSinc ell (t - T₀)) :=
    (integrable_squaredSinc ell).comp_sub_right T₀
  have hwin : ∫ t in S ∩ Ici (0 : ℝ), J t * squaredSinc ell (t - T₀) ≤ U := by
    calc ∫ t in S ∩ Ici (0 : ℝ), J t * squaredSinc ell (t - T₀)
        ≤ ∫ t in S ∩ Ici (0 : ℝ), U * squaredSinc ell (t - T₀) :=
            setIntegral_mono_on (hint.mono_set Set.inter_subset_right)
              (hKshift.const_mul U).integrableOn (measurableSet_Icc.inter measurableSet_Ici)
              fun t ht ↦ mul_le_mul_of_nonneg_right (hhigh t ht.1) (squaredSinc_nonneg hell.le _)
      _ ≤ ∫ t : ℝ, U * squaredSinc ell (t - T₀) :=
            setIntegral_le_integral (hKshift.const_mul U)
              (ae_of_all _ fun t ↦ mul_nonneg hU (squaredSinc_nonneg hell.le _))
      _ = U := by
            rw [integral_const_mul, integral_sub_right_eq_self (squaredSinc ell) T₀,
              squaredSinc_mass hell, mul_one]
  have htail_sub : Sᶜ ∩ Ici (0 : ℝ) ⊆ {t : ℝ | h ≤ |t - T₀|} := fun t ht ↦
    le_of_not_gt fun (hlt : |t - T₀| < h) ↦
      ht.1 ⟨by linarith [(abs_lt.mp hlt).1], by linarith [(abs_lt.mp hlt).2]⟩
  have htail : ∫ t in Sᶜ ∩ Ici (0 : ℝ), J t * squaredSinc ell (t - T₀) ≤
      M * ∫ v in {v : ℝ | h ≤ |v|}, squaredSinc ell v := by
    calc ∫ t in Sᶜ ∩ Ici (0 : ℝ), J t * squaredSinc ell (t - T₀)
        ≤ ∫ t in Sᶜ ∩ Ici (0 : ℝ), M * squaredSinc ell (t - T₀) :=
            setIntegral_mono_on (hint.mono_set Set.inter_subset_right)
              (hKshift.const_mul M).integrableOn (measurableSet_Icc.compl.inter measurableSet_Ici)
              fun t ht ↦ mul_le_mul_of_nonneg_right (hJM t ht.2) (squaredSinc_nonneg hell.le _)
      _ ≤ ∫ t in {t : ℝ | h ≤ |t - T₀|}, M * squaredSinc ell (t - T₀) :=
            setIntegral_mono_set (hKshift.const_mul M).integrableOn
              (ae_of_all _ fun t ↦ mul_nonneg hM (squaredSinc_nonneg hell.le _))
              (Eventually.of_forall htail_sub)
      _ = M * ∫ v in {v : ℝ | h ≤ |v|}, squaredSinc ell v := by
            rw [integral_const_mul, setIntegral_abs_sub_ge_squaredSinc]
  linarith

/-! ### The triangle formula -/

/-- **The kernel is the inverse Fourier transform of the triangle.** For `λ ≥ 0` and every `v`,
`K_λ(v) = (1 / 2π) ∫_{-2λ}^{2λ} (1 - |y| / (2λ)) e^{i y v} dy`, the inverse Fourier transform, in
angular frequency, of the triangle `1 - |y| / (2λ)` supported on `[-2λ, 2λ]`. -/
theorem squaredSinc_fourier (hell : 0 ≤ ell) (v : ℝ) :
    (squaredSinc ell v : ℂ) = 1 / (2 * π) *
      ∫ y : ℝ in (-(2 * ell))..(2 * ell),
        ((1 - |y| / (2 * ell) : ℝ) : ℂ) * Complex.exp (Complex.I * y * v) := by
  rcases hell.eq_or_lt with rfl | hell
  · simp
  set F : ℝ → ℂ := fun y ↦ ((1 - |y| / (2 * ell) : ℝ) : ℂ) * Complex.exp (Complex.I * y * v)
  have hcomp := intervalIntegral.integral_comp_mul_left (a := -π⁻¹) (b := π⁻¹) F
    (by positivity : (2 * π * ell : ℝ) ≠ 0)
  have hcongr : ∫ w in (-π⁻¹)..π⁻¹, F ((2 * π * ell) * w) =
      ∫ w in (-π⁻¹)..π⁻¹,
        Complex.exp (2 * π * Complex.I * w * ↑(ell * v)) * ((max (1 - |π * w|) 0 : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun w hw ↦ ?_
    rw [uIcc_of_le (by linarith [inv_pos.mpr pi_pos] : -π⁻¹ ≤ π⁻¹)] at hw
    have hw1 : |π * w| ≤ 1 := by
      rw [abs_mul, abs_of_pos pi_pos]
      nlinarith [mul_inv_cancel₀ pi_pos.ne', abs_le.mpr hw, pi_pos]
    have hdiv : |(2 * π * ell) * w| / (2 * ell) = |π * w| := by
      rw [← abs_of_pos (by positivity : (0 : ℝ) < 2 * ell), ← abs_div]
      congr 1; field_simp
    simp only [F, hdiv, max_eq_left (sub_nonneg.mpr hw1)]
    push_cast; ring_nf
  rw [(by field_simp : (2 * π * ell) * (-π⁻¹) = -(2 * ell)),
    (by field_simp : (2 * π * ell) * π⁻¹ = 2 * ell), hcongr,
    TauCeti.intervalIntegral_cexp_mul_max_one_sub_abs_pi_mul, Complex.real_smul] at hcomp
  calc (squaredSinc ell v : ℂ) = ell * ((π⁻¹ * sinc (ell * v) ^ 2 : ℝ) : ℂ) := by
        rw [squaredSinc_def]; push_cast; ring
    _ = ell * (((2 * π * ell)⁻¹ : ℝ) * ∫ y : ℝ in -(2 * ell)..2 * ell, F y) := by rw [hcomp]
    _ = 1 / (2 * π) * ∫ y : ℝ in -(2 * ell)..2 * ell, F y := by
        push_cast; field_simp [Complex.ofReal_ne_zero.mpr hell.ne']

/-- **The cosine transform of the kernel is the triangle.** For `λ > 0` and every `ξ`,
`∫ v, K_λ(v) cos (ξ v) = max (1 - |ξ| / (2λ)) 0`; in particular it vanishes whenever
`2λ ≤ |ξ|`. -/
theorem integral_squaredSinc_mul_cos (hell : 0 < ell) (ξ : ℝ) :
    ∫ v : ℝ, squaredSinc ell v * cos (ξ * v) = max (1 - |ξ| / (2 * ell)) 0 := by
  have hrew : (fun v : ℝ ↦ squaredSinc ell v * cos (ξ * v)) =
      fun v ↦ (ell / π) * (sinc (ell * v) ^ 2 * cos ((ξ / ell) * (ell * v))) := funext fun v ↦ by
    rw [squaredSinc_def, ← mul_assoc (ξ / ell), div_mul_cancel₀ _ hell.ne']
    ring
  have habs : |ξ / ell| / 2 = |ξ| / (2 * ell) := by
    rw [abs_div, abs_of_pos hell, div_div, mul_comm ell 2]
  rw [hrew, integral_const_mul,
    Measure.integral_comp_mul_left (fun x : ℝ ↦ sinc x ^ 2 * cos ((ξ / ell) * x)) ell,
    abs_inv, abs_of_pos hell, smul_eq_mul, TauCeti.integral_sinc_sq_mul_cos, habs]
  field_simp

/-- **Shifted cosine convolution of the kernel.** For `λ > 0` and all `ξ` and `T`,
`∫ t, cos (ξ t) K_λ(t - T) = max (1 - |ξ| / (2λ)) 0 * cos (ξ T)`. -/
theorem integral_cos_mul_squaredSinc_sub (hell : 0 < ell) (ξ T : ℝ) :
    ∫ t : ℝ, cos (ξ * t) * squaredSinc ell (t - T) =
      max (1 - |ξ| / (2 * ell)) 0 * cos (ξ * T) := by
  rw [← integral_add_right_eq_self (fun t : ℝ ↦ cos (ξ * t) * squaredSinc ell (t - T)) T]
  have hsplit : (fun v : ℝ ↦ cos (ξ * (v + T)) * squaredSinc ell (v + T - T)) =
      fun v ↦ cos (ξ * T) * (squaredSinc ell v * cos (ξ * v)) -
        sin (ξ * T) * (squaredSinc ell v * sin (ξ * v)) := funext fun v ↦ by
    rw [add_sub_cancel_right, mul_add, cos_add]
    ring
  have hint_cos : Integrable (fun v : ℝ ↦ squaredSinc ell v * cos (ξ * v)) :=
    (integrable_squaredSinc ell).mul_bdd
      (by fun_prop : Continuous fun v ↦ cos (ξ * v)).aestronglyMeasurable
      (Eventually.of_forall fun _ ↦ abs_cos_le_one _)
  have hint_sin : Integrable (fun v : ℝ ↦ squaredSinc ell v * sin (ξ * v)) :=
    (integrable_squaredSinc ell).mul_bdd
      (by fun_prop : Continuous fun v ↦ sin (ξ * v)).aestronglyMeasurable
      (Eventually.of_forall fun _ ↦ abs_sin_le_one _)
  have hodd : ∫ v : ℝ, squaredSinc ell v * sin (ξ * v) = 0 :=
    MeasureTheory.integral_eq_zero_of_odd (Eventually.of_forall fun v ↦ by
      rw [squaredSinc_neg_right, mul_neg, sin_neg, mul_neg])
  rw [hsplit, integral_sub (hint_cos.const_mul _) (hint_sin.const_mul _), integral_const_mul,
    integral_const_mul, integral_squaredSinc_mul_cos hell ξ, hodd]
  ring

/-- **Band-limit cancellation.** For `λ ≥ 0` and `2λ ≤ |ξ|`, the convolution of `t ↦ cos (ξ t)`
with `squaredSinc λ` vanishes at every shift `T`. -/
theorem integral_cos_mul_squaredSinc_eq_zero {ξ : ℝ} (hell : 0 ≤ ell)
    (hξ : 2 * ell ≤ |ξ|) (T : ℝ) :
    ∫ t : ℝ, cos (ξ * t) * squaredSinc ell (t - T) = 0 := by
  rcases hell.eq_or_lt with rfl | hell
  · simp
  rw [integral_cos_mul_squaredSinc_sub hell ξ T,
    max_eq_right (sub_nonpos.mpr ((one_le_div (by positivity)).mpr hξ)), zero_mul]

end TauCeti.HigherPoleTauberian
