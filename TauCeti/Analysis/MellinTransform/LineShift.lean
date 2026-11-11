/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Contour.Residue.VerticalLineShift
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Shifting the line of Mellin inversion (DLMF 2.5.6–2.5.7)

Let `G` be holomorphic on a neighbourhood of the closed strip `d ≤ Re z ≤ c` except at finitely
many poles in the open strip, integrable on both boundary lines, and with `G(σ + iT) → 0` as
`|T| → ∞` uniformly for `σ ∈ [d, c]`. Then, for `x > 0`,

`(2πi)⁻¹ ∫_{(c)} x^{-z} G(z) dz = ∑ Res(x^{-z} G(z)) + (2πi)⁻¹ ∫_{(d)} x^{-z} G(z) dz`,

in Mathlib's notation `mellinInv c G x = ∑_p Res(x^{-·} G, p) + mellinInv d G x`. By the
Riemann–Lebesgue lemma the remaining integral is `o(x^{-d})` as `x → 0+`, and likewise
`mellinInv c G x = o(x^{-c})` as `x → +∞`, which is the estimate after a shift to the right.

## Main results

* `TauCeti.mellinInv_eq_sum_residue_add`: the shift of the line of Mellin inversion.
* `TauCeti.mellinInv_isLittleO_nhdsGT_zero`, `TauCeti.mellinInv_isLittleO_atTop`: the
  remainder estimates, both from `TauCeti.mellinInv_isLittleO_of_tendsto_log`.
-/

@[expose] public section

open Complex Set Filter MeasureTheory Asymptotics
open scoped Topology Real FourierTransform Interval

namespace TauCeti

/-- The integrand of `mellinInv σ G x` as a Fourier integrand in `y`, at frequency
`log x / (2π)`. -/
private lemma cpow_neg_smul_eq_fourierChar {σ x : ℝ} (hx : 0 < x) (G : ℂ → ℂ) (y : ℝ) :
    (x : ℂ) ^ (-((σ : ℂ) + y * I)) • G (σ + y * I) =
      ((x ^ (-σ) : ℝ) : ℂ) * ((Real.fourierChar (-(y * (Real.log x / (2 * π)))) : ℂ) *
        G (σ + y * I)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [smul_eq_mul, cpow_def_of_ne_zero hx0, Real.rpow_def_of_pos hx, Real.fourierChar_apply,
    ← ofReal_log hx.le]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring

/-- **The remainder estimate.** Along any filter on which `x > 0` eventually and `log x` leaves
every compact set, `mellinInv σ G x = o(x^{-σ})`, by the Riemann–Lebesgue lemma. No hypothesis on
`G` is needed: if `G` is not integrable on the line `Re z = σ`, both sides are `0` in Mathlib's
convention for the Bochner integral. -/
theorem mellinInv_isLittleO_of_tendsto_log (G : ℂ → ℂ) (σ : ℝ) {l : Filter ℝ}
    (hpos : ∀ᶠ x in l, 0 < x) (hlog : Tendsto Real.log l (cocompact ℝ)) :
    (fun x => mellinInv σ G x) =o[l] fun x => ((x ^ (-σ) : ℝ) : ℂ) := by
  set u : ℝ → ℂ := fun x => (1 / (2 * π) : ℝ) •
    ∫ y : ℝ, Real.fourierChar (-(y * (Real.log x / (2 * π)))) • G (σ + y * I)
  have hu : Tendsto u l (𝓝 0) := by
    have hRL := Real.tendsto_integral_exp_smul_cocompact (fun y : ℝ => G (σ + y * I))
    have hfreq : Tendsto (fun x : ℝ => Real.log x / (2 * π)) l (cocompact ℝ) :=
      (Homeomorph.mulRight₀ (2 * π)⁻¹ (by positivity)).toCocompactMap.cocompact_tendsto'.comp
        hlog |>.congr fun x => by simp [div_eq_mul_inv]
    have := (hRL.comp hfreq).const_smul (1 / (2 * π) : ℝ)
    simpa [u] using this
  have heq : (fun x => mellinInv σ G x) =ᶠ[l] fun x => ((x ^ (-σ) : ℝ) : ℂ) * u x := by
    filter_upwards [hpos] with x hx
    simp only [mellinInv, u, cpow_neg_smul_eq_fourierChar hx, Circle.smul_def, smul_eq_mul]
    rw [integral_const_mul]
    simp only [Complex.real_smul]
    push_cast
    ring
  refine IsLittleO.congr' ?_ heq.symm EventuallyEq.rfl
  simpa using (isBigO_refl (fun x : ℝ => ((x ^ (-σ) : ℝ) : ℂ)) l).mul_isLittleO
    ((isLittleO_one_iff ℂ).2 hu)

/-- DLMF 2.5.7: `mellinInv σ G x = o(x^{-σ})` as `x → 0+`. -/
theorem mellinInv_isLittleO_nhdsGT_zero (G : ℂ → ℂ) (σ : ℝ) :
    (fun x => mellinInv σ G x) =o[𝓝[>] 0] fun x => ((x ^ (-σ) : ℝ) : ℂ) :=
  mellinInv_isLittleO_of_tendsto_log G σ self_mem_nhdsWithin
    (Real.tendsto_log_nhdsGT_zero.mono_right atBot_le_cocompact)

/-- `mellinInv σ G x = o(x^{-σ})` as `x → +∞`, the estimate after a shift to the right. -/
theorem mellinInv_isLittleO_atTop (G : ℂ → ℂ) (σ : ℝ) :
    (fun x => mellinInv σ G x) =o[atTop] fun x => ((x ^ (-σ) : ℝ) : ℂ) :=
  mellinInv_isLittleO_of_tendsto_log G σ (eventually_gt_atTop 0)
    (Real.tendsto_log_atTop.mono_right atTop_le_cocompact)

/-- **DLMF 2.5.6: shifting the line of Mellin inversion.** Let `G` be holomorphic on an open
neighbourhood `U` of the closed strip `d ≤ Re z ≤ c` except at a finite set `P` of points of the
open strip, at which `G` is meromorphic, integrable on both lines, and with `G(σ + iT) → 0` as
`|T| → ∞` uniformly for `σ ∈ [d, c]`. Then for `x > 0`,
`mellinInv c G x = ∑_{p ∈ P} Res(x^{-·} G, p) + mellinInv d G x`. -/
theorem mellinInv_eq_sum_residue_add {G : ℂ → ℂ} {c d x : ℝ} (hdc : d < c) (hx : 0 < x)
    {U : Set ℂ} (hU : IsOpen U) (hstrip : {z : ℂ | d ≤ z.re ∧ z.re ≤ c} ⊆ U)
    (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hG : DifferentiableOn ℂ G (U \ (P : Set ℂ))) (hm : ∀ p ∈ P, MeromorphicAt G p)
    (hc : Integrable fun y : ℝ => G (c + y * I)) (hd : Integrable fun y : ℝ => G (d + y * I))
    (hdecay : Tendsto (fun q : ℝ × ℝ => G (q.2 + q.1 * I)) (cocompact ℝ ×ˢ 𝓟 (Icc d c))
      (𝓝 0)) :
    mellinInv c G x =
      ∑ p ∈ P, Contour.residue (fun z => (x : ℂ) ^ (-z) * G z) p + mellinInv d G x := by
  set F : ℂ → ℂ := fun z => (x : ℂ) ^ (-z) * G z with hFdef
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpow (z : ℂ) : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ (-z)) z :=
    analyticAt_const.cpow analyticAt_id.neg (ofReal_mem_slitPlane.mpr hx)
  have hnorm (σ y : ℝ) : ‖(x : ℂ) ^ (-((σ : ℂ) + y * I))‖ = x ^ (-σ) := by
    rw [norm_cpow_eq_rpow_re_of_pos hx]; simp
  have hF : DifferentiableOn ℂ F (U \ (P : Set ℂ)) := fun z hz =>
    (hpow z).differentiableAt.differentiableWithinAt.mul (hG z hz)
  have hmF : ∀ p ∈ P, MeromorphicAt F p := fun p hp => (hpow p).meromorphicAt.mul (hm p hp)
  have hline {σ : ℝ} (hσ : Integrable fun y : ℝ => G (σ + y * I)) :
      Integrable fun y : ℝ => F (σ + y * I) := by
    refine (hσ.norm.const_mul (x ^ (-σ))).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (Continuous.aestronglyMeasurable (by fun_prop (disch := exact hx0))).mul
        hσ.aestronglyMeasurable
    · simp only [hFdef, norm_mul, hnorm]; rfl
  -- A bound for `x^{-σ}` on `[d, c]`.
  set X : ℝ := max (x ^ (-d)) (x ^ (-c)) + 1
  have hX0 : 0 < X := by positivity
  have hX (σ : ℝ) (hσ : σ ∈ Icc d c) : x ^ (-σ) ≤ X := by
    have : x ^ (-σ) ≤ max (x ^ (-d)) (x ^ (-c)) := by
      rcases le_total 1 x with h1 | h1
      · exact (Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hσ.1])).trans
          (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hx h1 (by linarith [hσ.2])).trans
          (le_max_right _ _)
    linarith
  have hhor : Tendsto (fun T : ℝ => ∫ σ in d..c, F (σ + T * I)) (cocompact ℝ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hδ : 0 < ε / (2 * X * (c - d)) := by
      have : 0 < c - d := sub_pos.mpr hdc
      positivity
    have h := Metric.tendsto_nhds.mp hdecay _ hδ
    rw [Filter.Eventually, mem_prod_principal] at h
    filter_upwards [h] with T hT
    rw [dist_zero_right]
    have hb : ∀ σ ∈ Ι d c, ‖F (σ + T * I)‖ ≤ X * (ε / (2 * X * (c - d))) := fun σ hσ => by
      rw [uIoc_of_le hdc.le] at hσ
      have hσ' : σ ∈ Icc d c := Ioc_subset_Icc_self hσ
      have hG' := hT σ hσ'
      rw [dist_zero_right] at hG'
      simp only [hFdef, norm_mul, hnorm]
      exact mul_le_mul (hX σ hσ') hG'.le (norm_nonneg _) hX0.le
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans_lt ?_
    rw [abs_of_pos (sub_pos.mpr hdc)]
    have hcd : 0 < c - d := sub_pos.mpr hdc
    field_simp
    linarith
  have hshift := Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue_of_meromorphicAt F hdc
    hU hstrip P hP hF hmF (hline hc) (hline hd) (hhor.mono_left atTop_le_cocompact)
    (hhor.mono_left atBot_le_cocompact)
  simp only [hFdef] at hshift
  have e : ((1 / (2 * π) : ℝ) : ℂ) * (2 * π) = 1 := by
    push_cast
    field_simp
  simp only [mellinInv, Complex.real_smul, smul_eq_mul]
  linear_combination ((1 / (2 * π) : ℝ) : ℂ) * hshift +
    (∑ p ∈ P, Contour.residue (fun z => (x : ℂ) ^ (-z) * G z) p) * e

end TauCeti
