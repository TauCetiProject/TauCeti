/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.NumberTheory.LSeries.Lerch.Differential
public import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Principal integral representation of the Lerch transcendent

For `0 < Re s`, `1 - z ∈ Complex.slitPlane` (`z ∈ ℂ \ [1, ∞)`), and `0 < Re c`, the Laplace-Mellin
integral `lerchIntegral (s, z, c) = Γ(s)⁻¹ * ∫ t in Ioi 0, t ^ (s - 1) * exp (-(c * t)) /
(1 - z * exp (-t))` converges absolutely and defines a jointly analytic function of `(s, z, c)`
extending `TauCeti.lerchSeries z s c` from `‖z‖ < 1` across `ℂ \ [1, ∞)`.

## Main declarations

* `TauCeti.lerchIntegral`, `TauCeti.exists_le_norm_one_sub_mul_exp_neg`,
  `TauCeti.integrableOn_lerchIntegrand`: Gamma-normalized integral representation, uniform cut-plane
  denominator bound, and integrability on `(0, ∞)`.
* `TauCeti.analyticOnNhd_lerchIntegral`, `TauCeti.differentiableOn_lerchIntegral`: joint analyticity
  and holomorphy on `{p | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}`.
* `TauCeti.lerchIntegral_eq_lerchSeries`, `TauCeti.lerchIntegral_eq_cpow_add_mul_add_one`,
  `TauCeti.mul_lerchIntegral_one_one_eq_polylog_one`: agreement with `lerchSeries` on `‖z‖ < 1`,
  `c`-shift identity, and `z * lerchIntegral (1, z, 1) = Li_1(z)` on `1 - z ∈ Complex.slitPlane`.

## References

* [A. Erdélyi et al., *Higher Transcendental Functions*, Vol. 1][erdelyi1953vol1], Chapter 1.11,
  (3).
* [J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function I. Zeta integrals*][lagariasli2012].
-/

public section

open Filter Function MeasureTheory Metric Set Topology

namespace TauCeti

/-- Principal Gamma-normalized integral representation of the Lerch transcendent in coordinates
`p = (s, z, c) : ℂ × ℂ × ℂ`. -/
noncomputable def lerchIntegral (p : ℂ × ℂ × ℂ) : ℂ :=
  (Complex.Gamma p.1)⁻¹ * ∫ t : ℝ in Ioi 0,
    (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t))

/-- Defining Laplace-Mellin integral formula for `lerchIntegral`. -/
theorem lerchIntegral_def (p : ℂ × ℂ × ℂ) :
    lerchIntegral p = (Complex.Gamma p.1)⁻¹ * ∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t)) := by rfl

/-! ### Cut-domain denominator bounds and integrability -/

/-- On a compact subset `K` of `{z : ℂ | 1 - z ∈ Complex.slitPlane}`, the denominator
`1 - z * exp (-t)` is bounded away from zero uniformly for all `t ≥ 0`. -/
theorem exists_le_norm_one_sub_mul_exp_neg {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane}) :
    ∃ δ > 0, ∀ z ∈ K, ∀ t ≥ (0 : ℝ), δ ≤ ‖1 - z * Complex.exp (-t)‖ := by
  obtain ⟨δ, hδ, h⟩ := Polylog.exists_le_norm_one_sub_ofReal_mul hK hKΩ
  refine ⟨δ, hδ, fun z hz t ht => ?_⟩
  simpa [Complex.ofReal_exp, mul_comm z] using
    h z hz (Real.exp (-t)) ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩

private theorem one_sub_mul_exp_neg_ne_zero {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) {t : ℝ}
    (ht : 0 ≤ t) : 1 - z * Complex.exp (-t) ≠ 0 := by
  obtain ⟨δ, hδ, hd⟩ := exists_le_norm_one_sub_mul_exp_neg (isCompact_singleton (x := z))
    (singleton_subset_iff.mpr hz)
  exact norm_pos_iff.mp (hδ.trans_le (hd z rfl t ht))

private theorem exists_integrableOn_Ioi_lerchMajorant {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    (hKΩ : K ⊆ {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re})
    (k pow_denom : ℕ) (shift_s shift_c : ℝ)
    (hs_shift : ∀ p ∈ K, -1 < p.1.re + shift_s) (hc_shift : ∀ p ∈ K, 0 < p.2.2.re + shift_c) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ p ∈ K, ∀ t > (0 : ℝ),
        ‖(t : ℂ) ^ (p.1 + shift_s) * (Complex.log t) ^ k *
          Complex.exp (-((p.2.2 + shift_c) * t))‖ /
            ‖1 - p.2.1 * Complex.exp (-t)‖ ^ pow_denom ≤ g t := by
  obtain ⟨δ, hδ, hden⟩ := exists_le_norm_one_sub_mul_exp_neg
    (hK.image (continuous_fst.comp continuous_snd)) (by rintro _ ⟨p, hp, rfl⟩; exact (hKΩ hp).2.1)
  obtain ⟨g₀, hg₀, hnum⟩ :=
    Complex.exists_integrableOn_Ioi_norm_cpow_mul_log_pow_mul_exp_neg_mul_le
      (hK.image (by fun_prop : Continuous fun p : ℂ × ℂ × ℂ =>
        (p.1 + (shift_s : ℂ), p.2.2 + (shift_c : ℂ))))
      (by rintro _ ⟨p, hp, rfl⟩; simpa using hs_shift p hp)
      (by rintro _ ⟨p, hp, rfl⟩; simpa using hc_shift p hp) k
  refine ⟨fun t => (δ ^ pow_denom)⁻¹ * g₀ t, hg₀.const_mul _, fun p hp t ht => ?_⟩
  have hd := pow_le_pow_left₀ hδ.le (hden p.2.1 ⟨p, hp, rfl⟩ t ht.le) pow_denom
  have hn := hnum (p.1 + shift_s, p.2.2 + shift_c) ⟨p, hp, rfl⟩ t ht
  have : 0 ≤ g₀ t := (norm_nonneg _).trans hn
  rw [div_eq_mul_inv, mul_comm _ (‖1 - p.2.1 * Complex.exp (-t)‖ ^ pow_denom)⁻¹]
  exact mul_le_mul (inv_anti₀ (pow_pos hδ _) hd) hn (norm_nonneg _) (by positivity)

/-- For `0 < Re s`, `1 - z ∈ Complex.slitPlane`, and `0 < Re c`, the Lerch integrand is integrable
on `(0, ∞)`. -/
theorem integrableOn_lerchIntegrand {p : ℂ × ℂ × ℂ} (hs : 0 < p.1.re)
    (hz : 1 - p.2.1 ∈ Complex.slitPlane) (hc : 0 < p.2.2.re) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) /
        (1 - p.2.1 * Complex.exp (-t))) (Ioi 0) := by
  obtain ⟨g, hg, hle⟩ := exists_integrableOn_Ioi_lerchMajorant (isCompact_singleton (x := p))
    (singleton_subset_iff.mpr ⟨hs, hz, hc⟩) 0 1 (-1) 0 (by simp [hs]) (by simp [hc])
  refine hg.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa [sub_eq_add_neg, norm_div] using hle p rfl t ht

/-! ### Joint analyticity on the cut domain -/

private theorem isOpen_lerchIntegralDomain :
    IsOpen {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} :=
  (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter <|
    (Complex.isOpen_slitPlane.preimage
      (continuous_const.sub (continuous_fst.comp continuous_snd))).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_snd.comp continuous_snd)))

private theorem continuousOn_rawLerchIntegral :
    ContinuousOn
      (fun p : ℂ × ℂ × ℂ => ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t)))
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} := by
  rw [isOpen_lerchIntegralDomain.continuousOn_iff]
  intro p₀ hp₀
  obtain ⟨r, hr, hcb⟩ := (isCompact_singleton (x := p₀)).exists_cthickening_subset_open
    isOpen_lerchIntegralDomain (singleton_subset_iff.mpr hp₀)
  have hsub : closedBall p₀ r ⊆
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} := by
    simpa [cthickening_singleton _ hr.le] using hcb
  obtain ⟨g, hg, hle⟩ := exists_integrableOn_Ioi_lerchMajorant (isCompact_closedBall p₀ r) hsub
    0 1 (-1) 0 (fun p hp => by linarith [(hsub hp).1]) (fun p hp => by simpa using (hsub hp).2.2)
  refine MeasureTheory.continuousAt_of_dominated
    (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop)) ?_ hg ?_
  · filter_upwards [closedBall_mem_nhds p₀ hr] with p hp
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa [sub_eq_add_neg, norm_div] using hle p hp t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (((ContinuousAt.const_cpow (by fun_prop)
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)))).mul (by fun_prop)).div
      (by fun_prop) (one_sub_mul_exp_neg_ne_zero hp₀.2.1 ht.le))

private theorem differentiableAt_rawLerchIntegral_first {p₀ : ℂ × ℂ × ℂ}
    (hp₀ : 0 < p₀.1.re ∧ 1 - p₀.2.1 ∈ Complex.slitPlane ∧ 0 < p₀.2.2.re) :
    DifferentiableAt ℂ
      (fun s : ℂ => ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (s - 1) * Complex.exp (-(p₀.2.2 * t)) / (1 - p₀.2.1 * Complex.exp (-t)))
      p₀.1 := by
  set r : ℝ := p₀.1.re / 2 with hr_def
  have hr : 0 < r := half_pos hp₀.1
  have hK : IsCompact ((fun s : ℂ => (s, p₀.2.1, p₀.2.2)) '' closedBall p₀.1 r) :=
    (isCompact_closedBall p₀.1 r).image (by fun_prop)
  have hKΩ : ((fun s : ℂ => (s, p₀.2.1, p₀.2.2)) '' closedBall p₀.1 r) ⊆
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} := by
    rintro _ ⟨s, hs, rfl⟩
    have habs := (Complex.abs_re_le_norm (s - p₀.1)).trans (mem_closedBall_iff_norm.mp hs)
    rw [Complex.sub_re] at habs
    exact ⟨by linarith [hr_def, hp₀.1, (abs_le.mp habs).1], hp₀.2.1, hp₀.2.2⟩
  obtain ⟨g, hg, hle⟩ := exists_integrableOn_Ioi_lerchMajorant hK hKΩ 1 1 (-1) 0
    (fun p hp => by linarith [(hKΩ hp).1]) (fun p hp => by simpa using (hKΩ hp).2.2)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun s (t : ℝ) => (t : ℂ) ^ (s - 1) * Complex.exp (-(p₀.2.2 * t)) /
      (1 - p₀.2.1 * Complex.exp (-t)))
    (F' := fun s (t : ℝ) => (t : ℂ) ^ (s - 1) * Complex.log t * Complex.exp (-(p₀.2.2 * t)) /
      (1 - p₀.2.1 * Complex.exp (-t))) (bound := g) (closedBall_mem_nhds p₀.1 hr)
    (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_lerchIntegrand hp₀.1 hp₀.2.1 hp₀.2.2)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hg ?_).2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    simpa [sub_eq_add_neg, norm_div] using hle (s, p₀.2.1, p₀.2.2) ⟨s, hs, rfl⟩ t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _
    have hd : HasDerivAt (fun s : ℂ => (t : ℂ) ^ (s - 1)) ((t : ℂ) ^ (s - 1) * Complex.log t) s :=
      by simpa using (((hasDerivAt_id s).sub_const 1).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))))
    simpa [mul_div_assoc, mul_assoc] using
      hd.mul_const (Complex.exp (-(p₀.2.2 * t)) / (1 - p₀.2.1 * Complex.exp (-t)))

private theorem differentiableAt_rawLerchIntegral_second {p₀ : ℂ × ℂ × ℂ}
    (hp₀ : 0 < p₀.1.re ∧ 1 - p₀.2.1 ∈ Complex.slitPlane ∧ 0 < p₀.2.2.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (p₀.1 - 1) * Complex.exp (-(p₀.2.2 * t)) / (1 - z * Complex.exp (-t)))
      p₀.2.1 := by
  have hΩo : IsOpen {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)
  obtain ⟨r, hr, hcb⟩ := (isCompact_singleton (x := p₀.2.1)).exists_cthickening_subset_open hΩo
    (singleton_subset_iff.mpr hp₀.2.1)
  have hsub : closedBall p₀.2.1 r ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane} := by
    simpa [cthickening_singleton _ hr.le] using hcb
  have hK : IsCompact ((fun z : ℂ => (p₀.1, z, p₀.2.2)) '' closedBall p₀.2.1 r) :=
    (isCompact_closedBall p₀.2.1 r).image (by fun_prop)
  have hKΩ : ((fun z : ℂ => (p₀.1, z, p₀.2.2)) '' closedBall p₀.2.1 r) ⊆
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} := by
    rintro _ ⟨z, hz, rfl⟩; exact ⟨hp₀.1, hsub hz, hp₀.2.2⟩
  obtain ⟨g, hg, hle⟩ := exists_integrableOn_Ioi_lerchMajorant hK hKΩ 0 2 (-1) 1
    (fun p hp => by linarith [(hKΩ hp).1]) (fun p hp => by linarith [(hKΩ hp).2.2])
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun z (t : ℝ) => (t : ℂ) ^ (p₀.1 - 1) * Complex.exp (-(p₀.2.2 * t)) /
      (1 - z * Complex.exp (-t)))
    (F' := fun z (t : ℝ) => (t : ℂ) ^ (p₀.1 - 1) * Complex.exp (-((p₀.2.2 + 1) * t)) /
      (1 - z * Complex.exp (-t)) ^ 2) (bound := g) (closedBall_mem_nhds p₀.2.1 hr)
    (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_lerchIntegrand hp₀.1 hp₀.2.1 hp₀.2.2)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hg ?_).2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    simpa [sub_eq_add_neg, norm_div] using hle (p₀.1, z, p₀.2.2) ⟨z, hz, rfl⟩ t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    have hden := one_sub_mul_exp_neg_ne_zero (hsub hz) ht.le
    have hd := ((hasDerivAt_const z (1 : ℂ)).sub
      ((hasDerivAt_id z).mul_const (Complex.exp (-t)))).inv hden
    convert hd.const_mul ((t : ℂ) ^ (p₀.1 - 1) * Complex.exp (-(p₀.2.2 * t))) using 1
    · ext w; simp [div_eq_mul_inv]
    · dsimp only [Pi.sub_apply, id_eq]
      rw [show -((p₀.2.2 + 1) * (t : ℂ)) = -(p₀.2.2 * t) + (-(t : ℂ)) by ring, Complex.exp_add]
      field_simp; ring

private theorem differentiableAt_rawLerchIntegral_third {p₀ : ℂ × ℂ × ℂ}
    (hp₀ : 0 < p₀.1.re ∧ 1 - p₀.2.1 ∈ Complex.slitPlane ∧ 0 < p₀.2.2.re) :
    DifferentiableAt ℂ
      (fun c : ℂ => ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (p₀.1 - 1) * Complex.exp (-(c * t)) / (1 - p₀.2.1 * Complex.exp (-t)))
      p₀.2.2 := by
  set r : ℝ := p₀.2.2.re / 2 with hr_def
  have hr : 0 < r := half_pos hp₀.2.2
  have hK : IsCompact ((fun c : ℂ => (p₀.1, p₀.2.1, c)) '' closedBall p₀.2.2 r) :=
    (isCompact_closedBall p₀.2.2 r).image (by fun_prop)
  have hKΩ : ((fun c : ℂ => (p₀.1, p₀.2.1, c)) '' closedBall p₀.2.2 r) ⊆
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} := by
    rintro _ ⟨c, hc, rfl⟩
    have habs := (Complex.abs_re_le_norm (c - p₀.2.2)).trans (mem_closedBall_iff_norm.mp hc)
    rw [Complex.sub_re] at habs
    exact ⟨hp₀.1, hp₀.2.1, by linarith [hr_def, hp₀.2.2, (abs_le.mp habs).1]⟩
  obtain ⟨g, hg, hle⟩ := exists_integrableOn_Ioi_lerchMajorant hK hKΩ 0 1 0 0
    (fun p hp => by linarith [(hKΩ hp).1]) (fun p hp => by simpa using (hKΩ hp).2.2)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun c (t : ℝ) => (t : ℂ) ^ (p₀.1 - 1) * Complex.exp (-(c * t)) /
      (1 - p₀.2.1 * Complex.exp (-t)))
    (F' := fun c (t : ℝ) => -((t : ℂ) ^ p₀.1 * Complex.exp (-(c * t)) /
      (1 - p₀.2.1 * Complex.exp (-t)))) (bound := g) (closedBall_mem_nhds p₀.2.2 hr)
    (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_lerchIntegrand hp₀.1 hp₀.2.1 hp₀.2.2)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hg ?_).2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht c hc
    simpa [norm_div] using hle (p₀.1, p₀.2.1, c) ⟨c, hc, rfl⟩ t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht c _
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have hd : HasDerivAt (fun c : ℂ => Complex.exp (-(c * t)))
        (-(t : ℂ) * Complex.exp (-(c * t))) c := by
      simpa [mul_comm] using (((hasDerivAt_id c).mul_const (t : ℂ)).neg).cexp
    have hpow : (t : ℂ) ^ (p₀.1 - 1) * (t : ℂ) = (t : ℂ) ^ p₀.1 := by
      simpa [sub_add_cancel] using (Complex.cpow_add (p₀.1 - 1) 1 ht0).symm
    convert (hd.const_mul ((t : ℂ) ^ (p₀.1 - 1))).div_const
      (1 - p₀.2.1 * Complex.exp (-t)) using 1
    rw [show (t : ℂ) ^ (p₀.1 - 1) * (-(t : ℂ) * Complex.exp (-(c * t))) =
      -(((t : ℂ) ^ (p₀.1 - 1) * (t : ℂ)) * Complex.exp (-(c * t))) by ring, hpow, neg_div]

/-- The principal Lerch integral `lerchIntegral` is jointly analytic on
`{p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}`. -/
theorem analyticOnNhd_lerchIntegral :
    AnalyticOnNhd ℂ lerchIntegral
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} := by
  set U : Set (ℂ × ℂ × ℂ) := {p | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}
  let raw : ℂ × ℂ × ℂ → ℂ := fun p => ∫ t : ℝ in Ioi 0,
    (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t))
  let e : (Fin 3 → ℂ) ≃L[ℂ] ℂ × ℂ × ℂ :=
    { toFun := fun v => (v 0, v 1, v 2), invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := fun v => by ext i; fin_cases i <;> rfl
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := continuous_pi fun i => by fin_cases i <;> fun_prop }
  have hraw_an : AnalyticOnNhd ℂ (raw ∘ e) (e ⁻¹' U) := by
    refine ContinuousOn.analyticOnNhd_of_differentiableAt_update
      (continuousOn_rawLerchIntegral.comp e.continuous.continuousOn (mapsTo_preimage _ _))
      (isOpen_lerchIntegralDomain.preimage e.continuous) fun v hv i => ?_
    have hv' : 0 < (v 0).re ∧ 1 - v 1 ∈ Complex.slitPlane ∧ 0 < (v 2).re := hv
    fin_cases i
    · change DifferentiableAt ℂ (fun s => raw (update v 0 s 0, update v 0 s 1, update v 0 s 2))
        (v 0)
      simpa [raw] using differentiableAt_rawLerchIntegral_first (p₀ := (v 0, v 1, v 2)) hv'
    · change DifferentiableAt ℂ (fun z => raw (update v 1 z 0, update v 1 z 1, update v 1 z 2))
        (v 1)
      simpa [raw] using differentiableAt_rawLerchIntegral_second (p₀ := (v 0, v 1, v 2)) hv'
    · change DifferentiableAt ℂ (fun c => raw (update v 2 c 0, update v 2 c 1, update v 2 c 2))
        (v 2)
      simpa [raw] using differentiableAt_rawLerchIntegral_third (p₀ := (v 0, v 1, v 2)) hv'
  have hraw_diff : DifferentiableOn ℂ raw U := fun p hp =>
    ((hraw_an (e.symm p) (by simpa using hp)).comp
      (e.symm.analyticAt p)).differentiableAt.differentiableWithinAt
  have hG_diff : DifferentiableOn ℂ (fun p : ℂ × ℂ × ℂ => (Complex.Gamma p.1)⁻¹) U :=
    fun p hp => by
      have hs0 : ∀ m : ℕ, p.1 ≠ -(m : ℂ) := fun m h => by
        have hre := congrArg Complex.re h; simp only [Complex.neg_re, Complex.natCast_re] at hre
        linarith [hp.1, Nat.cast_nonneg (α := ℝ) m]
      exact (((Complex.differentiableAt_Gamma p.1 hs0).comp p differentiableAt_fst).inv
        (Complex.Gamma_ne_zero_of_re_pos hp.1)).differentiableWithinAt
  exact DifferentiableOn.analyticOnNhd_of_finiteDimensional
    ((hG_diff.mul hraw_diff).congr fun p _ => lerchIntegral_def p) isOpen_lerchIntegralDomain

/-- `lerchIntegral` is jointly complex differentiable on
`{p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}`. -/
theorem differentiableOn_lerchIntegral :
    DifferentiableOn ℂ lerchIntegral
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} :=
  analyticOnNhd_lerchIntegral.differentiableOn

/-! ### Agreement with `lerchSeries` on the open unit disc and principal-sheet identities -/

private theorem natCast_add_re_pos (n : ℕ) {c : ℂ} (hc : 0 < c.re) : 0 < ((n : ℂ) + c).re := by
  simp only [Complex.add_re, Complex.natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem summable_integral_norm_lerchTerm {s z c : ℂ} (hs : 0 < s.re) (hz : ‖z‖ < 1)
    (hc : 0 < c.re) :
    Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0,
      ‖z ^ n * ((t : ℂ) ^ (s - 1) * Complex.exp (-(((n : ℂ) + c) * t)))‖) := by
  let g₀ : ℝ → ℝ := fun t => ‖(t : ℂ) ^ (s - 1) * Complex.exp (-(c * t))‖
  have hg₀ : Integrable g₀ (volume.restrict (Ioi 0)) :=
    (Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs hc).norm
  refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right (∫ t : ℝ in Ioi 0, g₀ t))
  rw [← integral_const_mul]
  refine integral_mono_ae
    ((Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs (natCast_add_re_pos n hc)).const_mul
      (z ^ n)).norm (hg₀.const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hexp : Real.exp (-(n : ℝ) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hsplit : Complex.exp (-(((n : ℂ) + c) * t)) =
      Complex.exp (-((n : ℂ) * t)) * Complex.exp (-(c * t)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hn_exp : ‖Complex.exp (-((n : ℂ) * t))‖ = Real.exp (-(n : ℝ) * t) := by
    rw [Complex.norm_exp]; simp [neg_mul]
  dsimp only [g₀]
  rw [hsplit, ← mul_assoc ((t : ℂ) ^ (s - 1)), mul_comm ((t : ℂ) ^ (s - 1)), mul_assoc,
    norm_mul, norm_pow, norm_mul, hn_exp]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hexp) (by positivity)

/-- On the open unit disc `‖z‖ < 1` with `0 < Re s` and `0 < Re c`, `lerchIntegral (s, z, c)`
agrees with `lerchSeries z s c`. -/
theorem lerchIntegral_eq_lerchSeries {s z c : ℂ} (hs : 0 < s.re) (hz : ‖z‖ < 1) (hc : 0 < c.re) :
    lerchIntegral (s, z, c) = lerchSeries z s c := by
  let F : ℕ → ℝ → ℂ := fun n t =>
    z ^ n * ((t : ℂ) ^ (s - 1) * Complex.exp (-(((n : ℂ) + c) * t)))
  have hF_int (n : ℕ) : Integrable (F n) (volume.restrict (Ioi 0)) :=
    (Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs (natCast_add_re_pos n hc)).const_mul (z ^ n)
  have hsum := hasSum_integral_of_summable_integral_norm hF_int
    (summable_integral_norm_lerchTerm hs hz hc)
  have htsum_eq : ∫ t : ℝ in Ioi 0, (∑' n, F n t) =
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-(c * t)) / (1 - z * Complex.exp (-t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      have ht0 : 0 < t := ht
      have hzw : ‖z * Complex.exp (-t)‖ < 1 := by
        rw [norm_mul, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
        exact (mul_le_of_le_one_right (norm_nonneg z)
          (Real.exp_le_one_iff.mpr (by linarith))).trans_lt hz
      have hterm (n : ℕ) : F n t =
          ((t : ℂ) ^ (s - 1) * Complex.exp (-(c * t))) * (z * Complex.exp (-t)) ^ n := by
        dsimp only [F]
        rw [mul_pow, ← Complex.exp_nat_mul,
          show -(((n : ℂ) + c) * (t : ℂ)) = -(c * t) + (n : ℂ) * (-(t : ℂ)) by ring,
          Complex.exp_add]
        ring
      simp_rw [hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hzw, div_eq_mul_inv]
  have hterm_int (n : ℕ) : ∫ t : ℝ in Ioi 0, F n t =
      Complex.Gamma s * (z ^ n * Complex.exp (-s * Complex.log (n + c))) := by
    dsimp only [F]
    rw [integral_const_mul,
      Complex.integral_cpow_mul_exp_neg_mul_Ioi_eq_Gamma_mul_exp hs (natCast_add_re_pos n hc)]
    ring
  rw [lerchIntegral_def, ← htsum_eq, ← hsum.tsum_eq]
  simp_rw [hterm_int, tsum_mul_left, ← lerchSeries_def]
  exact inv_mul_cancel_left₀ (Complex.Gamma_ne_zero_of_re_pos hs) _

/-- Parameter shift `lerchIntegral (s, z, c) = exp (-s * log c) + z * lerchIntegral (s, z, c + 1)`
across the entire cut domain `0 < Re s`, `1 - z ∈ Complex.slitPlane`, `0 < Re c`. -/
theorem lerchIntegral_eq_cpow_add_mul_add_one {s z c : ℂ} (hs : 0 < s.re)
    (hz : 1 - z ∈ Complex.slitPlane) (hc : 0 < c.re) :
    lerchIntegral (s, z, c) =
      Complex.exp (-s * Complex.log c) + z * lerchIntegral (s, z, c + 1) := by
  have hc1 : 0 < (c + 1).re := by simp; linarith
  have hi1 := Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs hc
  have hi2 := (integrableOn_lerchIntegrand (p := (s, z, c + 1)) hs hz hc1).const_mul z
  have hcongr : ∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (s - 1) * Complex.exp (-(c * t)) / (1 - z * Complex.exp (-t)) =
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-(c * t))) +
        ∫ t : ℝ in Ioi 0, z * ((t : ℂ) ^ (s - 1) * Complex.exp (-((c + 1) * t)) /
          (1 - z * Complex.exp (-t))) := by
    rw [← integral_add hi1 hi2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hden := one_sub_mul_exp_neg_ne_zero hz (le_of_lt ht)
    rw [show -((c + 1) * (t : ℂ)) = -(c * t) + (-(t : ℂ)) by ring, Complex.exp_add]
    field_simp; ring
  rw [lerchIntegral_def (s, z, c), lerchIntegral_def (s, z, c + 1), hcongr,
    Complex.integral_cpow_mul_exp_neg_mul_Ioi_eq_Gamma_mul_exp hs hc, integral_const_mul,
    mul_add, inv_mul_cancel_left₀ (Complex.Gamma_ne_zero_of_re_pos hs)]
  dsimp only; ring

/-- Across the cut plane `1 - z ∈ Complex.slitPlane`, `z * lerchIntegral (1, z, 1) = Li_1(z)`. -/
theorem mul_lerchIntegral_one_one_eq_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * lerchIntegral (1, z, 1) = Polylog.polylog 1 z := by
  let Ω : Set ℂ := {w : ℂ | 1 - w ∈ Complex.slitPlane}
  have hΩo : IsOpen Ω := Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)
  have hΩ_eq : Ω = (fun w : ℂ => 1 - w) '' Complex.slitPlane := by
    ext w; exact ⟨fun hw => ⟨1 - w, hw, sub_sub_cancel 1 w⟩,
      by rintro ⟨u, hu, rfl⟩; dsimp [Ω]; rwa [sub_sub_cancel]⟩
  have hΩ_pre : IsPreconnected Ω := by
    rw [hΩ_eq]
    exact (Complex.starConvex_one_slitPlane.isPathConnected Complex.one_mem_slitPlane).isConnected
      |>.isPreconnected.image _ (continuous_const.sub continuous_id).continuousOn
  have han1 : AnalyticOnNhd ℂ (fun w : ℂ => w * lerchIntegral (1, w, 1)) Ω :=
    DifferentiableOn.analyticOnNhd (fun w hw => by
      have hd := (differentiableOn_lerchIntegral (1, w, 1)
        ⟨by norm_num, hw, by norm_num⟩).differentiableAt
        (isOpen_lerchIntegralDomain.mem_nhds ⟨by norm_num, hw, by norm_num⟩)
      exact (((hasDerivAt_id w).mul (hd.hasFDerivAt.comp_hasDerivAt w
        ((hasDerivAt_const w (1 : ℂ)).prodMk ((hasDerivAt_id w).prodMk
          (hasDerivAt_const w (1 : ℂ)))))).congr_of_eventuallyEq
        (Eventually.of_forall fun _ => rfl)).differentiableAt.differentiableWithinAt) hΩo
  have han2 : AnalyticOnNhd ℂ (Polylog.polylog 1) Ω :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      ((((Complex.hasDerivAt_log hw).comp w ((hasDerivAt_const w (1 : ℂ)).sub
        (hasDerivAt_id w))).neg).congr_of_eventuallyEq
        (Eventually.of_forall Polylog.polylog_one)).differentiableAt.differentiableWithinAt) hΩo
  have hev : (fun w : ℂ => w * lerchIntegral (1, w, 1)) =ᶠ[𝓝 (0 : ℂ)] Polylog.polylog 1 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    rw [lerchIntegral_eq_lerchSeries one_pos hw1 one_pos, polylog_one_eq_mul_lerchSeries hw1]
  exact han1.eqOn_of_preconnected_of_eventuallyEq han2 hΩ_pre (by simp [Ω]) hev hz

end TauCeti
