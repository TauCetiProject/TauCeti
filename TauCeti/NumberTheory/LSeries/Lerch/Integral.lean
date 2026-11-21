/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.NumberTheory.LSeries.Lerch.Series
public import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate

import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.SlitPlane

/-!
# Principal integral representation of the Lerch transcendent

For `0 < Re s`, `1 - z ∈ Complex.slitPlane` (`z ∈ ℂ \ [1, ∞)`), and `0 < Re c`, the Laplace-Mellin
integral `lerchIntegral (s, z, c) = Γ(s)⁻¹ * ∫ t in Ioi 0, t ^ (s - 1) * exp (-(c * t)) /
(1 - z * exp (-t))` converges absolutely and defines a jointly analytic function of `(s, z, c)`
extending `TauCeti.lerchSeries z s c` from `‖z‖ < 1` across `ℂ \ [1, ∞)`.

## Main declarations

* `TauCeti.lerchIntegral`, `TauCeti.integrableOn_lerchIntegrand`: Gamma-normalized integral
  representation and integrability on `(0, ∞)`.
* `TauCeti.analyticOnNhd_lerchIntegral`, `TauCeti.differentiableOn_lerchIntegral`: joint analyticity
  and holomorphy on `{p | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}`.
* `TauCeti.lerchIntegral_eq_lerchSeries`, `TauCeti.lerchIntegral_eq_exp_add_mul_add_one_right`,
  `TauCeti.mul_deriv_lerchIntegral_middle_add_mul`: agreement with `lerchSeries` on `‖z‖ < 1`,
  `c`-shift identity, and lowering relation `(z ∂_z + c) lerchIntegral (s, z, c) =
  lerchIntegral (s - 1, z, c)` on `1 - z ∈ Complex.slitPlane`.

## References

* A. Erdélyi, W. Magnus, F. Oberhettinger, and F. G. Tricomi, *Higher Transcendental Functions*,
  Vol. 1, McGraw-Hill, 1953, Chapter 1.11, (3).
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  24 (2012), 49–84, §2 (2.2)–(2.4), §4 (4.18)–(4.23), (4.30)–(4.32).
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  arXiv:1506.06161, (1.8)–(1.9).
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

/-! ### Cut-domain integrability -/

private theorem exists_integrableOn_Ioi_lerchMajorant {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    (hKz : ∀ p ∈ K, 1 - p.2.1 ∈ Complex.slitPlane)
    (k pow_denom : ℕ) (shift_s shift_c : ℝ)
    (hs_shift : ∀ p ∈ K, -1 < p.1.re + shift_s) (hc_shift : ∀ p ∈ K, 0 < p.2.2.re + shift_c) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ p ∈ K, ∀ t > (0 : ℝ),
        ‖(t : ℂ) ^ (p.1 + shift_s) * (Complex.log t) ^ k *
          Complex.exp (-((p.2.2 + shift_c) * t))‖ /
            ‖1 - p.2.1 * Complex.exp (-t)‖ ^ pow_denom ≤ g t := by
  obtain ⟨δ, hδ, hden⟩ :=
    (hK.image (continuous_fst.comp continuous_snd)).exists_le_norm_one_sub_mul_exp_neg
      (by rintro _ ⟨p, hp, rfl⟩; exact hKz p hp)
  have hK' : IsCompact ((fun p : ℂ × ℂ × ℂ => (p.1 + (shift_s : ℂ), p.2.2 + (shift_c : ℂ))) '' K) :=
    hK.image (by fun_prop)
  obtain ⟨g₀, hg₀, hnum⟩ :=
    hK'.exists_integrableOn_Ioi_norm_cpow_mul_log_pow_mul_exp_neg_mul_le
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
    (by rintro _ rfl; exact hz) 0 1 (-1) 0 (by simp [hs]) (by simp [hc])
  refine hg.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa [sub_eq_add_neg, norm_div] using hle p rfl t ht

/-! ### Joint analyticity on the cut domain -/

private theorem isOpen_lerchIntegralDomain :
    IsOpen {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} :=
  (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter <|
    (Complex.isOpen_setOf_one_sub_mem_slitPlane.preimage
      (continuous_fst.comp continuous_snd)).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_snd.comp continuous_snd)))

private theorem continuousOn_rawLerchIntegral :
    ContinuousOn
      (fun p : ℂ × ℂ × ℂ => ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t)))
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} := by
  rw [isOpen_lerchIntegralDomain.continuousOn_iff]
  intro p₀ hp₀
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (isOpen_lerchIntegralDomain.mem_nhds hp₀)
  obtain ⟨g, hg, hle⟩ := exists_integrableOn_Ioi_lerchMajorant (isCompact_closedBall p₀ r)
    (fun p hp => (hsub hp).2.1) 0 1 (-1) 0 (fun p hp => by linarith [(hsub hp).1])
    (fun p hp => by simpa using (hsub hp).2.2)
  refine MeasureTheory.continuousAt_of_dominated
    (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop)) ?_ hg ?_
  · filter_upwards [closedBall_mem_nhds p₀ hr] with p hp
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa [sub_eq_add_neg, norm_div] using hle p hp t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (((ContinuousAt.const_cpow (by fun_prop)
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)))).mul (by fun_prop)).div
      (by fun_prop) (Complex.one_sub_mul_exp_neg_ne_zero hp₀.2.1 ht.le))

private theorem exp_neg_add_mul (c a : ℂ) (t : ℝ) :
    Complex.exp (-((c + a) * t)) = Complex.exp (-(c * t)) * Complex.exp (-(a * t)) := by
  rw [add_mul, neg_add, Complex.exp_add]

private theorem exp_neg_add_one_mul (c : ℂ) (t : ℝ) :
    Complex.exp (-((c + 1) * t)) = Complex.exp (-(c * t)) * Complex.exp (-(t : ℂ)) := by
  simpa using exp_neg_add_mul c 1 t

private theorem exp_neg_natCast_add_mul (n : ℕ) (c : ℂ) (t : ℝ) :
    Complex.exp (-(((n : ℂ) + c) * t)) =
      Complex.exp (-((n : ℂ) * t)) * Complex.exp (-(c * t)) := by
  rw [add_comm (n : ℂ) c, exp_neg_add_mul, mul_comm]

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
  obtain ⟨g, hg, hle⟩ := exists_integrableOn_Ioi_lerchMajorant hK
    (by rintro _ ⟨_, _, rfl⟩; exact hp₀.2.1) 1 1 (-1) 0
    (by
      rintro _ ⟨s, hs, rfl⟩
      have habs := (Complex.abs_re_le_norm (s - p₀.1)).trans (mem_closedBall_iff_norm.mp hs)
      rw [Complex.sub_re] at habs
      linarith [hr_def, hp₀.1, (abs_le.mp habs).1])
    (by rintro _ ⟨_, _, rfl⟩; simpa using hp₀.2.2)
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
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Complex.isOpen_setOf_one_sub_mem_slitPlane.mem_nhds hp₀.2.1)
  have hK : IsCompact ((fun z : ℂ => (p₀.1, z, p₀.2.2)) '' closedBall p₀.2.1 r) :=
    (isCompact_closedBall p₀.2.1 r).image (by fun_prop)
  obtain ⟨g, hg, hle⟩ := exists_integrableOn_Ioi_lerchMajorant hK
    (by rintro _ ⟨z, hz, rfl⟩; exact hsub hz) 0 2 (-1) 1
    (by rintro _ ⟨_, _, rfl⟩; linarith [hp₀.1]) (by rintro _ ⟨_, _, rfl⟩; linarith [hp₀.2.2])
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
    have hden := Complex.one_sub_mul_exp_neg_ne_zero (hsub hz) ht.le
    have hd := ((hasDerivAt_const z (1 : ℂ)).sub
      ((hasDerivAt_id z).mul_const (Complex.exp (-t)))).inv hden
    convert hd.const_mul ((t : ℂ) ^ (p₀.1 - 1) * Complex.exp (-(p₀.2.2 * t))) using 1
    · ext w; simp [div_eq_mul_inv]
    · dsimp only [Pi.sub_apply, id_eq]
      rw [exp_neg_add_one_mul]
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
  obtain ⟨g, hg, hle⟩ := exists_integrableOn_Ioi_lerchMajorant hK
    (by rintro _ ⟨_, _, rfl⟩; exact hp₀.2.1) 0 1 0 0
    (by rintro _ ⟨_, _, rfl⟩; linarith [hp₀.1])
    (by
      rintro _ ⟨c, hc, rfl⟩
      have habs := (Complex.abs_re_le_norm (c - p₀.2.2)).trans (mem_closedBall_iff_norm.mp hc)
      rw [Complex.sub_re] at habs
      have hcre : 0 < c.re := by linarith [hr_def, hp₀.2.2, (abs_le.mp habs).1]
      simpa using hcre)
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
    refine ((hd.const_mul ((t : ℂ) ^ (p₀.1 - 1))).div_const
      (1 - p₀.2.1 * Complex.exp (-t))).congr_deriv ?_
    have hmul : (t : ℂ) ^ (p₀.1 - 1) * (-(t : ℂ) * Complex.exp (-(c * t))) =
        -(((t : ℂ) ^ (p₀.1 - 1) * (t : ℂ)) * Complex.exp (-(c * t))) := by ring
    rw [hmul, hpow, neg_div]

/-- The principal Lerch integral `lerchIntegral` is jointly analytic on
`{p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}`. -/
theorem analyticOnNhd_lerchIntegral :
    AnalyticOnNhd ℂ lerchIntegral
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} := by
  set U : Set (ℂ × ℂ × ℂ) := {p | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}
  have hraw : AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ × ℂ => ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t))) U :=
    continuousOn_rawLerchIntegral.analyticOnNhd_of_differentiableAt_prod_prod
      isOpen_lerchIntegralDomain
      (fun _ hp => differentiableAt_rawLerchIntegral_first hp)
      (fun _ hp => differentiableAt_rawLerchIntegral_second hp)
      (fun _ hp => differentiableAt_rawLerchIntegral_third hp)
  have hG : AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => (Complex.Gamma p.1)⁻¹) U := fun p _ =>
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ p.1
      trivial).comp analyticAt_fst
  exact (hG.mul hraw).congr isOpen_lerchIntegralDomain fun p _ => (lerchIntegral_def p).symm

/-- `lerchIntegral` is jointly complex differentiable on
`{p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}`. -/
theorem differentiableOn_lerchIntegral :
    DifferentiableOn ℂ lerchIntegral
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} :=
  analyticOnNhd_lerchIntegral.differentiableOn

/-! ### Agreement with `lerchSeries` on the open unit disc and principal-sheet identities -/

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
    ((Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs
      (Complex.natCast_add_re_pos n hc)).const_mul (z ^ n)).norm (hg₀.const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hexp : Real.exp (-(n : ℝ) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hn_exp : ‖Complex.exp (-((n : ℂ) * t))‖ = Real.exp (-(n : ℝ) * t) := by
    rw [Complex.norm_exp]; simp [neg_mul]
  dsimp only [g₀]
  simp only [exp_neg_natCast_add_mul, norm_mul, norm_pow, hn_exp]
  gcongr
  exact mul_le_of_le_one_left (norm_nonneg _) hexp

/-- On the open unit disc `‖z‖ < 1` with `0 < Re s` and `0 < Re c`, `lerchIntegral (s, z, c)`
agrees with `lerchSeries z s c`. -/
theorem lerchIntegral_eq_lerchSeries {s z c : ℂ} (hs : 0 < s.re) (hz : ‖z‖ < 1) (hc : 0 < c.re) :
    lerchIntegral (s, z, c) = lerchSeries z s c := by
  let F : ℕ → ℝ → ℂ := fun n t =>
    z ^ n * ((t : ℂ) ^ (s - 1) * Complex.exp (-(((n : ℂ) + c) * t)))
  have hF_int (n : ℕ) : Integrable (F n) (volume.restrict (Ioi 0)) :=
    (Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs
      (Complex.natCast_add_re_pos n hc)).const_mul (z ^ n)
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
        rw [exp_neg_natCast_add_mul, mul_pow, ← Complex.exp_natCast_mul]
        simp only [mul_neg]
        ring
      simp_rw [hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hzw, div_eq_mul_inv]
  have hterm_int (n : ℕ) : ∫ t : ℝ in Ioi 0, F n t =
      Complex.Gamma s * (z ^ n * Complex.exp (-s * Complex.log (n + c))) := by
    have hcpos := Complex.natCast_add_re_pos n hc
    have hne : (n : ℂ) + c ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hcpos; exact lt_irrefl 0 hcpos
    dsimp only [F]
    rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs hcpos,
      Complex.cpow_def_of_ne_zero hne, mul_comm (Complex.log _)]
    ring
  rw [lerchIntegral_def, ← htsum_eq, ← hsum.tsum_eq]
  simp_rw [hterm_int, tsum_mul_left, ← lerchSeries_def]
  exact inv_mul_cancel_left₀ (Complex.Gamma_ne_zero_of_re_pos hs) _

/-- Parameter shift `lerchIntegral (s, z, c) = exp (-s * log c) + z * lerchIntegral (s, z, c + 1)`
across the entire cut domain `0 < Re s`, `1 - z ∈ Complex.slitPlane`, `0 < Re c`. -/
theorem lerchIntegral_eq_exp_add_mul_add_one_right {s z c : ℂ} (hs : 0 < s.re)
    (hz : 1 - z ∈ Complex.slitPlane) (hc : 0 < c.re) :
    lerchIntegral (s, z, c) =
      Complex.exp (-s * Complex.log c) + z * lerchIntegral (s, z, c + 1) := by
  have hc1 : 0 < (c + 1).re := by simp; linarith
  have hc0 : c ≠ 0 := by intro h; rw [h, Complex.zero_re] at hc; exact lt_irrefl 0 hc
  have hi1 := Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs hc
  have hi2 := (integrableOn_lerchIntegrand (p := (s, z, c + 1)) hs hz hc1).const_mul z
  have hcongr : ∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (s - 1) * Complex.exp (-(c * t)) / (1 - z * Complex.exp (-t)) =
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-(c * t))) +
        ∫ t : ℝ in Ioi 0, z * ((t : ℂ) ^ (s - 1) * Complex.exp (-((c + 1) * t)) /
          (1 - z * Complex.exp (-t))) := by
    rw [← integral_add hi1 hi2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hden := Complex.one_sub_mul_exp_neg_ne_zero hz (le_of_lt ht)
    rw [exp_neg_add_one_mul]
    field_simp; ring
  rw [lerchIntegral_def (s, z, c), lerchIntegral_def (s, z, c + 1), hcongr,
    Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs hc,
    Complex.cpow_def_of_ne_zero hc0, mul_comm (Complex.log c), integral_const_mul,
    mul_add, inv_mul_cancel_left₀ (Complex.Gamma_ne_zero_of_re_pos hs)]
  dsimp only; ring

/-- Lowering differential relation
`(z ∂_z + c) lerchIntegral (s, z, c) = lerchIntegral (s - 1, z, c)` on the principal cut plane
`1 - z ∈ Complex.slitPlane` for `1 < s.re` and `0 < c.re`. -/
theorem mul_deriv_lerchIntegral_middle_add_mul {s z c : ℂ} (hs : 1 < s.re)
    (hz : 1 - z ∈ Complex.slitPlane) (hc : 0 < c.re) :
    z * deriv (fun w => lerchIntegral (s, w, c)) z + c * lerchIntegral (s, z, c) =
      lerchIntegral (s - 1, z, c) := by
  let Ω : Set ℂ := {w : ℂ | 1 - w ∈ Complex.slitPlane}
  have hs0 : 0 < s.re := by linarith
  have hs1 : 0 < (s - 1).re := by simp; linarith
  have hF_an : AnalyticOnNhd ℂ (fun w : ℂ => lerchIntegral (s, w, c)) Ω := fun w hw => by
    let φ : ℂ → ℂ × ℂ × ℂ := fun u => (s, u, c)
    have hφ : AnalyticAt ℂ φ w := analyticAt_const.prod (analyticAt_id.prod analyticAt_const)
    exact (analyticOnNhd_lerchIntegral (φ w) ⟨hs0, hw, hc⟩).comp (f := φ) hφ
  have han1 : AnalyticOnNhd ℂ
      (fun w : ℂ => w * deriv (fun u => lerchIntegral (s, u, c)) w + c * lerchIntegral (s, w, c))
      Ω := fun w hw =>
    (analyticAt_id.mul (hF_an w hw).deriv).add (analyticAt_const.mul (hF_an w hw))
  have han2 : AnalyticOnNhd ℂ (fun w : ℂ => lerchIntegral (s - 1, w, c)) Ω := fun w hw => by
    let φ : ℂ → ℂ × ℂ × ℂ := fun u => (s - 1, u, c)
    have hφ : AnalyticAt ℂ φ w := analyticAt_const.prod (analyticAt_id.prod analyticAt_const)
    exact (analyticOnNhd_lerchIntegral (φ w) ⟨hs1, hw, hc⟩).comp (f := φ) hφ
  have hev : (fun w : ℂ =>
        w * deriv (fun u => lerchIntegral (s, u, c)) w + c * lerchIntegral (s, w, c)) =ᶠ[𝓝 (0 : ℂ)]
      fun w => lerchIntegral (s - 1, w, c) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hloc : (fun u => lerchIntegral (s, u, c)) =ᶠ[𝓝 w] fun u => lerchSeries u s c := by
      filter_upwards [isOpen_ball.mem_nhds hw] with u hu
      exact lerchIntegral_eq_lerchSeries hs0 (mem_ball_zero_iff.mp hu) hc
    rw [hloc.deriv_eq, lerchIntegral_eq_lerchSeries hs0 hw1 hc,
      lerchIntegral_eq_lerchSeries hs1 hw1 hc]
    exact mul_deriv_lerchSeries_left_add_mul hw1 s fun n =>
      Complex.slitPlane_ne_zero
        (Complex.mem_slitPlane_iff.mpr (Or.inl (Complex.natCast_add_re_pos n hc)))
  exact han1.eqOn_of_preconnected_of_eventuallyEq han2
    Complex.isPreconnected_setOf_one_sub_mem_slitPlane (by simp [Ω]) hev hz

end TauCeti
