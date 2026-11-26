/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.NumberTheory.LSeries.Lerch.Series

import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate

/-!
# Principal integral representation of the Lerch transcendent

For `0 < Re s`, `1 - z ∈ Complex.slitPlane` (`z ∈ ℂ \ [1, ∞)`), and `0 < Re c`, the Laplace-Mellin
integral `lerchIntegral (s, z, c) = Γ(s)⁻¹ * ∫ t in Ioi 0, t ^ (s - 1) * exp (-(c * t)) /
(1 - z * exp (-t))` converges absolutely and defines a jointly analytic function of `(s, z, c)`
extending `TauCeti.lerchSeries z s c` from `‖z‖ < 1` across `ℂ \ [1, ∞)`.

## Main declarations

* `TauCeti.lerchIntegrand`, `TauCeti.lerchIntegral`,
  `IsCompact.exists_integrableOn_Ioi_norm_lerchIntegrand_le`,
  `TauCeti.integrableOn_lerchIntegrand`: integrand, Gamma-normalized integral representation,
  compact dominated majorant, and integrability on `(0, ∞)`.
* `TauCeti.lerchIntegralDomain`, `TauCeti.isOpen_lerchIntegralDomain`,
  `TauCeti.analyticOnNhd_lerchIntegral`, `TauCeti.analyticOnNhd_lerchIntegral_middle`,
  `TauCeti.differentiableOn_lerchIntegral`: cut domain, domain openness, joint analyticity,
  `z`-slice analyticity, and holomorphy on `lerchIntegralDomain`.
* `TauCeti.lerchIntegral_eq_lerchSeries`, `TauCeti.lerchIntegral_zero_middle`,
  `TauCeti.lerchIntegral_eq_sum_range_add_pow_mul_add_natCast_right`,
  `TauCeti.lerchIntegral_eq_exp_add_mul_add_one_right`: agreement with `lerchSeries` on `‖z‖ < 1`,
  evaluation at `z = 0`, and `N`-step and `1`-step `c`-shift identities.
* `TauCeti.mul_deriv_lerchIntegral_middle_add_mul`, `TauCeti.hasDerivAt_lerchIntegral_right`,
  `TauCeti.deriv_lerchIntegral_right`, `TauCeti.mul_deriv_deriv_lerchIntegral_right_add_mul`:
  lowering relation `(z ∂_z + c) lerchIntegral (s, z, c) = lerchIntegral (s - 1, z, c)`, raising
  relation `∂_c lerchIntegral (s, z, c) = -s * lerchIntegral (s + 1, z, c)`, and Lerch PDE
  `(z ∂_z + c) ∂_c lerchIntegral (s, z, c) = -s * lerchIntegral (s, z, c)` on
  `1 - z ∈ Complex.slitPlane`.

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

/-- Laplace-Mellin integrand `t ↦ t ^ (s - 1) * exp (-(c * t)) / (1 - z * exp (-t))` of the
principal Lerch integral in coordinates `p = (s, z, c) : ℂ × ℂ × ℂ`. -/
noncomputable def lerchIntegrand (p : ℂ × ℂ × ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t))

/-- Defining formula for `lerchIntegrand`. -/
theorem lerchIntegrand_def (p : ℂ × ℂ × ℂ) (t : ℝ) :
    lerchIntegrand p t =
      (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t)) := by
  rfl

/-- Principal Gamma-normalized integral representation of the Lerch transcendent in coordinates
`p = (s, z, c) : ℂ × ℂ × ℂ`. -/
noncomputable def lerchIntegral (p : ℂ × ℂ × ℂ) : ℂ :=
  (Complex.Gamma p.1)⁻¹ * ∫ t : ℝ in Ioi 0, lerchIntegrand p t

/-- Defining Laplace-Mellin integral formula for `lerchIntegral`. -/
theorem lerchIntegral_def (p : ℂ × ℂ × ℂ) :
    lerchIntegral p = (Complex.Gamma p.1)⁻¹ * ∫ t : ℝ in Ioi 0, lerchIntegrand p t := by rfl

/-! ### Cut-domain integrability -/

/-- On a compact subset `K` of `{p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧
0 < p.2.2.re}`, `lerchIntegrand` admits a single integrable norm majorant on `(0, ∞)` uniformly on
`K`. -/
theorem _root_.IsCompact.exists_integrableOn_Ioi_norm_lerchIntegrand_le
    {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K) (hKs : ∀ p ∈ K, 0 < p.1.re)
    (hKz : ∀ p ∈ K, 1 - p.2.1 ∈ Complex.slitPlane) (hKc : ∀ p ∈ K, 0 < p.2.2.re) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧
      ∀ p ∈ K, ∀ t > (0 : ℝ), ‖lerchIntegrand p t‖ ≤ g t := by
  obtain ⟨δ, hδ, hden⟩ :=
    (hK.image (continuous_fst.comp continuous_snd)).exists_le_norm_one_sub_ofReal_mul
      (by rintro _ ⟨p, hp, rfl⟩; exact hKz p hp)
  have hK' : IsCompact ((fun p : ℂ × ℂ × ℂ => (p.1 - 1, p.2.2)) '' K) :=
    hK.image (by fun_prop)
  obtain ⟨g₀, hg₀, hnum⟩ :=
    hK'.exists_integrableOn_Ioi_norm_cpow_mul_log_pow_mul_exp_neg_mul_le
      (by rintro _ ⟨p, hp, rfl⟩; simp; linarith [hKs p hp])
      (by rintro _ ⟨p, hp, rfl⟩; exact hKc p hp) 0
  refine ⟨fun t => δ⁻¹ * g₀ t, hg₀.const_mul _, fun p hp t ht => ?_⟩
  have hden_t : δ ≤ ‖1 - p.2.1 * Complex.exp (-t)‖ := by
    simpa [Complex.ofReal_exp, mul_comm p.2.1] using hden p.2.1 ⟨p, hp, rfl⟩ (Real.exp (-t))
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)⟩
  have hn := hnum (p.1 - 1, p.2.2) ⟨p, hp, rfl⟩ t ht
  simp only [pow_zero, mul_one] at hn
  rw [lerchIntegrand_def, norm_div, div_eq_mul_inv, mul_comm _ (‖1 - p.2.1 * Complex.exp (-t)‖)⁻¹]
  exact mul_le_mul (inv_anti₀ hδ hden_t) hn (norm_nonneg _) (by positivity)

/-- For `0 < Re s`, `1 - z ∈ Complex.slitPlane`, and `0 < Re c`, `lerchIntegrand` is integrable on
`(0, ∞)`. -/
theorem integrableOn_lerchIntegrand {p : ℂ × ℂ × ℂ} (hs : 0 < p.1.re)
    (hz : 1 - p.2.1 ∈ Complex.slitPlane) (hc : 0 < p.2.2.re) :
    IntegrableOn (lerchIntegrand p) (Ioi 0) := by
  obtain ⟨g, hg, hle⟩ :=
    (isCompact_singleton (x := p)).exists_integrableOn_Ioi_norm_lerchIntegrand_le
      (by rintro _ rfl; exact hs) (by rintro _ rfl; exact hz) (by rintro _ rfl; exact hc)
  have hmeas : Measurable (fun t : ℝ => lerchIntegrand p t) := by
    simp_rw [lerchIntegrand_def]
    fun_prop
  refine hg.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hle p rfl t ht

/-! ### Joint analyticity on the cut domain -/

/-- The principal Lerch integral domain
`{p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}`
in coordinates `(s, z, c)`. -/
def lerchIntegralDomain : Set (ℂ × ℂ × ℂ) :=
  {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}

/-- Defining set expression for `lerchIntegralDomain`. -/
theorem lerchIntegralDomain_def :
    lerchIntegralDomain =
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} := by
  rfl

/-- Membership characterization for `lerchIntegralDomain`. -/
@[simp]
theorem mem_lerchIntegralDomain {p : ℂ × ℂ × ℂ} :
    p ∈ lerchIntegralDomain ↔
      0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re := by
  rfl

/-- The principal Lerch integral domain `lerchIntegralDomain` is open. -/
theorem isOpen_lerchIntegralDomain : IsOpen lerchIntegralDomain := by
  rw [lerchIntegralDomain_def]
  exact (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter <|
    (Complex.isOpen_setOf_one_sub_mem_slitPlane.preimage
      (continuous_fst.comp continuous_snd)).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_snd.comp continuous_snd)))

/-- The principal Lerch integral `lerchIntegral` is jointly analytic on `lerchIntegralDomain`. -/
theorem analyticOnNhd_lerchIntegral :
    AnalyticOnNhd ℂ lerchIntegral lerchIntegralDomain := by
  have hmeas : ∀ p : ℂ × ℂ × ℂ,
      AEStronglyMeasurable (fun t : ℝ => lerchIntegrand p t) (volume.restrict (Ioi 0)) :=
    fun p => Measurable.aestronglyMeasurable
      (by simp_rw [lerchIntegrand_def]; fun_prop : Measurable (fun t : ℝ => lerchIntegrand p t))
  have hraw : AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => ∫ t : ℝ in Ioi 0, lerchIntegrand p t)
      lerchIntegralDomain := by
    refine analyticOnNhd_integral_of_dominated isOpen_lerchIntegralDomain (fun p _ => hmeas p) ?_ ?_
    · intro p₀ hp₀
      obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
        (isOpen_lerchIntegralDomain.mem_nhds hp₀)
      obtain ⟨g, hg, hle⟩ :=
        (isCompact_closedBall p₀ r).exists_integrableOn_Ioi_norm_lerchIntegrand_le
          (fun p hp => (mem_lerchIntegralDomain.mp (hsub hp)).1)
          (fun p hp => (mem_lerchIntegralDomain.mp (hsub hp)).2.1)
          (fun p hp => (mem_lerchIntegralDomain.mp (hsub hp)).2.2)
      refine ⟨closedBall p₀ r, closedBall_mem_nhds p₀ hr, g, hg, ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht p hp
      exact hle p hp t ht
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht p hp
      rw [mem_lerchIntegralDomain] at hp
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      have hden : 1 - p.2.1 * Complex.exp (-t) ≠ 0 :=
        Complex.slitPlane_ne_zero <| by
          simpa [Complex.ofReal_exp] using Complex.one_sub_mul_ofReal_mem_slitPlane hp.2.1
            ⟨(Real.exp_pos (-t)).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)⟩
      have hpow : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => (t : ℂ) ^ (q.1 - 1)) p :=
        ((differentiableAt_fst.sub_const 1).const_cpow (Or.inl ht0)).comp p differentiableAt_id
      have hexp : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => Complex.exp (-(q.2.2 * t))) p := by
        fun_prop
      have hden_diff : DifferentiableAt ℂ
          (fun q : ℂ × ℂ × ℂ => 1 - q.2.1 * Complex.exp (-t)) p := by
        fun_prop
      simp only [lerchIntegrand_def, div_eq_mul_inv]
      exact ((hpow.fun_mul hexp).fun_mul (hden_diff.fun_inv hden)).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => (Complex.Gamma p.1)⁻¹)
      lerchIntegralDomain := fun p _ =>
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ p.1
      trivial).comp analyticAt_fst
  exact (hG.mul hraw).congr isOpen_lerchIntegralDomain fun p _ => (lerchIntegral_def p).symm

/-- For `0 < Re s` and `0 < Re c`, `z ↦ lerchIntegral (s, z, c)` is analytic on the cut plane
`{w : ℂ | 1 - w ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_lerchIntegral_middle {s c : ℂ} (hs : 0 < s.re) (hc : 0 < c.re) :
    AnalyticOnNhd ℂ (fun w : ℂ => lerchIntegral (s, w, c)) {w | 1 - w ∈ Complex.slitPlane} :=
  fun w hw =>
    (analyticOnNhd_lerchIntegral (s, w, c) (mem_lerchIntegralDomain.mpr ⟨hs, hw, hc⟩)).comp
      (f := fun u : ℂ => (s, u, c)) (analyticAt_const.prod (analyticAt_id.prod analyticAt_const))

/-- `lerchIntegral` is jointly complex differentiable on `lerchIntegralDomain`. -/
theorem differentiableOn_lerchIntegral :
    DifferentiableOn ℂ lerchIntegral lerchIntegralDomain :=
  analyticOnNhd_lerchIntegral.differentiableOn

/-! ### Agreement with `lerchSeries` on the open unit disc and principal-sheet identities -/

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
    (Complex.summable_integral_norm_mul_cpow_mul_exp_neg_mul_Ioi (a := fun n : ℕ => z ^ n)
      (w := fun n : ℕ => (n : ℂ) + c)
      (by simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg z) hz) hc
      (fun n => by simp) hs)
  have htsum_eq : ∫ t : ℝ in Ioi 0, (∑' n, F n t) =
      ∫ t : ℝ in Ioi 0, lerchIntegrand (s, z, c) t :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => by
      have ht0 : 0 < t := ht
      have hzw : ‖z * Complex.exp (-t)‖ < 1 := by
        rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal]
        exact (mul_le_of_le_one_right (norm_nonneg z)
          (Real.exp_le_one_iff.mpr (by linarith))).trans_lt hz
      have hterm (n : ℕ) : F n t =
          ((t : ℂ) ^ (s - 1) * Complex.exp (-(c * t))) * (z * Complex.exp (-t)) ^ n := by
        dsimp only [F]
        rw [add_mul, neg_add, Complex.exp_add, mul_pow, ← Complex.exp_natCast_mul]
        simp only [mul_neg]
        ring
      rw [lerchIntegrand_def]
      simp_rw [hterm, tsum_mul_left, tsum_geometric_of_norm_lt_one hzw, div_eq_mul_inv]
  have hterm_int (n : ℕ) : ∫ t : ℝ in Ioi 0, F n t =
      Complex.Gamma s * (z ^ n * Complex.exp (-s * Complex.log (n + c))) := by
    have hcpos := Complex.natCast_add_re_pos n hc
    have hcne : (n : ℂ) + c ≠ 0 := Complex.ne_zero_of_re_pos hcpos
    dsimp only [F]
    rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs hcpos,
      Complex.cpow_def_of_ne_zero hcne, mul_comm (Complex.log _)]
    ring
  rw [lerchIntegral_def, ← htsum_eq, ← hsum.tsum_eq]
  simp_rw [hterm_int, tsum_mul_left, ← lerchSeries_def]
  exact inv_mul_cancel_left₀ (Complex.Gamma_ne_zero_of_re_pos hs) _

/-- At `z = 0` with `0 < Re s` and `0 < Re c`, `lerchIntegral (s, 0, c) = exp (-s * log c)`. -/
@[simp]
theorem lerchIntegral_zero_middle {s c : ℂ} (hs : 0 < s.re) (hc : 0 < c.re) :
    lerchIntegral (s, 0, c) = Complex.exp (-s * Complex.log c) := by
  rw [lerchIntegral_eq_lerchSeries hs (by simp) hc, lerchSeries_zero_left]

/-- Parameter shift `lerchIntegral (s, z, c) = exp (-s * log c) + z * lerchIntegral (s, z, c + 1)`
across the entire cut domain `0 < Re s`, `1 - z ∈ Complex.slitPlane`, `0 < Re c`. -/
theorem lerchIntegral_eq_exp_add_mul_add_one_right {s z c : ℂ} (hs : 0 < s.re)
    (hz : 1 - z ∈ Complex.slitPlane) (hc : 0 < c.re) :
    lerchIntegral (s, z, c) =
      Complex.exp (-s * Complex.log c) + z * lerchIntegral (s, z, c + 1) := by
  have hcne : c ≠ 0 := Complex.ne_zero_of_re_pos hc
  have hc1 : 0 < (c + 1).re := by simp; linarith
  have hi1 := Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs hc
  have hi2 := (integrableOn_lerchIntegrand (p := (s, z, c + 1)) hs hz hc1).const_mul z
  have hcongr : ∫ t : ℝ in Ioi 0, lerchIntegrand (s, z, c) t =
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-(c * t))) +
        ∫ t : ℝ in Ioi 0, z * lerchIntegrand (s, z, c + 1) t := by
    rw [← integral_add hi1 hi2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hden := Complex.slitPlane_ne_zero <| by
      simpa [Complex.ofReal_exp] using Complex.one_sub_mul_ofReal_mem_slitPlane hz
        ⟨(Real.exp_pos (-t)).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)⟩
    rw [lerchIntegrand_def, lerchIntegrand_def, add_mul, one_mul, neg_add, Complex.exp_add]
    field_simp; ring
  rw [lerchIntegral_def (s, z, c), lerchIntegral_def (s, z, c + 1), hcongr,
    Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs hc,
    Complex.cpow_def_of_ne_zero hcne, mul_comm (Complex.log c), integral_const_mul,
    mul_add, inv_mul_cancel_left₀ (Complex.Gamma_ne_zero_of_re_pos hs)]
  dsimp only; ring

/-- `N`-step shift identity in `c` for `lerchIntegral`, peeling off the first `N` terms across
the entire cut domain `0 < Re s`, `1 - z ∈ Complex.slitPlane`, `0 < Re c`. -/
theorem lerchIntegral_eq_sum_range_add_pow_mul_add_natCast_right {s z c : ℂ} (hs : 0 < s.re)
    (hz : 1 - z ∈ Complex.slitPlane) (hc : 0 < c.re) (N : ℕ) :
    lerchIntegral (s, z, c) =
      (∑ n ∈ Finset.range N, z ^ n * Complex.exp (-s * Complex.log (n + c))) +
        z ^ N * lerchIntegral (s, z, c + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hshift :=
      lerchIntegral_eq_exp_add_mul_add_one_right hs hz (Complex.natCast_add_re_pos N hc)
    rw [add_comm (N : ℂ) c] at hshift
    rw [ih, Finset.sum_range_succ, hshift]
    push_cast
    rw [add_comm (N : ℂ) c, ← add_assoc, pow_succ]
    ring

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
  have hF_an : AnalyticOnNhd ℂ (fun w : ℂ => lerchIntegral (s, w, c)) Ω :=
    analyticOnNhd_lerchIntegral_middle hs0 hc
  have han1 : AnalyticOnNhd ℂ
      (fun w : ℂ => w * deriv (fun u => lerchIntegral (s, u, c)) w + c * lerchIntegral (s, w, c))
      Ω := fun w hw =>
    (analyticAt_id.mul (hF_an w hw).deriv).add (analyticAt_const.mul (hF_an w hw))
  have han2 : AnalyticOnNhd ℂ (fun w : ℂ => lerchIntegral (s - 1, w, c)) Ω :=
    analyticOnNhd_lerchIntegral_middle hs1 hc
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
    exact mul_deriv_lerchSeries_left_add_mul hw1 s
      (natCast_add_ne_zero_of_mem_slitPlane (Complex.mem_slitPlane_iff.mpr (Or.inl hc)))
  exact han1.eqOn_of_preconnected_of_eventuallyEq han2
    Complex.isPreconnected_setOf_one_sub_mem_slitPlane (by simp [Ω]) hev hz

/-- `HasDerivAt` form of the raising relation in `c` for `lerchIntegral`:
`∂_c lerchIntegral (s, z, c) = -s * lerchIntegral (s + 1, z, c)` on `0 < Re s`,
`1 - z ∈ Complex.slitPlane`, `0 < Re c`. -/
theorem hasDerivAt_lerchIntegral_right {s z c : ℂ} (hs : 0 < s.re) (hz : 1 - z ∈ Complex.slitPlane)
    (hc : 0 < c.re) :
    HasDerivAt (fun w => lerchIntegral (s, z, w)) (-s * lerchIntegral (s + 1, z, c)) c := by
  obtain ⟨δ, hδ, hcb⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hc)
  let K : Set (ℂ × ℂ × ℂ) := ({s} : Set ℂ) ×ˢ (({z} : Set ℂ) ×ˢ closedBall c δ)
  have hK : IsCompact K :=
    isCompact_singleton.prod (isCompact_singleton.prod (isCompact_closedBall c δ))
  obtain ⟨g, hg, hle⟩ := hK.exists_integrableOn_Ioi_norm_lerchIntegrand_le
    (fun p hp => by rw [hp.1]; exact hs) (fun p hp => by rw [hp.2.1]; exact hz)
    (fun p hp => hcb hp.2.2)
  let F : ℂ → ℝ → ℂ := fun w t => lerchIntegrand (s, z, w) t
  have hF_diff (t : ℝ) : Differentiable ℂ (fun w => F w t) := by
    simp_rw [F, lerchIntegrand_def]
    fun_prop
  have hraw : HasDerivAt (fun w => ∫ t : ℝ in Ioi 0, F w t)
      (∫ t : ℝ in Ioi 0, deriv (F · t) c) c := by
    refine hasDerivAt_integral_of_dominated_of_differentiableOn isOpen_ball (mem_ball_self hδ)
      (fun w _ => Measurable.aestronglyMeasurable
        (by simp_rw [F, lerchIntegrand_def]; fun_prop : Measurable (fun t : ℝ => F w t)))
      ?_ hg (Eventually.of_forall fun t => (hF_diff t).differentiableOn)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    exact hle (s, z, w) ⟨rfl, rfl, ball_subset_closedBall hw⟩ t ht
  have hderiv_int : ∫ t : ℝ in Ioi 0, deriv (F · t) c =
      - ∫ t : ℝ in Ioi 0, lerchIntegrand (s + 1, z, c) t := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have hpow : (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ ((s + 1) - 1) := by
      simpa [sub_add_cancel, add_sub_cancel_right] using (Complex.cpow_add (s - 1) 1 ht0).symm
    have hF_eq : (F · t) =
        fun w : ℂ => (t : ℂ) ^ (s - 1) * Complex.exp (-(w * t)) / (1 - z * Complex.exp (-t)) :=
      funext fun w => lerchIntegrand_def (s, z, w) t
    have hd : HasDerivAt (F · t) (-(lerchIntegrand (s + 1, z, c) t)) c := by
      rw [hF_eq, lerchIntegrand_def]
      refine ((((((hasDerivAt_id c).mul_const (t : ℂ)).fun_neg).cexp).const_mul
        ((t : ℂ) ^ (s - 1))).div_const (1 - z * Complex.exp (-t))).congr_deriv ?_
      dsimp only [id_eq]
      rw [← hpow]
      ring
    exact hd.deriv
  refine ((hraw.const_mul (Complex.Gamma s)⁻¹).congr_of_eventuallyEq
    (Eventually.of_forall fun w => (lerchIntegral_def (s, z, w)).symm)).congr_deriv ?_
  rw [hderiv_int, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one, lerchIntegral_def]
  ring

/-- Raising relation in `c` for `lerchIntegral`:
`∂_c lerchIntegral (s, z, c) = -s * lerchIntegral (s + 1, z, c)` on `0 < Re s`,
`1 - z ∈ Complex.slitPlane`, `0 < Re c`. -/
theorem deriv_lerchIntegral_right {s z c : ℂ} (hs : 0 < s.re) (hz : 1 - z ∈ Complex.slitPlane)
    (hc : 0 < c.re) :
    deriv (fun w => lerchIntegral (s, z, w)) c = -s * lerchIntegral (s + 1, z, c) :=
  (hasDerivAt_lerchIntegral_right hs hz hc).deriv

/-- Coupling the raising derivative in `c` with the lowering operator `z ∂_z + c` yields the
second-order Lerch partial differential equation `(z ∂_z + c) ∂_c lerchIntegral (s, z, c) =
-s * lerchIntegral (s, z, c)` on `0 < s.re`, `1 - z ∈ Complex.slitPlane`, and `0 < c.re`. -/
theorem mul_deriv_deriv_lerchIntegral_right_add_mul {s z c : ℂ} (hs : 0 < s.re)
    (hz : 1 - z ∈ Complex.slitPlane) (hc : 0 < c.re) :
    z * deriv (fun w => deriv (fun u => lerchIntegral (s, w, u)) c) z +
        c * deriv (fun u => lerchIntegral (s, z, u)) c =
      -s * lerchIntegral (s, z, c) := by
  have hs1 : 1 < (s + 1).re := by simp; linarith
  have hloc : (fun w => deriv (fun u => lerchIntegral (s, w, u)) c) =ᶠ[𝓝 z]
      fun w => -s * lerchIntegral (s + 1, w, c) := by
    filter_upwards [Complex.isOpen_setOf_one_sub_mem_slitPlane.mem_nhds hz] with w hw
    exact deriv_lerchIntegral_right hs hw hc
  have hdiff : DifferentiableAt ℂ (fun w => lerchIntegral (s + 1, w, c)) z :=
    (analyticOnNhd_lerchIntegral_middle (by linarith) hc z hz).differentiableAt
  rw [hloc.deriv_eq, deriv_const_mul _ hdiff, deriv_lerchIntegral_right hs hz hc]
  have hlow := mul_deriv_lerchIntegral_middle_add_mul hs1 hz hc
  rw [add_sub_cancel_right] at hlow
  linear_combination -s * hlow

end TauCeti
