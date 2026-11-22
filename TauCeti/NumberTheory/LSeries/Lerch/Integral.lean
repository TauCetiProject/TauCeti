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
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.Analysis.SpecialFunctions.Integrals.LogPower

/-!
# Principal integral representation of the Lerch transcendent

For `0 < Re s`, `1 - z ∈ Complex.slitPlane` (`z ∈ ℂ \ [1, ∞)`), and `0 < Re c`, the Laplace-Mellin
integral `lerchIntegral (s, z, c) = Γ(s)⁻¹ * ∫ t in Ioi 0, t ^ (s - 1) * exp (-(c * t)) /
(1 - z * exp (-t))` converges absolutely and defines a jointly analytic function of `(s, z, c)`
extending `TauCeti.lerchSeries z s c` from `‖z‖ < 1` across `ℂ \ [1, ∞)`.

## Main declarations

* `TauCeti.lerchIntegral`, `IsCompact.exists_integrableOn_Ioi_lerchMajorant`,
  `TauCeti.integrableOn_lerchIntegrand`: Gamma-normalized integral representation, compact
  dominated majorant, and integrability on `(0, ∞)`.
* `TauCeti.analyticOnNhd_lerchIntegral`, `TauCeti.analyticOnNhd_lerchIntegral_middle`,
  `TauCeti.differentiableOn_lerchIntegral`: joint analyticity, `z`-slice analyticity, and
  holomorphy on `{p | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}`.
* `TauCeti.lerchIntegral_eq_lerchSeries`,
  `TauCeti.lerchIntegral_eq_sum_range_add_pow_mul_add_natCast_right`,
  `TauCeti.lerchIntegral_eq_exp_add_mul_add_one_right`: agreement with `lerchSeries` on `‖z‖ < 1`,
  `N`-step and `1`-step `c`-shift identities.
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

/-- On a compact set `K ⊆ ℂ × ℂ × ℂ` whose second component satisfies `1 - z ∈ Complex.slitPlane`,
shifted powers `‖(t : ℂ) ^ (s + shift_s) * (log t) ^ k * exp (-((c + shift_c) * t))‖` divided by
`‖1 - z * exp (-t)‖ ^ pow_denom` admit a single integrable majorant on `(0, ∞)` whenever
`-1 < Re s + shift_s` and `0 < Re c + shift_c`. -/
theorem _root_.IsCompact.exists_integrableOn_Ioi_lerchMajorant {K : Set (ℂ × ℂ × ℂ)}
    (hK : IsCompact K) (hKz : ∀ p ∈ K, 1 - p.2.1 ∈ Complex.slitPlane)
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
  obtain ⟨g, hg, hle⟩ := (isCompact_singleton (x := p)).exists_integrableOn_Ioi_lerchMajorant
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

/-- The principal Lerch integral `lerchIntegral` is jointly analytic on
`{p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}`. -/
theorem analyticOnNhd_lerchIntegral :
    AnalyticOnNhd ℂ lerchIntegral
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} := by
  set U : Set (ℂ × ℂ × ℂ) := {p | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}
  set F : (ℂ × ℂ × ℂ) → ℝ → ℂ := fun p t =>
    (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t))
  have hraw : AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => ∫ t : ℝ in Ioi 0, F p t) U := by
    refine analyticOnNhd_integral_of_dominated isOpen_lerchIntegralDomain
      (fun _ _ => Measurable.aestronglyMeasurable (by fun_prop)) ?_ ?_
    · intro p₀ hp₀
      obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
        (isOpen_lerchIntegralDomain.mem_nhds hp₀)
      obtain ⟨g, hg, hle⟩ := (isCompact_closedBall p₀ r).exists_integrableOn_Ioi_lerchMajorant
        (fun p hp => (hsub hp).2.1) 0 1 (-1) 0
        (fun p hp => by linarith [(hsub hp).1]) (fun p hp => by simpa using (hsub hp).2.2)
      refine ⟨closedBall p₀ r, closedBall_mem_nhds p₀ hr, g, hg, ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht p hp
      simpa [F, sub_eq_add_neg, norm_div] using hle p hp t ht
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht p hp
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
      have hden : 1 - p.2.1 * Complex.exp (-t) ≠ 0 :=
        Complex.slitPlane_ne_zero (Complex.one_sub_mul_exp_neg_mem_slitPlane hp.2.1 ht.le)
      have hpow : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => (t : ℂ) ^ (q.1 - 1)) p :=
        ((differentiableAt_fst.sub_const 1).const_cpow (Or.inl ht0)).comp p differentiableAt_id
      have hexp : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => Complex.exp (-(q.2.2 * t))) p := by
        fun_prop
      have hden_diff : DifferentiableAt ℂ
          (fun q : ℂ × ℂ × ℂ => 1 - q.2.1 * Complex.exp (-t)) p := by
        fun_prop
      simpa only [F, div_eq_mul_inv] using
        ((hpow.fun_mul hexp).fun_mul (hden_diff.fun_inv hden)).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => (Complex.Gamma p.1)⁻¹) U := fun p _ =>
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ p.1
      trivial).comp analyticAt_fst
  exact (hG.mul hraw).congr isOpen_lerchIntegralDomain fun p _ => (lerchIntegral_def p).symm

/-- For `0 < Re s` and `0 < Re c`, `z ↦ lerchIntegral (s, z, c)` is analytic on the cut plane
`{w : ℂ | 1 - w ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_lerchIntegral_middle {s c : ℂ} (hs : 0 < s.re) (hc : 0 < c.re) :
    AnalyticOnNhd ℂ (fun w : ℂ => lerchIntegral (s, w, c)) {w | 1 - w ∈ Complex.slitPlane} :=
  fun w hw =>
    (analyticOnNhd_lerchIntegral (s, w, c) ⟨hs, hw, hc⟩).comp
      (f := fun u : ℂ => (s, u, c)) (analyticAt_const.prod (analyticAt_id.prod analyticAt_const))

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
    dsimp only [F]
    rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi_eq_Gamma_mul_exp hs hcpos]
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
  have hi1 := Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs hc
  have hi2 := (integrableOn_lerchIntegrand (p := (s, z, c + 1)) hs hz hc1).const_mul z
  have hcongr : ∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (s - 1) * Complex.exp (-(c * t)) / (1 - z * Complex.exp (-t)) =
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-(c * t))) +
        ∫ t : ℝ in Ioi 0, z * ((t : ℂ) ^ (s - 1) * Complex.exp (-((c + 1) * t)) /
          (1 - z * Complex.exp (-t))) := by
    rw [← integral_add hi1 hi2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hden :=
      Complex.slitPlane_ne_zero (Complex.one_sub_mul_exp_neg_mem_slitPlane hz (le_of_lt ht))
    rw [exp_neg_add_one_mul]
    field_simp; ring
  rw [lerchIntegral_def (s, z, c), lerchIntegral_def (s, z, c + 1), hcongr,
    Complex.integral_cpow_mul_exp_neg_mul_Ioi_eq_Gamma_mul_exp hs hc, integral_const_mul,
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
    exact mul_deriv_lerchSeries_left_add_mul hw1 s fun n =>
      Complex.slitPlane_ne_zero
        (Complex.mem_slitPlane_iff.mpr (Or.inl (Complex.natCast_add_re_pos n hc)))
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
  obtain ⟨g, hg, hle⟩ := hK.exists_integrableOn_Ioi_lerchMajorant
    (fun p hp => by rw [hp.2.1]; exact hz) 0 1 (-1) 0
    (fun p hp => by rw [hp.1]; linarith) (fun p hp => by simpa using hcb hp.2.2)
  let F : ℂ → ℝ → ℂ := fun w t =>
    (t : ℂ) ^ (s - 1) * Complex.exp (-(w * t)) / (1 - z * Complex.exp (-t))
  have hraw : HasDerivAt (fun w => ∫ t : ℝ in Ioi 0, F w t)
      (∫ t : ℝ in Ioi 0, deriv (F · t) c) c := by
    refine hasDerivAt_integral_of_dominated_of_differentiableOn isOpen_ball (mem_ball_self hδ)
      (fun _ _ => Measurable.aestronglyMeasurable (by fun_prop)) ?_ hg
      (Eventually.of_forall fun _ => (by fun_prop : Differentiable ℂ (F · _)).differentiableOn)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    simpa [F, sub_eq_add_neg, norm_div] using
      hle (s, z, w) ⟨rfl, rfl, ball_subset_closedBall hw⟩ t ht
  have hderiv_int : ∫ t : ℝ in Ioi 0, deriv (F · t) c =
      - ∫ t : ℝ in Ioi 0,
          (t : ℂ) ^ ((s + 1) - 1) * Complex.exp (-(c * t)) / (1 - z * Complex.exp (-t)) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have hpow : (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ ((s + 1) - 1) := by
      simpa [sub_add_cancel, add_sub_cancel_right] using (Complex.cpow_add (s - 1) 1 ht0).symm
    have hd : HasDerivAt (F · t)
        (-((t : ℂ) ^ ((s + 1) - 1) * Complex.exp (-(c * t)) / (1 - z * Complex.exp (-t)))) c := by
      refine ((((((hasDerivAt_id c).mul_const (t : ℂ)).fun_neg).cexp).const_mul
        ((t : ℂ) ^ (s - 1))).div_const (1 - z * Complex.exp (-t))).congr_deriv ?_
      dsimp only [id_eq]
      rw [← hpow]
      ring
    exact hd.deriv
  refine (hraw.const_mul (Complex.Gamma s)⁻¹).congr_deriv ?_
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
