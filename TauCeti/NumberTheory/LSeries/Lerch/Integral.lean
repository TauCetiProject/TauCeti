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
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
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
* `TauCeti.analyticOnNhd_lerchIntegral`, `TauCeti.analyticOnNhd_lerchIntegral_z`,
  `TauCeti.differentiableOn_lerchIntegral`: joint analyticity, `z`-slice analyticity, and
  holomorphy on `{p | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}`.
* `TauCeti.lerchIntegral_eq_lerchSeries`,
  `TauCeti.lerchIntegral_eq_sum_range_add_pow_mul_add_natCast_right`,
  `TauCeti.lerchIntegral_eq_exp_add_mul_add_one_right`: agreement with `lerchSeries` on `‖z‖ < 1`,
  `N`-step and `1`-step `c`-shift identities.
* `TauCeti.mul_deriv_lerchIntegral_z_add_mul`, `TauCeti.hasDerivAt_lerchIntegral_c`,
  `TauCeti.deriv_lerchIntegral_c`: lowering relation `(z ∂_z + c) lerchIntegral (s, z, c) =
  lerchIntegral (s - 1, z, c)` and raising relation `∂_c lerchIntegral (s, z, c) =
  -s * lerchIntegral (s + 1, z, c)` on `1 - z ∈ Complex.slitPlane`.

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

private theorem exists_le_norm_one_sub_mul_exp_neg {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ {z : ℂ | 1 - z ∈ Complex.slitPlane}) :
    ∃ δ > 0, ∀ z ∈ K, ∀ t ≥ (0 : ℝ), δ ≤ ‖1 - z * Complex.exp (-t)‖ := by
  obtain ⟨δ, hδ, h⟩ := hK.exists_le_norm_one_sub_ofReal_mul hKΩ
  refine ⟨δ, hδ, fun z hz t ht => ?_⟩
  simpa [Complex.ofReal_exp, mul_comm z] using
    h z hz (Real.exp (-t)) ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩

private theorem one_sub_mul_exp_neg_mem_slitPlane {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane)
    {t : ℝ} (ht : 0 ≤ t) : 1 - z * Complex.exp (-t) ∈ Complex.slitPlane := by
  simpa [Complex.ofReal_exp] using
    Complex.one_sub_mul_ofReal_mem_slitPlane hz
      ⟨(Real.exp_pos (-t)).le, Real.exp_le_one_iff.mpr (by linarith)⟩

private theorem one_sub_mul_exp_neg_ne_zero {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) {t : ℝ}
    (ht : 0 ≤ t) : 1 - z * Complex.exp (-t) ≠ 0 :=
  Complex.slitPlane_ne_zero (one_sub_mul_exp_neg_mem_slitPlane hz ht)

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
    exists_le_norm_one_sub_mul_exp_neg (hK.image (continuous_fst.comp continuous_snd))
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

private theorem differentiableAt_rawLerchIntegral {p₀ : ℂ × ℂ × ℂ}
    (hp₀ : 0 < p₀.1.re ∧ 1 - p₀.2.1 ∈ Complex.slitPlane ∧ 0 < p₀.2.2.re) :
    DifferentiableAt ℂ
      (fun p : ℂ × ℂ × ℂ => ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t)))
      p₀ := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (isOpen_lerchIntegralDomain.mem_nhds hp₀)
  have hK : IsCompact (closedBall p₀ r) := isCompact_closedBall p₀ r
  obtain ⟨g₁, hg₁, hle₁⟩ := exists_integrableOn_Ioi_lerchMajorant hK
    (fun p hp => (hsub hp).2.1) 1 1 (-1) 0
    (fun p hp => by linarith [(hsub hp).1]) (fun p hp => by simpa using (hsub hp).2.2)
  obtain ⟨g₂, hg₂, hle₂⟩ := exists_integrableOn_Ioi_lerchMajorant hK
    (fun p hp => (hsub hp).2.1) 0 2 (-1) 1
    (fun p hp => by linarith [(hsub hp).1]) (fun p hp => by linarith [(hsub hp).2.2])
  obtain ⟨g₃, hg₃, hle₃⟩ := exists_integrableOn_Ioi_lerchMajorant hK
    (fun p hp => (hsub hp).2.1) 0 1 0 0
    (fun p hp => by linarith [(hsub hp).1]) (fun p hp => by simpa using (hsub hp).2.2)
  let π₁ : (ℂ × ℂ × ℂ) →L[ℂ] ℂ := ContinuousLinearMap.fst ℂ ℂ (ℂ × ℂ)
  let π₂ : (ℂ × ℂ × ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))
  let π₃ : (ℂ × ℂ × ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))
  let F : (ℂ × ℂ × ℂ) → ℝ → ℂ := fun p t =>
    (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t))
  let dsF : (ℂ × ℂ × ℂ) → ℝ → ℂ := fun p t =>
    (t : ℂ) ^ (p.1 - 1) * Complex.log t * Complex.exp (-(p.2.2 * t)) /
      (1 - p.2.1 * Complex.exp (-t))
  let dzF : (ℂ × ℂ × ℂ) → ℝ → ℂ := fun p t =>
    (t : ℂ) ^ (p.1 - 1) * Complex.exp (-((p.2.2 + 1) * t)) /
      (1 - p.2.1 * Complex.exp (-t)) ^ 2
  let dcF : (ℂ × ℂ × ℂ) → ℝ → ℂ := fun p t =>
    -((t : ℂ) ^ p.1 * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t)))
  let F' : (ℂ × ℂ × ℂ) → ℝ → (ℂ × ℂ × ℂ) →L[ℂ] ℂ := fun p t =>
    dsF p t • π₁ + dzF p t • π₂ + dcF p t • π₃
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (bound := fun t => g₁ t + g₂ t + g₃ t)
    (closedBall_mem_nhds p₀ hr)
    (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_lerchIntegrand hp₀.1 hp₀.2.1 hp₀.2.2)
    ?meas_F' ?bound_le ((hg₁.add hg₂).add hg₃) ?diff).differentiableAt
  case meas_F' =>
    exact ((Measurable.smul_const (by fun_prop) π₁).add
      (Measurable.smul_const (by fun_prop) π₂)).add
      (Measurable.smul_const (by fun_prop) π₃) |>.aestronglyMeasurable
  case bound_le =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht p hp
    have h1' : ‖dsF p t‖ ≤ g₁ t := calc
      ‖dsF p t‖
          = ‖(t : ℂ) ^ (p.1 + ((-1 : ℝ) : ℂ)) * (Complex.log t) ^ 1 *
              Complex.exp (-((p.2.2 + ((0 : ℝ) : ℂ)) * t))‖ /
            ‖1 - p.2.1 * Complex.exp (-t)‖ ^ 1 := by
              simp [dsF, sub_eq_add_neg]
      _ ≤ g₁ t := hle₁ p hp t ht
    have h2' : ‖dzF p t‖ ≤ g₂ t := calc
      ‖dzF p t‖
          = ‖(t : ℂ) ^ (p.1 + ((-1 : ℝ) : ℂ)) * (Complex.log t) ^ 0 *
              Complex.exp (-((p.2.2 + ((1 : ℝ) : ℂ)) * t))‖ /
            ‖1 - p.2.1 * Complex.exp (-t)‖ ^ 2 := by
              simp [dzF, sub_eq_add_neg, norm_pow]
      _ ≤ g₂ t := hle₂ p hp t ht
    have h3' : ‖dcF p t‖ ≤ g₃ t := calc
      ‖dcF p t‖
          = ‖(t : ℂ) ^ (p.1 + ((0 : ℝ) : ℂ)) * (Complex.log t) ^ 0 *
              Complex.exp (-((p.2.2 + ((0 : ℝ) : ℂ)) * t))‖ /
            ‖1 - p.2.1 * Complex.exp (-t)‖ ^ 1 := by
              simp [dcF, norm_neg]
      _ ≤ g₃ t := hle₃ p hp t ht
    refine ContinuousLinearMap.opNorm_le_bound _ (by
      linarith [(norm_nonneg (dsF p t)).trans h1', (norm_nonneg (dzF p t)).trans h2',
        (norm_nonneg (dcF p t)).trans h3']) fun v => ?_
    have hv1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
    have hv2 : ‖v.2.1‖ ≤ ‖v‖ := (norm_fst_le v.2).trans (norm_snd_le v)
    have hv3 : ‖v.2.2‖ ≤ ‖v‖ := (norm_snd_le v.2).trans (norm_snd_le v)
    have hsum : ‖F' p t v‖ ≤ ‖dsF p t‖ * ‖v.1‖ + ‖dzF p t‖ * ‖v.2.1‖ + ‖dcF p t‖ * ‖v.2.2‖ := by
      simp only [F', add_apply, smul_apply, smul_eq_mul, π₁, π₂, π₃,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_snd', ← norm_mul]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    calc ‖F' p t v‖
        ≤ ‖dsF p t‖ * ‖v.1‖ + ‖dzF p t‖ * ‖v.2.1‖ + ‖dcF p t‖ * ‖v.2.2‖ := hsum
      _ ≤ g₁ t * ‖v‖ + g₂ t * ‖v‖ + g₃ t * ‖v‖ :=
        add_le_add
          (add_le_add
            (mul_le_mul h1' hv1 (norm_nonneg _) ((norm_nonneg _).trans h1'))
            (mul_le_mul h2' hv2 (norm_nonneg _) ((norm_nonneg _).trans h2')))
          (mul_le_mul h3' hv3 (norm_nonneg _) ((norm_nonneg _).trans h3'))
      _ = (g₁ t + g₂ t + g₃ t) * ‖v‖ := by ring
  case diff =>
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht p hp
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have hden : 1 - p.2.1 * Complex.exp (-t) ≠ 0 := one_sub_mul_exp_neg_ne_zero (hsub hp).2.1 ht.le
    have hp1 : HasFDerivAt (fun q : ℂ × ℂ × ℂ => q.1) π₁ p := hasFDerivAt_fst
    have hp2 : HasFDerivAt (fun q : ℂ × ℂ × ℂ => q.2.1) π₂ p :=
      hasFDerivAt_fst.comp p hasFDerivAt_snd
    have hp3 : HasFDerivAt (fun q : ℂ × ℂ × ℂ => q.2.2) π₃ p :=
      hasFDerivAt_snd.comp p hasFDerivAt_snd
    have hd_pow_1d : HasDerivAt (fun u : ℂ => (t : ℂ) ^ (u - 1))
        ((t : ℂ) ^ (p.1 - 1) * Complex.log t) p.1 :=
      (((hasDerivAt_id p.1).sub_const 1).const_cpow (Or.inl ht0)).congr_deriv
        (by simp [id_eq, mul_comm])
    have hd_pow : HasFDerivAt (fun q : ℂ × ℂ × ℂ => (t : ℂ) ^ (q.1 - 1))
        (((t : ℂ) ^ (p.1 - 1) * Complex.log t) • π₁) p :=
      hd_pow_1d.comp_hasFDerivAt p hp1
    have hd_exp_1d : HasDerivAt (fun u : ℂ => Complex.exp (-(u * t)))
        (-(t : ℂ) * Complex.exp (-(p.2.2 * t))) p.2.2 :=
      (((hasDerivAt_id p.2.2).mul_const (t : ℂ)).neg.cexp).congr_deriv
        (by simp [id_eq, mul_comm])
    have hd_exp : HasFDerivAt (fun q : ℂ × ℂ × ℂ => Complex.exp (-(q.2.2 * t)))
        ((-(t : ℂ) * Complex.exp (-(p.2.2 * t))) • π₃) p :=
      hd_exp_1d.comp_hasFDerivAt (h₂ := fun u : ℂ => Complex.exp (-(u * t))) p hp3
    have hd_den_1d : HasDerivAt (fun u : ℂ => (1 - u * Complex.exp (-t))⁻¹)
        (Complex.exp (-t) / (1 - p.2.1 * Complex.exp (-t)) ^ 2) p.2.1 :=
      (((hasDerivAt_const p.2.1 (1 : ℂ)).sub
        ((hasDerivAt_id p.2.1).mul_const (Complex.exp (-t)))).inv hden).congr_deriv
        (by simp)
    have hd_den : HasFDerivAt (fun q : ℂ × ℂ × ℂ => (1 - q.2.1 * Complex.exp (-t))⁻¹)
        ((Complex.exp (-t) / (1 - p.2.1 * Complex.exp (-t)) ^ 2) • π₂) p :=
      hd_den_1d.comp_hasFDerivAt (h₂ := fun u : ℂ => (1 - u * Complex.exp (-t))⁻¹) p hp2
    have hd_mul := (hd_pow.mul hd_exp).mul hd_den
    refine (hd_mul.congr_of_eventuallyEq (Eventually.of_forall fun q => by
      simp [F, div_eq_mul_inv])).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    have hpow : (t : ℂ) ^ (p.1 - 1) * (t : ℂ) = (t : ℂ) ^ p.1 := by
      simpa [sub_add_cancel] using (Complex.cpow_add (p.1 - 1) 1 ht0).symm
    simp only [F', dsF, dzF, dcF, π₁, π₂, π₃, Pi.mul_apply, add_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_snd']
    rw [exp_neg_add_one_mul, ← hpow]
    field_simp [hden]
    ring

/-- The principal Lerch integral `lerchIntegral` is jointly analytic on
`{p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}`. -/
theorem analyticOnNhd_lerchIntegral :
    AnalyticOnNhd ℂ lerchIntegral
      {p : ℂ × ℂ × ℂ | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re} := by
  set U : Set (ℂ × ℂ × ℂ) := {p | 0 < p.1.re ∧ 1 - p.2.1 ∈ Complex.slitPlane ∧ 0 < p.2.2.re}
  have hraw : AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ × ℂ => ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (p.1 - 1) * Complex.exp (-(p.2.2 * t)) / (1 - p.2.1 * Complex.exp (-t))) U :=
    DifferentiableOn.analyticOnNhd_of_finiteDimensional
      (fun _ hp => (differentiableAt_rawLerchIntegral hp).differentiableWithinAt)
      isOpen_lerchIntegralDomain
  have hG : AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => (Complex.Gamma p.1)⁻¹) U := fun p _ =>
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ p.1
      trivial).comp analyticAt_fst
  exact (hG.mul hraw).congr isOpen_lerchIntegralDomain fun p _ => (lerchIntegral_def p).symm

/-- For `0 < Re s` and `0 < Re c`, `z ↦ lerchIntegral (s, z, c)` is analytic on the cut plane
`{w : ℂ | 1 - w ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_lerchIntegral_z {s c : ℂ} (hs : 0 < s.re) (hc : 0 < c.re) :
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
    have hden := one_sub_mul_exp_neg_ne_zero hz (le_of_lt ht)
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
theorem mul_deriv_lerchIntegral_z_add_mul {s z c : ℂ} (hs : 1 < s.re)
    (hz : 1 - z ∈ Complex.slitPlane) (hc : 0 < c.re) :
    z * deriv (fun w => lerchIntegral (s, w, c)) z + c * lerchIntegral (s, z, c) =
      lerchIntegral (s - 1, z, c) := by
  let Ω : Set ℂ := {w : ℂ | 1 - w ∈ Complex.slitPlane}
  have hs0 : 0 < s.re := by linarith
  have hs1 : 0 < (s - 1).re := by simp; linarith
  have hF_an : AnalyticOnNhd ℂ (fun w : ℂ => lerchIntegral (s, w, c)) Ω :=
    analyticOnNhd_lerchIntegral_z hs0 hc
  have han1 : AnalyticOnNhd ℂ
      (fun w : ℂ => w * deriv (fun u => lerchIntegral (s, u, c)) w + c * lerchIntegral (s, w, c))
      Ω := fun w hw =>
    (analyticAt_id.mul (hF_an w hw).deriv).add (analyticAt_const.mul (hF_an w hw))
  have han2 : AnalyticOnNhd ℂ (fun w : ℂ => lerchIntegral (s - 1, w, c)) Ω :=
    analyticOnNhd_lerchIntegral_z hs1 hc
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
    exact mul_deriv_lerchSeries_z_add_mul hw1 s fun n =>
      Complex.slitPlane_ne_zero
        (Complex.mem_slitPlane_iff.mpr (Or.inl (Complex.natCast_add_re_pos n hc)))
  exact han1.eqOn_of_preconnected_of_eventuallyEq han2
    Complex.isPreconnected_setOf_one_sub_mem_slitPlane (by simp [Ω]) hev hz

/-- Raising relation in `c` for `lerchIntegral`:
`∂_c lerchIntegral (s, z, c) = -s * lerchIntegral (s + 1, z, c)` on `0 < Re s`,
`1 - z ∈ Complex.slitPlane`, `0 < Re c`. -/
theorem deriv_lerchIntegral_c {s z c : ℂ} (hs : 0 < s.re) (hz : 1 - z ∈ Complex.slitPlane)
    (hc : 0 < c.re) :
    deriv (fun w => lerchIntegral (s, z, w)) c = -s * lerchIntegral (s + 1, z, c) := by
  let Ω : Set ℂ := {w : ℂ | 1 - w ∈ Complex.slitPlane}
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have han1 : AnalyticOnNhd ℂ (fun w : ℂ => deriv (fun u => lerchIntegral (s, w, u)) c) Ω := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_)
      Complex.isOpen_setOf_one_sub_mem_slitPlane
    let L : (ℂ × ℂ × ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0, 0, (1 : ℂ))
    have hA : AnalyticAt ℂ lerchIntegral (s, w, c) :=
      analyticOnNhd_lerchIntegral (s, w, c) ⟨hs, hw, hc⟩
    have hφ : DifferentiableAt ℂ (fun w' : ℂ => (s, w', c)) w :=
      (differentiableAt_const s).prodMk (differentiableAt_id.prodMk (differentiableAt_const c))
    have hdiff : DifferentiableAt ℂ (fun w' : ℂ => L (fderiv ℂ lerchIntegral (s, w', c))) w :=
      L.differentiableAt.comp w (hA.fderiv.differentiableAt.comp w hφ)
    refine (hdiff.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [Complex.isOpen_setOf_one_sub_mem_slitPlane.mem_nhds hw] with w' hw'
    have hd : DifferentiableAt ℂ lerchIntegral (s, w', c) :=
      (analyticOnNhd_lerchIntegral (s, w', c) ⟨hs, hw', hc⟩).differentiableAt
    have hline : HasDerivAt (fun u : ℂ => lerchIntegral (s, w', u))
        (fderiv ℂ lerchIntegral (s, w', c) (0, 0, 1)) c := by
      have hc' : HasDerivAt (fun u : ℂ => (s, w', u)) (0, 0, (1 : ℂ)) c :=
        (hasDerivAt_const c s).prodMk ((hasDerivAt_const c w').prodMk (hasDerivAt_id c))
      exact hd.hasFDerivAt.comp_hasDerivAt c hc'
    exact hline.deriv
  have han2 : AnalyticOnNhd ℂ (fun w : ℂ => -s * lerchIntegral (s + 1, w, c)) Ω := fun w hw =>
    analyticAt_const.mul (analyticOnNhd_lerchIntegral_z hs1 hc w hw)
  have hev : (fun w : ℂ => deriv (fun u => lerchIntegral (s, w, u)) c) =ᶠ[𝓝 (0 : ℂ)]
      fun w => -s * lerchIntegral (s + 1, w, c) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    have hloc : (fun u => lerchIntegral (s, w, u)) =ᶠ[𝓝 c] fun u => lerchSeries w s u := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hc] with u hu
      exact lerchIntegral_eq_lerchSeries hs hw1 hu
    rw [hloc.deriv_eq, deriv_lerchSeries_c hw1 s (Complex.mem_slitPlane_iff.mpr (Or.inl hc)),
      lerchIntegral_eq_lerchSeries hs1 hw1 hc]
  exact han1.eqOn_of_preconnected_of_eventuallyEq han2
    Complex.isPreconnected_setOf_one_sub_mem_slitPlane (by simp [Ω]) hev hz

/-- `HasDerivAt` form of the raising relation in `c` for `lerchIntegral`. -/
theorem hasDerivAt_lerchIntegral_c {s z c : ℂ} (hs : 0 < s.re) (hz : 1 - z ∈ Complex.slitPlane)
    (hc : 0 < c.re) :
    HasDerivAt (fun w => lerchIntegral (s, z, w)) (-s * lerchIntegral (s + 1, z, c)) c := by
  have hdiff : DifferentiableAt ℂ (fun w => lerchIntegral (s, z, w)) c :=
    ((analyticOnNhd_lerchIntegral (s, z, c) ⟨hs, hz, hc⟩).comp
      (f := fun w : ℂ => (s, z, w))
      (analyticAt_const.prod (analyticAt_const.prod analyticAt_id))).differentiableAt
  simpa only [deriv_lerchIntegral_c hs hz hc] using hdiff.hasDerivAt

end TauCeti
