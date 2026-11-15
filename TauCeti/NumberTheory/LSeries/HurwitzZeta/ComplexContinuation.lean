/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.HurwitzZeta.BernoulliKernel
public import TauCeti.NumberTheory.LSeries.HurwitzZeta.ComplexSeries
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.Analysis.SpecialFunctions.Gamma.Order

/-!
# Joint analytic continuation and Bernoulli values of the complex Hurwitz zeta function

For `1 < s.re` and `0 < c.re`, the complex-rate Gamma integral
`Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos` expresses the complex-parameter Hurwitz series
`complexHurwitzSeries s c` as the normalized Mellin transform

`Γ(s)⁻¹ * ∫ t in Ioi 0, t ^ (s - 2) * hurwitzBernoulliKernel c t`.

Splitting `(0, ∞)` at `t = 1` and substituting the exact factored Taylor remainder
`hurwitzBernoulliKernel c t = ∑_{k=0}^M hurwitzBernoulliCoeff k c * t ^ k + t ^ (M + 1) * Q_M(c, t)`
on `(0, 1]` yields a family of subtracted Mellin approximations `hurwitzApprox M` that agree on
overlapping half-planes `-(M : ℝ) < s.re` and glue to global functions `complexHurwitzZeta s c` and
`complexHurwitzReg s c`.

Key ingredients of this continuation:
* Subtracting the `k = 0` Taylor term `1` isolates `(Complex.Gamma s)⁻¹ * (s - 1)⁻¹`, producing a
  simple pole at `s = 1` with residue `1` independent of `c`.
* Each higher Taylor term `k = j + 1` contributes `(Complex.Gamma s)⁻¹ / (s + j)`, whose removable
  singularity at `s = -j` is resolved by the entire difference quotient
  `invGammaDSlope j = dslope (fun s ↦ (Complex.Gamma s)⁻¹) (-j)`. Using
  `Complex.hasDerivAt_inv_Gamma_neg_nat`, `(Complex.Gamma (-m))⁻¹ = 0` and
  `invGammaDSlope m (-m) = (-1) ^ m * m!`, so evaluating at `s = -m` (including `m = 0`) cancels
  the near and tail integrals and yields `-B_{m + 1}(c) / (m + 1)`.
* Joint analyticity of the near and tail integrals follows from Osgood's lemma
  (`ContinuousOn.analyticOnNhd_of_differentiableAt_update`) together with dominated differentiation
  under the integral sign and `TauCeti.analyticAt_integral_smul`.

## Main definitions and results

* `TauCeti.invGammaDSlope`: the entire quotient `s ↦ (Complex.Gamma s)⁻¹ / (s + j)` defined via
  `dslope`.
* `TauCeti.integral_Ioi_cpow_mul_exp_div_one_sub_exp`: Euler–Mellin integral representation of
  `complexHurwitzSeries` on `1 < s.re`, `0 < c.re`.
* `TauCeti.complexHurwitzZeta`, `TauCeti.complexHurwitzReg`: the jointly meromorphic continuation
  of `complexHurwitzSeries` and its regularized product `(s - 1) * complexHurwitzZeta s c`.
* `TauCeti.analyticOnNhd_complexHurwitzZeta`, `TauCeti.analyticOnNhd_complexHurwitzReg`: joint
  analyticity on `{p | p.1 ≠ 1 ∧ 0 < p.2.re}` and `{p | 0 < p.2.re}`.
* `TauCeti.complexHurwitzZeta_eq_complexHurwitzSeries`,
  `TauCeti.eq_complexHurwitzZeta_of_analyticOnNhd`: agreement with `complexHurwitzSeries` on
  `1 < s.re`, `0 < c.re` and uniqueness of analytic continuation to `{1}ᶜ`.
* `TauCeti.complexHurwitzReg_one`, `TauCeti.tendsto_sub_one_mul_complexHurwitzZeta_nhdsNE_one`:
  simple pole at `s = 1` with residue `1`.
* `TauCeti.complexHurwitzZeta_neg_nat`: `-B_{m + 1}(c) / (m + 1)` at all nonpositive integers `-m`
  (including `m = 0`).
* `TauCeti.complexHurwitzZeta_add_one`, `TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta`,
  `HurwitzZeta.hurwitzZeta_zero_of_mem_Ioc`, `ZMod.LFunction_eq_sum_Icc_complexHurwitzZeta`,
  `DirichletCharacter.LFunction_eq_sum_Icc_complexHurwitzZeta`: analytic-uniqueness identities off
  `s = 1`.
* `TauCeti.complexHurwitzContinuation_exists`: existential summary bundling joint differentiability,
  series agreement, simple pole at `s = 1`, and Bernoulli polynomial special values.

## References

* T. M. Apostol, *Introduction to Analytic Number Theory*, Springer (1976), §§12.4–12.11.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  24 (2012), 49–84, §9.
* NIST Digital Library of Mathematical Functions, §25.11, <https://dlmf.nist.gov/25.11>.
-/

public section

open Complex Filter MeasureTheory Metric Real Set Topology
open scoped BigOperators

namespace TauCeti

/-! ### Entire reciprocal-Gamma difference quotients -/

/-- The entire quotient `s ↦ (Complex.Gamma s)⁻¹ / (s + j)`, extended across the simple zero of
`(Complex.Gamma s)⁻¹` at `s = -j` via `dslope`. -/
noncomputable def invGammaDSlope (j : ℕ) : ℂ → ℂ :=
  dslope (fun s : ℂ ↦ (Complex.Gamma s)⁻¹) (-(j : ℂ))

/-- Unfolding lemma for `invGammaDSlope`. -/
theorem invGammaDSlope_def (j : ℕ) :
    invGammaDSlope j = dslope (fun s : ℂ ↦ (Complex.Gamma s)⁻¹) (-(j : ℂ)) := (rfl)

/-- `invGammaDSlope j` is analytic at every complex point `s`. -/
@[fun_prop]
theorem analyticAt_invGammaDSlope (j : ℕ) (s : ℂ) : AnalyticAt ℂ (invGammaDSlope j) s :=
  (Complex.differentiable_one_div_Gamma.analyticAt _).dslope (-(j : ℂ))

/-- `invGammaDSlope j` is an entire function on `ℂ`. -/
@[fun_prop]
theorem differentiable_invGammaDSlope (j : ℕ) : Differentiable ℂ (invGammaDSlope j) :=
  fun s ↦ (analyticAt_invGammaDSlope j s).differentiableAt

/-- Away from `-j`, `invGammaDSlope j s = (Complex.Gamma s)⁻¹ / (s + j)`. -/
theorem invGammaDSlope_of_ne (j : ℕ) {s : ℂ} (hs : s ≠ -(j : ℂ)) :
    invGammaDSlope j s = (Complex.Gamma s)⁻¹ / (s + j) := by
  rw [invGammaDSlope_def, dslope_of_ne _ hs, slope_def_field, Complex.Gamma_neg_nat_eq_zero,
    inv_zero, sub_zero, sub_neg_eq_add]

/-- At `s = -j`, `invGammaDSlope j (-j)` equals the derivative `(-1) ^ j * j!` of
`(Complex.Gamma s)⁻¹`. -/
@[simp]
theorem invGammaDSlope_neg_nat_self (j : ℕ) :
    invGammaDSlope j (-(j : ℂ)) = (-1 : ℂ) ^ j * j.factorial := by
  rw [invGammaDSlope_def, dslope_same]
  exact (Complex.hasDerivAt_inv_Gamma_neg_nat j).deriv

/-- At any other nonpositive integer `-m` (`m ≠ j`), `invGammaDSlope j (-m) = 0`. -/
theorem invGammaDSlope_neg_nat_of_ne {j m : ℕ} (hm : m ≠ j) :
    invGammaDSlope j (-(m : ℂ)) = 0 := by
  have hne : -(m : ℂ) ≠ -(j : ℂ) := fun h ↦ hm (Nat.cast_injective (neg_inj.mp h))
  rw [invGammaDSlope_of_ne j hne, Complex.Gamma_neg_nat_eq_zero, inv_zero, zero_div]

/-! ### Near and tail Mellin integrals -/

/-- The `M`-th subtracted near Mellin integral
`∫ t in Ioc 0 1, t ^ (s + M - 1) * hurwitzBernoulliRemainderQuot M (c, t)`, which converges and is
jointly analytic for `-(M : ℝ) < s.re` and all `c : ℂ`. -/
noncomputable def hurwitzNearIntegral (M : ℕ) (p : ℂ × ℂ) : ℂ :=
  ∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (p.1 + (M : ℂ) - 1) * hurwitzBernoulliRemainderQuot M (p.2, t)

/-- Unfolding lemma for `hurwitzNearIntegral`. -/
theorem hurwitzNearIntegral_def (M : ℕ) (p : ℂ × ℂ) :
    hurwitzNearIntegral M p =
      ∫ t : ℝ in Ioc 0 1,
        (t : ℂ) ^ (p.1 + (M : ℂ) - 1) * hurwitzBernoulliRemainderQuot M (p.2, t) := (rfl)

/-- Integrability of the `M`-th near Mellin integrand on `(0, 1]` for `-(M : ℝ) < p.1.re`. -/
theorem integrableOn_hurwitzNearIntegrand (M : ℕ) {p : ℂ × ℂ} (hs : -(M : ℝ) < p.1.re) :
    IntegrableOn
      (fun t : ℝ ↦ (t : ℂ) ^ (p.1 + (M : ℂ) - 1) * hurwitzBernoulliRemainderQuot M (p.2, t))
      (Ioc 0 1) := by
  have hQ_cont : ContinuousOn (fun t : ℝ ↦ hurwitzBernoulliRemainderQuot M (p.2, t)) (Icc 0 1) := by
    refine (analyticOnNhd_hurwitzBernoulliRemainderQuot M).continuousOn.comp
      (continuous_const.prodMk continuous_ofReal).continuousOn fun t ht ↦ ⟨mem_univ _, ?_⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1]
    linarith [ht.2]
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hQ_cont
  have hr : -1 < (p.1 + (M : ℂ) - 1).re := by
    simp only [sub_re, add_re, natCast_re, one_re]; linarith
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ ↦ (t : ℂ) ^ (p.1 + (M : ℂ) - 1) * hurwitzBernoulliRemainderQuot M (p.2, t))
      (volume.restrict (Ioc 0 1)) :=
    ((intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) hr).1).aestronglyMeasurable.mul
      ((hQ_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
  refine Integrable.mono'
    (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hr).1).const_mul (max B 0))
    hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1, mul_comm]
  exact mul_le_mul_of_nonneg_right
    ((hB t ⟨ht.1.le, ht.2⟩).trans (le_max_left B 0)) (Real.rpow_nonneg ht.1.le _)

private theorem continuousOn_hurwitzNearIntegral (M : ℕ) :
    ContinuousOn (hurwitzNearIntegral M) {p : ℂ × ℂ | -(M : ℝ) < p.1.re} := by
  have hU : IsOpen {p : ℂ × ℂ | -(M : ℝ) < p.1.re} :=
    isOpen_lt continuous_const (continuous_re.comp continuous_fst)
  intro p₀ hp₀
  have hp₀' : -(M : ℝ) < p₀.1.re := hp₀
  set δ : ℝ := (p₀.1.re + (M : ℝ)) / 2 with _hδ_def
  have hδ : 0 < δ := by linarith
  have hK_sub : Metric.closedBall p₀.2 1 ×ˢ Metric.closedBall (0 : ℂ) 1 ⊆
      Set.univ ×ˢ Metric.ball (0 : ℂ) 2 :=
    prod_mono (subset_univ _) (Metric.closedBall_subset_ball one_lt_two)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall p₀.2 1).prod (isCompact_closedBall (0 : ℂ) 1))
    |>.exists_bound_of_continuousOn
    ((analyticOnNhd_hurwitzBernoulliRemainderQuot M).continuousOn.mono hK_sub)
  set B' : ℝ := max B 0
  have hnhds : Metric.ball p₀.1 δ ×ˢ Metric.ball p₀.2 1 ∈ 𝓝 p₀ :=
    prod_mem_nhds (Metric.ball_mem_nhds p₀.1 hδ) (Metric.ball_mem_nhds p₀.2 zero_lt_one)
  refine ContinuousAt.continuousWithinAt <|
    MeasureTheory.continuousAt_of_dominated (bound := fun t : ℝ ↦ B' * t ^ (δ - 1)) ?_ ?_
      (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith)).1).const_mul B')
      ?_
  · filter_upwards [hU.mem_nhds hp₀'] with p hp
    exact (integrableOn_hurwitzNearIntegrand M hp).aestronglyMeasurable
  · filter_upwards [hnhds] with p hp
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hre : δ ≤ p.1.re + (M : ℝ) := by
      have h1 := abs_re_le_norm (p.1 - p₀.1); rw [sub_re] at h1
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 (mem_ball_iff_norm.mp hp.1))).1]
    have ht_ball : (t : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1.le]; exact ht.2
    have hQ_le : ‖hurwitzBernoulliRemainderQuot M (p.2, t)‖ ≤ B' :=
      (hB (p.2, t) ⟨ball_subset_closedBall hp.2, ht_ball⟩).trans (le_max_left B 0)
    have hpow_le : t ^ ((p.1 + (M : ℂ) - 1).re) ≤ t ^ (δ - 1) := by
      refine Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 ?_
      simp only [sub_re, add_re, natCast_re, one_re]; linarith
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1, mul_comm]
    exact mul_le_mul hQ_le hpow_le (Real.rpow_nonneg ht.1.le _) (le_max_right B 0)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hslit : (t : ℂ) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simpa using ht.1))
    have hc1 : ContinuousAt (fun p : ℂ × ℂ ↦ (t : ℂ) ^ (p.1 + (M : ℂ) - 1)) p₀ :=
      continuousAt_const.cpow ((continuousAt_fst.add continuousAt_const).sub continuousAt_const)
        hslit
    have ht_ball : (t : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1.le]; linarith [ht.2]
    exact hc1.mul <|
      ((analyticOnNhd_hurwitzBernoulliRemainderQuot M (p₀.2, t) ⟨mem_univ _, ht_ball⟩)
        |>.continuousAt).comp (f := fun p : ℂ × ℂ ↦ (p.2, (t : ℂ)))
        (continuousAt_snd.prodMk continuousAt_const)

private theorem differentiableAt_hurwitzNearIntegral_fst (M : ℕ) {p₀ : ℂ × ℂ}
    (hp₀ : -(M : ℝ) < p₀.1.re) :
    DifferentiableAt ℂ (fun s ↦ hurwitzNearIntegral M (s, p₀.2)) p₀.1 := by
  set δ : ℝ := (p₀.1.re + (M : ℝ)) / 3 with _hδ_def
  have hδ : 0 < δ := by linarith
  have hQ_cont : ContinuousOn
      (fun t : ℝ ↦ hurwitzBernoulliRemainderQuot M (p₀.2, t)) (Icc 0 1) := by
    refine (analyticOnNhd_hurwitzBernoulliRemainderQuot M).continuousOn.comp
      (continuous_const.prodMk continuous_ofReal).continuousOn fun t ht ↦ ⟨mem_univ _, ?_⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1]; linarith [ht.2]
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hQ_cont
  set B' : ℝ := max B 0
  have hball : Metric.ball p₀.1 δ ∈ 𝓝 p₀.1 := Metric.ball_mem_nhds p₀.1 hδ
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 1))
    (F := fun s (t : ℝ) ↦
      (t : ℂ) ^ (s + (M : ℂ) - 1) * hurwitzBernoulliRemainderQuot M (p₀.2, t))
    (F' := fun s (t : ℝ) ↦
      (t : ℂ) ^ (s + (M : ℂ) - 1) * Complex.log t * hurwitzBernoulliRemainderQuot M (p₀.2, t))
    (bound := fun t : ℝ ↦ B' * δ⁻¹ * t ^ (δ - 1))
    hball ?_ (integrableOn_hurwitzNearIntegrand M hp₀) ?_ ?_
    (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith)).1).const_mul
      (B' * δ⁻¹)) ?_
  · exact hd.2.differentiableAt
  · filter_upwards [hball] with s hs
    have hsM : -(M : ℝ) < s.re := by
      have h1 := abs_re_le_norm (s - p₀.1); rw [sub_re] at h1
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 (mem_ball_iff_norm.mp hs))).1]
    exact (integrableOn_hurwitzNearIntegrand M (p := (s, p₀.2)) hsM).aestronglyMeasurable
  · have hr₀ : -1 < (p₀.1 + (M : ℂ) - 1).re := by
      simp only [sub_re, add_re, natCast_re, one_re]; linarith
    refine (((intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) hr₀).1
        |>.aestronglyMeasurable).mul ?_).mul
      ((hQ_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    exact (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable.congr <| by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Complex.ofReal_log ht.1.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht s hs
    have hs2δ : 2 * δ ≤ s.re + (M : ℝ) := by
      have h1 := abs_re_le_norm (s - p₀.1); rw [sub_re] at h1
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 (mem_ball_iff_norm.mp hs))).1]
    have hlog_le : ‖Complex.log (t : ℂ)‖ ≤ δ⁻¹ * t ^ (-δ) := by
      rw [← Complex.ofReal_log ht.1.le, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (Real.log_nonpos ht.1.le ht.2)]
      have hle := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht.1 (-δ))
      rw [Real.log_rpow ht.1] at hle
      exact (le_inv_mul_iff₀ hδ).mpr (by linarith)
    have hpow_le : t ^ ((s + (M : ℂ) - 1).re) ≤ t ^ (2 * δ - 1) := by
      refine Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 ?_
      simp only [sub_re, add_re, natCast_re, one_re]; linarith
    have hQ_le : ‖hurwitzBernoulliRemainderQuot M (p₀.2, t)‖ ≤ B' :=
      (hB t ⟨ht.1.le, ht.2⟩).trans (le_max_left B 0)
    rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1]
    calc t ^ (s + (M : ℂ) - 1).re * ‖Complex.log (t : ℂ)‖ *
          ‖hurwitzBernoulliRemainderQuot M (p₀.2, t)‖
        ≤ t ^ (2 * δ - 1) * (δ⁻¹ * t ^ (-δ)) * B' :=
          mul_le_mul (mul_le_mul hpow_le hlog_le (norm_nonneg _) (Real.rpow_nonneg ht.1.le _))
            hQ_le (norm_nonneg _)
            (mul_nonneg (Real.rpow_nonneg ht.1.le _)
              (mul_nonneg (inv_nonneg.mpr hδ.le) (Real.rpow_nonneg ht.1.le _)))
      _ = B' * δ⁻¹ * (t ^ (2 * δ - 1) * t ^ (-δ)) := by ring
      _ = B' * δ⁻¹ * t ^ (δ - 1) := by rw [← Real.rpow_add ht.1]; ring_nf
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht s _
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have hd1 : HasDerivAt (fun s' : ℂ ↦ s' + (M : ℂ) - 1) 1 s := by
      simpa using ((hasDerivAt_id s).add_const (M : ℂ)).sub_const (1 : ℂ)
    simpa [one_mul] using (hd1.const_cpow (Or.inl ht0)).mul_const
      (hurwitzBernoulliRemainderQuot M (p₀.2, t))

private theorem differentiableAt_hurwitzNearIntegral_snd (M : ℕ) {p₀ : ℂ × ℂ}
    (hp₀ : -(M : ℝ) < p₀.1.re) :
    DifferentiableAt ℂ (fun c ↦ hurwitzNearIntegral M (p₀.1, c)) p₀.2 := by
  let φ : ℝ → ℂ := fun t ↦ ((max 0 (min 1 t) : ℝ) : ℂ)
  have hφ_cont : Continuous φ :=
    continuous_ofReal.comp (continuous_const.max (continuous_const.min continuous_id))
  have hφ_mem (t : ℝ) : φ t ∈ Metric.closedBall (0 : ℂ) 1 := by
    have h0 : 0 ≤ max (0 : ℝ) (min 1 t) := le_max_left 0 _
    have h1 : max (0 : ℝ) (min 1 t) ≤ 1 := max_le zero_le_one (min_le_left 1 t)
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg h0]; exact h1
  have hr₀ : -1 < (p₀.1 + (M : ℂ) - 1).re := by
    simp only [sub_re, add_re, natCast_re, one_re]; linarith
  have han := analyticAt_integral_smul (μ := volume.restrict (Ioc 0 1))
    (K := Metric.closedBall (0 : ℂ) 1) (p := p₀.2)
    (f := hurwitzBernoulliRemainderQuot M)
    (g := fun t : ℝ ↦ (t : ℂ) ^ (p₀.1 + (M : ℂ) - 1))
    (isCompact_closedBall (0 : ℂ) 1) hφ_cont hφ_mem
    (fun y hy ↦ analyticOnNhd_hurwitzBernoulliRemainderQuot M (p₀.2, y)
      ⟨mem_univ _, Metric.closedBall_subset_ball one_lt_two hy⟩)
    ((intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) hr₀).1)
  refine han.differentiableAt.congr_of_eventuallyEq <| Eventually.of_forall fun c ↦ ?_
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
  simp [φ, min_eq_right ht.2, max_eq_right ht.1.le, smul_eq_mul]

/-- Joint analyticity of `hurwitzNearIntegral M` on `{p : ℂ × ℂ | -(M : ℝ) < p.1.re}`. -/
theorem analyticOnNhd_hurwitzNearIntegral (M : ℕ) :
    AnalyticOnNhd ℂ (hurwitzNearIntegral M) {p : ℂ × ℂ | -(M : ℝ) < p.1.re} := by
  let g : (Fin 2 → ℂ) → ℂ := fun v ↦ hurwitzNearIntegral M (v 0, v 1)
  have hproj : Continuous (fun v : Fin 2 → ℂ ↦ (v 0, v 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hV : IsOpen {v : Fin 2 → ℂ | -(M : ℝ) < (v 0).re} :=
    isOpen_lt continuous_const (continuous_re.comp (continuous_apply 0))
  have hg : AnalyticOnNhd ℂ g {v : Fin 2 → ℂ | -(M : ℝ) < (v 0).re} := by
    refine ((continuousOn_hurwitzNearIntegral M).comp hproj.continuousOn fun _ hv ↦ hv)
      |>.analyticOnNhd_of_differentiableAt_update hV fun v hv i ↦ ?_
    fin_cases i
    · simpa [g] using differentiableAt_hurwitzNearIntegral_fst M (p₀ := (v 0, v 1)) hv
    · simpa [g] using differentiableAt_hurwitzNearIntegral_snd M (p₀ := (v 0, v 1)) hv
  intro p hp
  have hpai : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ ![q.1, q.2]) p :=
    analyticAt_pi_iff.mpr fun i ↦ by fin_cases i <;> [exact analyticAt_fst; exact analyticAt_snd]
  exact (hg ![p.1, p.2] hp).comp (f := fun q : ℂ × ℂ ↦ ![q.1, q.2]) hpai

private noncomputable def hurwitzTailIntegrand (p : ℂ × ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (p.1 - 1) * Complex.exp (-p.2 * t) / (1 - Complex.exp (-t))

/-- The Hurwitz tail Mellin integral
`∫ t in Ioi 1, t ^ (s - 1) * exp (-c * t) / (1 - exp (-t))`, which converges rapidly and is
jointly analytic for all `s : ℂ` and `0 < c.re`. -/
noncomputable def hurwitzTailIntegral (p : ℂ × ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 1, (t : ℂ) ^ (p.1 - 1) * Complex.exp (-p.2 * t) / (1 - Complex.exp (-t))

/-- Unfolding lemma for `hurwitzTailIntegral`. -/
theorem hurwitzTailIntegral_def (p : ℂ × ℂ) :
    hurwitzTailIntegral p =
      ∫ t : ℝ in Ioi 1,
        (t : ℂ) ^ (p.1 - 1) * Complex.exp (-p.2 * t) / (1 - Complex.exp (-t)) := (rfl)

private theorem norm_hurwitzTailIntegrand_le {p : ℂ × ℂ} {t A η : ℝ}
    (ht : 1 < t) (hs : (p.1 - 1).re ≤ A) (hc : η ≤ p.2.re) :
    ‖hurwitzTailIntegrand p t‖ ≤ (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-η * t)) := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hexp_lt : Real.exp (-t) < Real.exp (-1) := Real.exp_lt_exp.mpr (by linarith)
  have hexp1_lt : Real.exp (-1) < 1 := by simp
  have hden_norm : 1 - Real.exp (-1) ≤ ‖(1 : ℂ) - Complex.exp (-(t : ℂ))‖ := by
    have hcast : (1 : ℂ) - Complex.exp (-(t : ℂ)) = ((1 - Real.exp (-t) : ℝ) : ℂ) := by
      rw [ofReal_sub, ofReal_one, ofReal_exp, ofReal_neg]
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  have hden : ‖((1 : ℂ) - Complex.exp (-(t : ℂ)))⁻¹‖ ≤ (1 - Real.exp (-1))⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ (by linarith) hden_norm
  have hpow : t ^ (p.1 - 1).re ≤ t ^ A := Real.rpow_le_rpow_of_exponent_le ht.le hs
  have hexp : ‖Complex.exp (-p.2 * t)‖ ≤ Real.exp (-η * t) := by
    rw [Complex.norm_exp]
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  rw [hurwitzTailIntegrand, div_eq_mul_inv, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
  calc t ^ (p.1 - 1).re * ‖Complex.exp (-p.2 * t)‖ * ‖((1 : ℂ) - Complex.exp (-(t : ℂ)))⁻¹‖
      ≤ t ^ A * Real.exp (-η * t) * (1 - Real.exp (-1))⁻¹ :=
        mul_le_mul (mul_le_mul hpow hexp (norm_nonneg _) (Real.rpow_nonneg ht0.le _))
          hden (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_nonneg _))
    _ = (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-η * t)) := by ring

/-- Integrability of the Hurwitz tail integrand on `(1, ∞)` for `0 < p.2.re`. -/
theorem integrableOn_hurwitzTailIntegrand {p : ℂ × ℂ} (hc : 0 < p.2.re) :
    IntegrableOn
      (fun t : ℝ ↦ (t : ℂ) ^ (p.1 - 1) * Complex.exp (-p.2 * t) / (1 - Complex.exp (-t)))
      (Ioi 1) := by
  set A : ℝ := max (p.1.re - 1) 0 with _hA_def
  have hA : -1 < A := by linarith [le_max_right (p.1.re - 1) 0]
  have hcont : ContinuousOn (hurwitzTailIntegrand p) (Ioi 1) := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hslit : (t : ℂ) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simpa using ht0))
    have hden : (1 : ℂ) - Complex.exp (-(t : ℂ)) ≠ 0 := by
      intro h
      have hcast := congrArg Complex.re h
      have hexp : (Complex.exp (-(t : ℂ))).re = Real.exp (-t) := by
        rw [← ofReal_neg, ← ofReal_exp, ofReal_re]
      simp only [sub_re, one_re, zero_re, hexp] at hcast
      have hneg : -t < 0 := by linarith
      linarith [Real.exp_lt_one_iff.mpr hneg]
    exact (((continuous_ofReal.continuousAt.cpow continuousAt_const hslit).mul
      ((continuousAt_const.mul continuous_ofReal.continuousAt).cexp)).div
      (continuousAt_const.sub (continuous_ofReal.continuousAt.neg.cexp)) hden).continuousWithinAt
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A) (b := p.2.re) hA one_pos hc
  simp only [Real.rpow_one] at h0
  refine Integrable.mono'
    ((h0.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul (1 - Real.exp (-1))⁻¹)
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_hurwitzTailIntegrand_le ht (by rw [sub_re, one_re]; exact le_max_left _ 0) le_rfl

private theorem continuousOn_hurwitzTailIntegral :
    ContinuousOn hurwitzTailIntegral {p : ℂ × ℂ | 0 < p.2.re} := by
  have hU : IsOpen {p : ℂ × ℂ | 0 < p.2.re} :=
    isOpen_lt continuous_const (continuous_re.comp continuous_snd)
  intro p₀ hp₀
  have hp₀' : 0 < p₀.2.re := hp₀
  set η : ℝ := p₀.2.re / 2 with _hη_def
  have hη : 0 < η := by linarith
  set A : ℝ := |p₀.1.re| + 1 with _hA_def
  have hA : -1 < A := by linarith [abs_nonneg p₀.1.re]
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A) (b := η) hA one_pos hη
  simp only [Real.rpow_one] at h0
  have hnhds : Metric.ball p₀.1 1 ×ˢ Metric.ball p₀.2 η ∈ 𝓝 p₀ :=
    prod_mem_nhds (Metric.ball_mem_nhds p₀.1 zero_lt_one) (Metric.ball_mem_nhds p₀.2 hη)
  refine ContinuousAt.continuousWithinAt <|
    MeasureTheory.continuousAt_of_dominated
      (bound := fun t : ℝ ↦ (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-η * t))) ?_ ?_
      ((h0.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _) ?_
  · filter_upwards [hU.mem_nhds hp₀'] with p hp
    exact (integrableOn_hurwitzTailIntegrand hp).aestronglyMeasurable
  · filter_upwards [hnhds] with p hp
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hs_le : (p.1 - 1).re ≤ A := by
      have h1 := abs_re_le_norm (p.1 - p₀.1); rw [sub_re] at h1
      simp only [sub_re, one_re, A]
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 (mem_ball_iff_norm.mp hp.1))).2, le_abs_self p₀.1.re]
    have hc_ge : η ≤ p.2.re := by
      have h1 := abs_re_le_norm (p.2 - p₀.2); rw [sub_re] at h1
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 (mem_ball_iff_norm.mp hp.2))).1]
    exact norm_hurwitzTailIntegrand_le ht hs_le hc_ge
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hslit : (t : ℂ) ∈ slitPlane :=
      mem_slitPlane_iff.mpr (Or.inl (by simpa using zero_lt_one.trans ht))
    exact ((continuousAt_const.cpow (continuousAt_fst.sub continuousAt_const) hslit).mul
      ((continuousAt_snd.neg.mul continuousAt_const).cexp)).div_const _

private theorem differentiableAt_hurwitzTailIntegral_fst {p₀ : ℂ × ℂ} (hp₀ : 0 < p₀.2.re) :
    DifferentiableAt ℂ (fun s ↦ hurwitzTailIntegral (s, p₀.2)) p₀.1 := by
  set A : ℝ := |p₀.1.re| + 2 with _hA_def
  have hA : -1 < A := by linarith [abs_nonneg p₀.1.re]
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A) (b := p₀.2.re) hA one_pos hp₀
  simp only [Real.rpow_one] at h0
  have hball : Metric.ball p₀.1 1 ∈ 𝓝 p₀.1 := Metric.ball_mem_nhds p₀.1 zero_lt_one
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 1))
    (F := fun s (t : ℝ) ↦ hurwitzTailIntegrand (s, p₀.2) t)
    (F' := fun s (t : ℝ) ↦ hurwitzTailIntegrand (s, p₀.2) t * Complex.log t)
    (bound := fun t : ℝ ↦ (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-p₀.2.re * t)))
    hball
    (Eventually.of_forall fun s ↦
      (integrableOn_hurwitzTailIntegrand (p := (s, p₀.2)) hp₀).aestronglyMeasurable)
    (integrableOn_hurwitzTailIntegrand hp₀) ?_ ?_
    ((h0.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _) ?_
  · exact hd.2.differentiableAt
  · refine (integrableOn_hurwitzTailIntegrand hp₀).aestronglyMeasurable.mul ?_
    refine (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Complex.ofReal_log (zero_lt_one.trans ht).le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hs_le : (s - 1).re ≤ A - 1 := by
      have h1 := abs_re_le_norm (s - p₀.1); rw [sub_re] at h1
      simp only [sub_re, one_re, A]
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 (mem_ball_iff_norm.mp hs))).2, le_abs_self p₀.1.re]
    have hlog : ‖Complex.log (t : ℂ)‖ ≤ t := by
      rw [← Complex.ofReal_log ht0.le, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_nonneg ht.le)]
      linarith [Real.log_le_sub_one_of_pos ht0]
    have hbase := norm_hurwitzTailIntegrand_le (p := (s, p₀.2)) ht hs_le le_rfl
    have hexp_lt : Real.exp (-1) < 1 := by simp
    have hexp1 : 0 ≤ (1 - Real.exp (-1))⁻¹ * (t ^ (A - 1) * Real.exp (-p₀.2.re * t)) :=
      mul_nonneg (inv_nonneg.mpr (by linarith)) (by positivity)
    rw [norm_mul]
    calc ‖hurwitzTailIntegrand (s, p₀.2) t‖ * ‖Complex.log (t : ℂ)‖
        ≤ ((1 - Real.exp (-1))⁻¹ * (t ^ (A - 1) * Real.exp (-p₀.2.re * t))) * t :=
          mul_le_mul hbase hlog (norm_nonneg _) hexp1
      _ = (1 - Real.exp (-1))⁻¹ * ((t ^ (A - 1) * t) * Real.exp (-p₀.2.re * t)) := by ring
      _ = (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-p₀.2.re * t)) := by
          rw [← Real.rpow_add_one ht0.ne', sub_add_cancel]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    have hd1 : HasDerivAt (fun s' : ℂ ↦ s' - 1) 1 s := (hasDerivAt_id s).sub_const 1
    have hd2 := (hd1.const_cpow (Or.inl ht0)).mul_const
      (Complex.exp (-p₀.2 * t) / (1 - Complex.exp (-t)))
    have hfun : (fun s' : ℂ ↦ hurwitzTailIntegrand (s', p₀.2) t) =
        fun s' : ℂ ↦ (t : ℂ) ^ (s' - 1) * (Complex.exp (-p₀.2 * t) / (1 - Complex.exp (-t))) := by
      ext s'; dsimp only [hurwitzTailIntegrand]; ring
    have hval : hurwitzTailIntegrand (s, p₀.2) t * Complex.log t =
        (t : ℂ) ^ (s - 1) * Complex.log t * 1 *
          (Complex.exp (-p₀.2 * t) / (1 - Complex.exp (-t))) := by
      dsimp only [hurwitzTailIntegrand]; ring
    rw [hfun, hval]
    exact hd2

private theorem differentiableAt_hurwitzTailIntegral_snd {p₀ : ℂ × ℂ} (hp₀ : 0 < p₀.2.re) :
    DifferentiableAt ℂ (fun c ↦ hurwitzTailIntegral (p₀.1, c)) p₀.2 := by
  set η : ℝ := p₀.2.re / 2 with _hη_def
  have hη : 0 < η := by linarith
  set A : ℝ := max (p₀.1.re - 1) 0 + 1 with _hA_def
  have hA : -1 < A := by linarith [le_max_right (p₀.1.re - 1) 0]
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A) (b := η) hA one_pos hη
  simp only [Real.rpow_one] at h0
  have hball : Metric.ball p₀.2 η ∈ 𝓝 p₀.2 := Metric.ball_mem_nhds p₀.2 hη
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 1))
    (F := fun c (t : ℝ) ↦ hurwitzTailIntegrand (p₀.1, c) t)
    (F' := fun c (t : ℝ) ↦
      (t : ℂ) ^ (p₀.1 - 1) * (Complex.exp (-c * t) * -(t : ℂ)) / (1 - Complex.exp (-t)))
    (bound := fun t : ℝ ↦ (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-η * t)))
    hball ?_ (integrableOn_hurwitzTailIntegrand hp₀) ?_ ?_
    ((h0.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _) ?_
  · exact hd.2.differentiableAt
  · filter_upwards [hball] with c hc
    have hc_re : 0 < c.re := by
      have h1 := abs_re_le_norm (c - p₀.2); rw [sub_re] at h1
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 (mem_ball_iff_norm.mp hc))).1]
    exact (integrableOn_hurwitzTailIntegrand (p := (p₀.1, c)) hc_re).aestronglyMeasurable
  · exact ((integrableOn_hurwitzTailIntegrand hp₀).aestronglyMeasurable.mul
        Complex.measurable_ofReal.neg.aestronglyMeasurable).congr <| by
      filter_upwards with t; dsimp only [hurwitzTailIntegrand, Pi.mul_apply, Pi.neg_apply]; ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht c hc
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hc_ge : η ≤ c.re := by
      have h1 := abs_re_le_norm (c - p₀.2); rw [sub_re] at h1
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 (mem_ball_iff_norm.mp hc))).1]
    have hs_le : (p₀.1 - 1).re ≤ A - 1 := by
      simp only [sub_re, one_re, A]; linarith [le_max_left (p₀.1.re - 1) 0]
    have hbase := norm_hurwitzTailIntegrand_le (p := (p₀.1, c)) ht hs_le hc_ge
    have heq : (t : ℂ) ^ (p₀.1 - 1) * (Complex.exp (-c * t) * -(t : ℂ)) /
        (1 - Complex.exp (-t)) = hurwitzTailIntegrand (p₀.1, c) t * -(t : ℂ) := by
      dsimp only [hurwitzTailIntegrand]; ring
    rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    calc ‖hurwitzTailIntegrand (p₀.1, c) t‖ * t
        ≤ ((1 - Real.exp (-1))⁻¹ * (t ^ (A - 1) * Real.exp (-η * t))) * t :=
          mul_le_mul_of_nonneg_right hbase ht0.le
      _ = (1 - Real.exp (-1))⁻¹ * ((t ^ (A - 1) * t) * Real.exp (-η * t)) := by ring
      _ = (1 - Real.exp (-1))⁻¹ * (t ^ A * Real.exp (-η * t)) := by
          rw [← Real.rpow_add_one ht0.ne', sub_add_cancel]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ c _
    have hd1 : HasDerivAt (fun c' : ℂ ↦ -c' * (t : ℂ)) (-(t : ℂ)) c := by
      simpa using ((hasDerivAt_id c).neg.mul_const (t : ℂ))
    exact ((hd1.cexp.const_mul ((t : ℂ) ^ (p₀.1 - 1))).div_const (1 - Complex.exp (-t)))

/-- Joint analyticity of `hurwitzTailIntegral` on `{p : ℂ × ℂ | 0 < p.2.re}`. -/
theorem analyticOnNhd_hurwitzTailIntegral :
    AnalyticOnNhd ℂ hurwitzTailIntegral {p : ℂ × ℂ | 0 < p.2.re} := by
  let g : (Fin 2 → ℂ) → ℂ := fun v ↦ hurwitzTailIntegral (v 0, v 1)
  have hproj : Continuous (fun v : Fin 2 → ℂ ↦ (v 0, v 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hV : IsOpen {v : Fin 2 → ℂ | 0 < (v 1).re} :=
    isOpen_lt continuous_const (continuous_re.comp (continuous_apply 1))
  have hg : AnalyticOnNhd ℂ g {v : Fin 2 → ℂ | 0 < (v 1).re} := by
    refine (continuousOn_hurwitzTailIntegral.comp hproj.continuousOn fun _ hv ↦ hv)
      |>.analyticOnNhd_of_differentiableAt_update hV fun v hv i ↦ ?_
    fin_cases i
    · simpa [g] using differentiableAt_hurwitzTailIntegral_fst (p₀ := (v 0, v 1)) hv
    · simpa [g] using differentiableAt_hurwitzTailIntegral_snd (p₀ := (v 0, v 1)) hv
  intro p hp
  have hpai : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ ![q.1, q.2]) p :=
    analyticAt_pi_iff.mpr fun i ↦ by fin_cases i <;> [exact analyticAt_fst; exact analyticAt_snd]
  exact (hg ![p.1, p.2] hp).comp (f := fun q : ℂ × ℂ ↦ ![q.1, q.2]) hpai

/-! ### Taylor-subtracted Mellin approximations and overlap gluing -/

/-- The `M`-th Taylor-subtracted Mellin continuation of the Hurwitz zeta function on
`-(M : ℝ) < s.re`, `s ≠ 1`, `0 < c.re`. -/
noncomputable def hurwitzApprox (M : ℕ) (p : ℂ × ℂ) : ℂ :=
  (Complex.Gamma p.1)⁻¹ * (hurwitzNearIntegral M p + hurwitzTailIntegral p + (p.1 - 1)⁻¹) +
    ∑ j ∈ Finset.range M, invGammaDSlope j p.1 * hurwitzBernoulliCoeff (j + 1) p.2

/-- The `M`-th regularized approximation `(s - 1) * hurwitzApprox M (s, c)`, entire in `s` on
`-(M : ℝ) < s.re` (including across `s = 1`) for `0 < c.re`. -/
noncomputable def hurwitzRegApprox (M : ℕ) (p : ℂ × ℂ) : ℂ :=
  (Complex.Gamma p.1)⁻¹ *
      ((p.1 - 1) * (hurwitzNearIntegral M p + hurwitzTailIntegral p) + 1) +
    (p.1 - 1) * ∑ j ∈ Finset.range M, invGammaDSlope j p.1 * hurwitzBernoulliCoeff (j + 1) p.2

/-- Away from `s = 1`, `hurwitzRegApprox M (s, c) = (s - 1) * hurwitzApprox M (s, c)`. -/
theorem hurwitzRegApprox_eq_sub_one_mul (M : ℕ) {p : ℂ × ℂ} (hs : p.1 ≠ 1) :
    hurwitzRegApprox M p = (p.1 - 1) * hurwitzApprox M p := by
  have hsub : p.1 - 1 ≠ 0 := sub_ne_zero.mpr hs
  dsimp only [hurwitzRegApprox, hurwitzApprox]
  field_simp [hsub]

/-- Joint analyticity of `hurwitzApprox M` on `-(M : ℝ) < s.re`, `s ≠ 1`, `0 < c.re`. -/
theorem analyticOnNhd_hurwitzApprox (M : ℕ) :
    AnalyticOnNhd ℂ (hurwitzApprox M)
      {p : ℂ × ℂ | -(M : ℝ) < p.1.re ∧ p.1 ≠ 1 ∧ 0 < p.2.re} := by
  intro p hp
  have hinvG : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ (Complex.Gamma q.1)⁻¹) p :=
    (Complex.differentiable_one_div_Gamma.analyticAt p.1).comp analyticAt_fst
  have hnear : AnalyticAt ℂ (hurwitzNearIntegral M) p :=
    analyticOnNhd_hurwitzNearIntegral M p hp.1
  have htail : AnalyticAt ℂ hurwitzTailIntegral p :=
    analyticOnNhd_hurwitzTailIntegral p hp.2.2
  have hpole : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ (q.1 - 1)⁻¹) p :=
    (analyticAt_fst.sub analyticAt_const).inv (sub_ne_zero.mpr hp.2.1)
  have hsum : AnalyticAt ℂ
      (fun q : ℂ × ℂ ↦ ∑ j ∈ Finset.range M,
        invGammaDSlope j q.1 * hurwitzBernoulliCoeff (j + 1) q.2) p :=
    Finset.analyticAt_fun_sum _ fun j _ ↦
      ((analyticAt_invGammaDSlope j p.1).comp analyticAt_fst).mul
        ((analyticAt_hurwitzBernoulliCoeff (j + 1) p.2).comp analyticAt_snd)
  exact (hinvG.mul ((hnear.add htail).add hpole)).add hsum

/-- Joint analyticity of `hurwitzRegApprox M` on `-(M : ℝ) < s.re`, `0 < c.re` (including across
`s = 1`). -/
theorem analyticOnNhd_hurwitzRegApprox (M : ℕ) :
    AnalyticOnNhd ℂ (hurwitzRegApprox M)
      {p : ℂ × ℂ | -(M : ℝ) < p.1.re ∧ 0 < p.2.re} := by
  intro p hp
  have hinvG : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ (Complex.Gamma q.1)⁻¹) p :=
    (Complex.differentiable_one_div_Gamma.analyticAt p.1).comp analyticAt_fst
  have hnear : AnalyticAt ℂ (hurwitzNearIntegral M) p :=
    analyticOnNhd_hurwitzNearIntegral M p hp.1
  have htail : AnalyticAt ℂ hurwitzTailIntegral p :=
    analyticOnNhd_hurwitzTailIntegral p hp.2
  have hsub : AnalyticAt ℂ (fun q : ℂ × ℂ ↦ q.1 - 1) p :=
    analyticAt_fst.sub analyticAt_const
  have hsum : AnalyticAt ℂ
      (fun q : ℂ × ℂ ↦ ∑ j ∈ Finset.range M,
        invGammaDSlope j q.1 * hurwitzBernoulliCoeff (j + 1) q.2) p :=
    Finset.analyticAt_fun_sum _ fun j _ ↦
      ((analyticAt_invGammaDSlope j p.1).comp analyticAt_fst).mul
        ((analyticAt_hurwitzBernoulliCoeff (j + 1) p.2).comp analyticAt_snd)
  exact (hinvG.mul ((hsub.mul (hnear.add htail)).add analyticAt_const)).add (hsub.mul hsum)

/-- Euler–Mellin integral representation of the complex-parameter Hurwitz series: for `1 < s.re`
and `0 < c.re`,
`∫ t in Ioi 0, t ^ (s - 1) * exp (-c * t) / (1 - exp (-t)) = Γ(s) * complexHurwitzSeries s c`. -/
theorem integral_Ioi_cpow_mul_exp_div_one_sub_exp {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * Complex.exp (-c * t) / (1 - Complex.exp (-t))) =
      Complex.Gamma s * complexHurwitzSeries s c := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  let F : ℕ → ℝ → ℂ := fun n t ↦ (t : ℂ) ^ (s - 1) * Complex.exp (-(((n : ℂ) + c) * t))
  have hnc_re (n : ℕ) : 0 < ((n : ℂ) + c).re := by
    simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hF_int (n : ℕ) : Integrable (F n) (volume.restrict (Ioi 0)) :=
    Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hs0 (hnc_re n)
  have hF_norm_sum : Summable fun n : ℕ ↦ ∫ t : ℝ in Ioi 0, ‖F n t‖ := by
    have hnorm_eq (n : ℕ) :
        (∫ t : ℝ in Ioi 0, ‖F n t‖) = ((1 / ((n : ℝ) + c.re)) ^ s.re) * Real.Gamma s.re := by
      rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs0 (by simpa using hnc_re n)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      have ht' : 0 < t := ht
      simp only [F, norm_mul, norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_exp,
        neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re, one_re,
        add_re, natCast_re]
    simp_rw [hnorm_eq]
    refine Summable.mul_right _ ?_
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
      ((summable_nat_add_iff 1).mpr (Real.summable_nat_rpow (p := -s.re).mpr (by linarith)))
    have hn1 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + c.re := by linarith
    calc (1 / (((n + 1 : ℕ) : ℝ) + c.re)) ^ s.re
        ≤ (1 / ((n + 1 : ℕ) : ℝ)) ^ s.re :=
          Real.rpow_le_rpow (by positivity) (one_div_le_one_div_of_le hn1 hle) hs0.le
      _ = ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
          rw [one_div, Real.inv_rpow hn1.le, Real.rpow_neg hn1.le]
  have htsum_int := MeasureTheory.integral_tsum_of_summable_integral_norm hF_int hF_norm_sum
  have hterm_int (n : ℕ) : (∫ t : ℝ in Ioi 0, F n t) = Complex.Gamma s * ((n : ℂ) + c) ^ (-s) :=
    Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs0 (hnc_re n)
  simp_rw [hterm_int] at htsum_int
  rw [tsum_mul_left, ← complexHurwitzSeries_eq_tsum_cpow s hc] at htsum_int
  rw [htsum_int]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have hr_norm : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
    have ht' : (0 : ℝ) < t := ht
    rw [Complex.norm_exp]; simp only [neg_re, ofReal_re]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom := (hasSum_geometric_of_norm_lt_one hr_norm).tsum_eq
  have hF_rw (n : ℕ) :
      F n t = ((t : ℂ) ^ (s - 1) * Complex.exp (-c * t)) * (Complex.exp (-(t : ℂ))) ^ n := by
    simp only [F, ← Complex.exp_nat_mul]; rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
  simp_rw [hF_rw, tsum_mul_left, hgeom, inv_eq_one_div, mul_one_div]

/-- For `1 < s.re` and `0 < c.re`, the `M = 0` subtracted Mellin approximation equals
`complexHurwitzSeries s c`. -/
theorem hurwitzApprox_zero_eq_complexHurwitzSeries {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    hurwitzApprox 0 (s, c) = complexHurwitzSeries s c := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hs2 : -1 < (s - 2).re := by
    have h2 : (2 : ℂ).re = 2 := by norm_num
    rw [sub_re, h2]; linarith
  have hnear_eq {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
      (t : ℂ) ^ (s - 1) * Complex.exp (-c * t) / (1 - Complex.exp (-t)) =
        (t : ℂ) ^ (s - 2) +
          (t : ℂ) ^ (s + (0 : ℕ) - 1) * hurwitzBernoulliRemainderQuot 0 (c, t) := by
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have ht_ball : (t : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1.le]; linarith [ht.2]
    have hrem := hurwitzBernoulliKernel_sub_sum_eq 0 c ht_ball
    rw [zero_add, Finset.sum_range_one, hurwitzBernoulliCoeff_zero, pow_zero, mul_one,
      pow_one] at hrem
    have hK := eq_add_of_sub_eq' hrem
    have hs_sub : s - 1 = (s - 2) + 1 := by ring
    have hpow1 : (t : ℂ) ^ (s - 1) = (t : ℂ) ^ (s - 2) * (t : ℂ) := by
      rw [hs_sub, cpow_add _ _ ht0, cpow_one]
    have hpow2 : (t : ℂ) ^ (s - 2) * (t : ℂ) = (t : ℂ) ^ (s + (0 : ℕ) - 1) := by
      rw [← hpow1]; simp
    calc (t : ℂ) ^ (s - 1) * Complex.exp (-c * t) / (1 - Complex.exp (-t))
        = (t : ℂ) ^ (s - 2) * ((t : ℂ) * Complex.exp (-c * t) / (1 - Complex.exp (-t))) := by
          rw [hpow1]; ring
      _ = (t : ℂ) ^ (s - 2) * hurwitzBernoulliKernel c t := by
          rw [hurwitzBernoulliKernel_of_ne_zero c ht0]
      _ = (t : ℂ) ^ (s - 2) +
            (t : ℂ) ^ (s + (0 : ℕ) - 1) * hurwitzBernoulliRemainderQuot 0 (c, t) := by
          rw [hK, mul_add, mul_one, ← mul_assoc, hpow2]
  have hint_cpow : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 2)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) hs2).1
  have hint_Ioc : IntegrableOn
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * Complex.exp (-c * t) / (1 - Complex.exp (-t)))
      (Ioc 0 1) :=
    (hint_cpow.add (integrableOn_hurwitzNearIntegrand 0 (p := (s, c)) (by simpa using hs0)))
      |>.congr_fun (fun _ ht ↦ (hnear_eq ht).symm) measurableSet_Ioc
  have hcpow_int : (∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (s - 2)) = (s - 1)⁻¹ := by
    have hs_add : s - 2 + 1 = s - 1 := by ring
    have hs1_ne : s - 2 + 1 ≠ 0 := by
      rw [hs_add]; intro h
      have hre := congrArg Complex.re h
      simp only [sub_re, one_re, zero_re] at hre; linarith
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hs2),
      ofReal_one, one_cpow, ofReal_zero, zero_cpow hs1_ne, sub_zero, one_div, hs_add]
  have hsplit := integral_Ioi_cpow_mul_exp_div_one_sub_exp hs hc
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint_Ioc
      (integrableOn_hurwitzTailIntegrand (p := (s, c)) hc),
    setIntegral_congr_fun measurableSet_Ioc (fun _ ht ↦ hnear_eq ht),
    integral_add hint_cpow (integrableOn_hurwitzNearIntegrand 0 (p := (s, c)) (by simpa using hs0)),
    hcpow_int] at hsplit
  have hGne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have hsplit' : ((s - 1)⁻¹ + hurwitzNearIntegral 0 (s, c)) + hurwitzTailIntegral (s, c) =
      Complex.Gamma s * complexHurwitzSeries s c := hsplit
  have hsum_eq : hurwitzNearIntegral 0 (s, c) + hurwitzTailIntegral (s, c) + (s - 1)⁻¹ =
      Complex.Gamma s * complexHurwitzSeries s c := by linear_combination hsplit'
  rw [hurwitzApprox, Finset.range_zero, Finset.sum_empty, add_zero, hsum_eq,
    ← mul_assoc, inv_mul_cancel₀ hGne, one_mul]

/-- Stepping `M` to `M + 1` in `hurwitzNearIntegral` extracts the `(M + 1)`-st Taylor term
`hurwitzBernoulliCoeff (M + 1) c / (s + M)`. -/
theorem hurwitzNearIntegral_eq_add_succ (M : ℕ) {p : ℂ × ℂ} (hs : -(M : ℝ) < p.1.re) :
    hurwitzNearIntegral M p =
      hurwitzBernoulliCoeff (M + 1) p.2 / (p.1 + M) + hurwitzNearIntegral (M + 1) p := by
  have hr : -1 < (p.1 + (M : ℂ) - 1).re := by
    simp only [sub_re, add_re, natCast_re, one_re]; linarith
  have hs1 : -((M + 1 : ℕ) : ℝ) < p.1.re := by push_cast; linarith
  have hcongr : ∀ t ∈ Ioc (0 : ℝ) 1,
      (t : ℂ) ^ (p.1 + (M : ℂ) - 1) * hurwitzBernoulliRemainderQuot M (p.2, t) =
        hurwitzBernoulliCoeff (M + 1) p.2 * (t : ℂ) ^ (p.1 + (M : ℂ) - 1) +
          (t : ℂ) ^ (p.1 + ((M + 1 : ℕ) : ℂ) - 1) *
            hurwitzBernoulliRemainderQuot (M + 1) (p.2, t) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
    have ht_ball : (t : ℂ) ∈ Metric.ball (0 : ℂ) 2 := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg ht.1.le]; linarith [ht.2]
    have hexp_eq : p.1 + ((M + 1 : ℕ) : ℂ) - 1 = (p.1 + (M : ℂ) - 1) + 1 := by push_cast; ring
    have hpow : (t : ℂ) ^ (p.1 + (M : ℂ) - 1) * (t : ℂ) =
        (t : ℂ) ^ (p.1 + ((M + 1 : ℕ) : ℂ) - 1) := by
      rw [hexp_eq, cpow_add _ _ ht0, cpow_one]
    rw [hurwitzBernoulliRemainderQuot_eq_add_mul M p.2 ht_ball, mul_add, mul_comm _
      (hurwitzBernoulliCoeff (M + 1) p.2), ← mul_assoc, hpow]
  have hint_cpow : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (p.1 + (M : ℂ) - 1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) hr).1
  have hcpow_int : (∫ t : ℝ in Ioc 0 1, (t : ℂ) ^ (p.1 + (M : ℂ) - 1)) = (p.1 + M)⁻¹ := by
    have hr1 : p.1 + (M : ℂ) - 1 + 1 ≠ 0 := by
      rw [sub_add_cancel]; intro h; have hre := congrArg Complex.re h
      simp only [add_re, natCast_re, zero_re] at hre; linarith
    rw [← intervalIntegral.integral_of_le zero_le_one, integral_cpow (Or.inl hr),
      ofReal_one, one_cpow, ofReal_zero, zero_cpow hr1, sub_zero, one_div, sub_add_cancel]
  rw [hurwitzNearIntegral_def, setIntegral_congr_fun measurableSet_Ioc hcongr,
    integral_add (hint_cpow.const_mul _) (integrableOn_hurwitzNearIntegrand (M + 1) hs1),
    integral_const_mul, hcpow_int, div_eq_mul_inv, hurwitzNearIntegral_def]

/-- Overlap agreement: on `-(M : ℝ) < p.1.re`, `hurwitzApprox M p = hurwitzApprox (M + 1) p`. -/
theorem hurwitzApprox_succ (M : ℕ) {p : ℂ × ℂ} (hs : -(M : ℝ) < p.1.re) :
    hurwitzApprox M p = hurwitzApprox (M + 1) p := by
  have hs_ne : p.1 ≠ -(M : ℂ) := by
    intro h; rw [h, neg_re, natCast_re] at hs; exact lt_irrefl _ hs
  dsimp only [hurwitzApprox]
  rw [hurwitzNearIntegral_eq_add_succ M hs, Finset.sum_range_succ, invGammaDSlope_of_ne M hs_ne]
  ring

/-- Overlap agreement for the regularized approximations across `s = 1`. -/
theorem hurwitzRegApprox_succ (M : ℕ) {p : ℂ × ℂ} (hs : -(M : ℝ) < p.1.re) :
    hurwitzRegApprox M p = hurwitzRegApprox (M + 1) p := by
  have hs_ne : p.1 ≠ -(M : ℂ) := by
    intro h; rw [h, neg_re, natCast_re] at hs; exact lt_irrefl _ hs
  dsimp only [hurwitzRegApprox]
  rw [hurwitzNearIntegral_eq_add_succ M hs, Finset.sum_range_succ, invGammaDSlope_of_ne M hs_ne]
  ring

/-- Monotone index agreement for `hurwitzApprox` on `-(M : ℝ) < p.1.re`. -/
theorem hurwitzApprox_eq_of_le {M N : ℕ} (hMN : M ≤ N) {p : ℂ × ℂ} (hs : -(M : ℝ) < p.1.re) :
    hurwitzApprox M p = hurwitzApprox N p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMN
  induction d with
  | zero => simp
  | succ d ih =>
    have hMd : -((M + d : ℕ) : ℝ) < p.1.re := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) d]
    rw [ih (Nat.le_add_right M d), ← Nat.add_assoc, hurwitzApprox_succ (M + d) hMd]

/-- Monotone index agreement for `hurwitzRegApprox` on `-(M : ℝ) < p.1.re`. -/
theorem hurwitzRegApprox_eq_of_le {M N : ℕ} (hMN : M ≤ N) {p : ℂ × ℂ} (hs : -(M : ℝ) < p.1.re) :
    hurwitzRegApprox M p = hurwitzRegApprox N p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMN
  induction d with
  | zero => simp
  | succ d ih =>
    have hMd : -((M + d : ℕ) : ℝ) < p.1.re := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) d]
    rw [ih (Nat.le_add_right M d), ← Nat.add_assoc, hurwitzRegApprox_succ (M + d) hMd]

/-- Any two `hurwitzApprox` stages valid at `p` agree. -/
theorem hurwitzApprox_eq_of_lt (M N : ℕ) {p : ℂ × ℂ}
    (hM : -(M : ℝ) < p.1.re) (hN : -(N : ℝ) < p.1.re) :
    hurwitzApprox M p = hurwitzApprox N p := by
  rcases le_total M N with hMN | hNM
  · exact hurwitzApprox_eq_of_le hMN hM
  · exact (hurwitzApprox_eq_of_le hNM hN).symm

/-- Any two `hurwitzRegApprox` stages valid at `p` agree. -/
theorem hurwitzRegApprox_eq_of_lt (M N : ℕ) {p : ℂ × ℂ}
    (hM : -(M : ℝ) < p.1.re) (hN : -(N : ℝ) < p.1.re) :
    hurwitzRegApprox M p = hurwitzRegApprox N p := by
  rcases le_total M N with hMN | hNM
  · exact hurwitzRegApprox_eq_of_le hMN hM
  · exact (hurwitzRegApprox_eq_of_le hNM hN).symm

/-! ### Global glued continuation `complexHurwitzZeta` and `complexHurwitzReg` -/

/-- The meromorphically continued complex-parameter Hurwitz zeta function `ζ_H(s, c)`, glued from
`hurwitzApprox` by choosing `M = ⌊-s.re⌋₊ + 1` so that `-M < s.re` holds everywhere. -/
noncomputable def complexHurwitzZeta (s c : ℂ) : ℂ :=
  hurwitzApprox (Nat.floor (-s.re) + 1) (s, c)

/-- The entire-in-`s` regularized Hurwitz function `(s - 1) * ζ_H(s, c)`, taking the value `1` at
`s = 1`. -/
noncomputable def complexHurwitzReg (s c : ℂ) : ℂ :=
  hurwitzRegApprox (Nat.floor (-s.re) + 1) (s, c)

/-- On any half-plane `-(M : ℝ) < s.re`, `complexHurwitzZeta s c` agrees with `hurwitzApprox M`. -/
theorem complexHurwitzZeta_eq_hurwitzApprox (M : ℕ) {s : ℂ} (hs : -(M : ℝ) < s.re) (c : ℂ) :
    complexHurwitzZeta s c = hurwitzApprox M (s, c) :=
  hurwitzApprox_eq_of_lt _ M (neg_lt.mp (Nat.lt_succ_floor (-s.re))) hs

/-- On any half-plane `-(M : ℝ) < s.re`, `complexHurwitzReg s c` agrees with
`hurwitzRegApprox M`. -/
theorem complexHurwitzReg_eq_hurwitzRegApprox (M : ℕ) {s : ℂ} (hs : -(M : ℝ) < s.re) (c : ℂ) :
    complexHurwitzReg s c = hurwitzRegApprox M (s, c) :=
  hurwitzRegApprox_eq_of_lt _ M (neg_lt.mp (Nat.lt_succ_floor (-s.re))) hs

/-- Joint analyticity of `(s, c) ↦ complexHurwitzZeta s c` on `{p | p.1 ≠ 1 ∧ 0 < p.2.re}`. -/
theorem analyticOnNhd_complexHurwitzZeta :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ complexHurwitzZeta p.1 p.2)
      {p : ℂ × ℂ | p.1 ≠ 1 ∧ 0 < p.2.re} := by
  intro p hp
  obtain ⟨M, hM⟩ := exists_nat_gt (-p.1.re)
  have hM' : -(M : ℝ) < p.1.re := neg_lt.mp hM
  have hopen : IsOpen {q : ℂ × ℂ | -(M : ℝ) < q.1.re} :=
    isOpen_lt continuous_const (continuous_re.comp continuous_fst)
  refine (analyticOnNhd_hurwitzApprox M p ⟨hM', hp.1, hp.2⟩).congr ?_
  filter_upwards [hopen.mem_nhds hM'] with q hq
  exact (complexHurwitzZeta_eq_hurwitzApprox M hq q.2).symm

/-- Joint complex differentiability of `(s, c) ↦ complexHurwitzZeta s c` on
`{p | p.1 ≠ 1 ∧ 0 < p.2.re}`. -/
theorem differentiableOn_complexHurwitzZeta :
    DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ complexHurwitzZeta p.1 p.2)
      {p : ℂ × ℂ | p.1 ≠ 1 ∧ 0 < p.2.re} :=
  analyticOnNhd_complexHurwitzZeta.differentiableOn

/-- Joint analyticity of `(s, c) ↦ complexHurwitzReg s c` on `{p | 0 < p.2.re}`. -/
theorem analyticOnNhd_complexHurwitzReg :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ complexHurwitzReg p.1 p.2)
      {p : ℂ × ℂ | 0 < p.2.re} := by
  intro p hp
  obtain ⟨M, hM⟩ := exists_nat_gt (-p.1.re)
  have hM' : -(M : ℝ) < p.1.re := neg_lt.mp hM
  have hopen : IsOpen {q : ℂ × ℂ | -(M : ℝ) < q.1.re} :=
    isOpen_lt continuous_const (continuous_re.comp continuous_fst)
  refine (analyticOnNhd_hurwitzRegApprox M p ⟨hM', hp⟩).congr ?_
  filter_upwards [hopen.mem_nhds hM'] with q hq
  exact (complexHurwitzReg_eq_hurwitzRegApprox M hq q.2).symm

/-- Joint complex differentiability of `(s, c) ↦ complexHurwitzReg s c` on `{p | 0 < p.2.re}`. -/
theorem differentiableOn_complexHurwitzReg :
    DifferentiableOn ℂ (fun p : ℂ × ℂ ↦ complexHurwitzReg p.1 p.2)
      {p : ℂ × ℂ | 0 < p.2.re} :=
  analyticOnNhd_complexHurwitzReg.differentiableOn

/-- For fixed `0 < c.re`, `s ↦ complexHurwitzZeta s c` is analytic away from `s = 1`. -/
theorem analyticOnNhd_complexHurwitzZeta_left {c : ℂ} (hc : 0 < c.re) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ complexHurwitzZeta s c) {1}ᶜ := by
  intro s hs
  exact (analyticOnNhd_complexHurwitzZeta (s, c) ⟨hs, hc⟩).comp (f := fun x : ℂ ↦ (x, c))
    (analyticAt_id.prod analyticAt_const)

/-- For fixed `0 < c.re`, `s ↦ complexHurwitzZeta s c` is differentiable away from `s = 1`. -/
theorem differentiableOn_complexHurwitzZeta_left {c : ℂ} (hc : 0 < c.re) :
    DifferentiableOn ℂ (fun s : ℂ ↦ complexHurwitzZeta s c) {1}ᶜ :=
  (analyticOnNhd_complexHurwitzZeta_left hc).differentiableOn

/-- For fixed `0 < c.re`, `s ↦ complexHurwitzReg s c` is an entire function of `s`. -/
theorem differentiable_complexHurwitzReg_left {c : ℂ} (hc : 0 < c.re) :
    Differentiable ℂ (fun s : ℂ ↦ complexHurwitzReg s c) := fun s ↦
  ((analyticOnNhd_complexHurwitzReg (s, c) hc).comp (f := fun x : ℂ ↦ (x, c))
    (analyticAt_id.prod analyticAt_const)).differentiableAt

/-- Agreement with the defining Hurwitz series on `1 < s.re` and `0 < c.re`. -/
theorem complexHurwitzZeta_eq_complexHurwitzSeries {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    complexHurwitzZeta s c = complexHurwitzSeries s c := by
  rw [complexHurwitzZeta_eq_hurwitzApprox 0 (by simpa using zero_lt_one.trans hs),
    hurwitzApprox_zero_eq_complexHurwitzSeries hs hc]

/-- Away from `s = 1`, `complexHurwitzReg s c = (s - 1) * complexHurwitzZeta s c`. -/
theorem complexHurwitzReg_eq_sub_one_mul {s : ℂ} (hs : s ≠ 1) (c : ℂ) :
    complexHurwitzReg s c = (s - 1) * complexHurwitzZeta s c :=
  hurwitzRegApprox_eq_sub_one_mul _ hs

/-- At `s = 1`, `complexHurwitzReg 1 c = 1` for every parameter `c`. -/
@[simp]
theorem complexHurwitzReg_one (c : ℂ) : complexHurwitzReg 1 c = 1 := by
  rw [complexHurwitzReg_eq_hurwitzRegApprox 0 (by simp)]
  simp [hurwitzRegApprox, Complex.Gamma_one]

/-- Simple pole of `complexHurwitzZeta · c` at `s = 1` with residue `1` independent of `c`:
`(s - 1) * complexHurwitzZeta s c → 1` as `s → 1` (`s ≠ 1`). -/
theorem tendsto_sub_one_mul_complexHurwitzZeta_nhdsNE_one {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun s : ℂ ↦ (s - 1) * complexHurwitzZeta s c) (𝓝[≠] 1) (𝓝 1) := by
  have hcont := (differentiable_complexHurwitzReg_left hc 1).continuousAt
  have htend : Tendsto (fun s : ℂ ↦ complexHurwitzReg s c) (𝓝[≠] 1) (𝓝 1) := by
    simpa [complexHurwitzReg_one] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine htend.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact complexHurwitzReg_eq_sub_one_mul hs c

/-! ### Bernoulli polynomial values at all nonpositive integers -/

/-- Value of `complexHurwitzZeta` at every nonpositive integer `-m` (`m : ℕ`, including `m = 0`):
`ζ_H(-m, c) = -B_{m + 1}(c) / (m + 1)`. -/
theorem complexHurwitzZeta_neg_nat_eq_aeval (m : ℕ) (c : ℂ) :
    complexHurwitzZeta (-(m : ℂ)) c =
      -Polynomial.aeval c (Polynomial.bernoulli (m + 1)) / (m + 1) := by
  have hm_lt : -((m + 1 : ℕ) : ℝ) < (-(m : ℂ)).re := by
    simp only [neg_re, natCast_re]; push_cast; linarith
  rw [complexHurwitzZeta_eq_hurwitzApprox (m + 1) hm_lt]
  dsimp only [hurwitzApprox]
  rw [Complex.Gamma_neg_nat_eq_zero, inv_zero, zero_mul, zero_add]
  have hsum : ∑ j ∈ Finset.range (m + 1),
      invGammaDSlope j (-(m : ℂ)) * hurwitzBernoulliCoeff (j + 1) c =
      invGammaDSlope m (-(m : ℂ)) * hurwitzBernoulliCoeff (m + 1) c := by
    refine Finset.sum_eq_single m (fun j _ hjm ↦ ?_) (fun hm_mem ↦ False.elim (hm_mem (by simp)))
    rw [invGammaDSlope_neg_nat_of_ne hjm.symm, zero_mul]
  rw [hsum, invGammaDSlope_neg_nat_self, hurwitzBernoulliCoeff_def]
  have hfac : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hsign : (-1 : ℂ) ^ m * ((-1 : ℂ) ^ m * -1) = -1 := by
    calc (-1 : ℂ) ^ m * ((-1 : ℂ) ^ m * -1)
        = ((-1 : ℂ) * (-1 : ℂ)) ^ m * -1 := by rw [← mul_assoc, ← mul_pow]
      _ = -1 := by norm_num
  calc (-1 : ℂ) ^ m * (m.factorial : ℂ) *
        ((-1 : ℂ) ^ m * -1 * Polynomial.aeval c (Polynomial.bernoulli (m + 1)) /
          (((m : ℂ) + 1) * (m.factorial : ℂ)))
      = ((-1 : ℂ) ^ m * ((-1 : ℂ) ^ m * -1)) *
          Polynomial.aeval c (Polynomial.bernoulli (m + 1)) * (m.factorial : ℂ) /
          (((m : ℂ) + 1) * (m.factorial : ℂ)) := by ring
    _ = -Polynomial.aeval c (Polynomial.bernoulli (m + 1)) / ((m : ℂ) + 1) := by
          rw [hsign]; field_simp [hfac, hm1]

/-- Value of `complexHurwitzZeta` at `-m` (`m : ℕ`) written via `Polynomial.eval` of the mapped
rational Bernoulli polynomial `(Polynomial.bernoulli (m + 1)).map (algebraMap ℚ ℂ)`. -/
theorem complexHurwitzZeta_neg_nat (m : ℕ) (c : ℂ) :
    complexHurwitzZeta (-(m : ℂ)) c =
      -((Polynomial.bernoulli (m + 1)).map (algebraMap ℚ ℂ)).eval c / (m + 1) := by
  rw [complexHurwitzZeta_neg_nat_eq_aeval, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

/-- At `s = 0`, `complexHurwitzZeta 0 c = 1 / 2 - c`. -/
@[simp]
theorem complexHurwitzZeta_zero (c : ℂ) : complexHurwitzZeta 0 c = 1 / 2 - c := by
  have h := complexHurwitzZeta_neg_nat_eq_aeval 0 c
  have h1 := hurwitzBernoulliCoeff_one c
  rw [hurwitzBernoulliCoeff_def] at h1
  simp only [Nat.cast_zero, neg_zero, zero_add, div_one] at h
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h1
  linear_combination h + h1

/-- Special value `ζ_H(0, 1) = -1 / 2`. -/
theorem complexHurwitzZeta_zero_one : complexHurwitzZeta 0 1 = -1 / 2 := by
  rw [complexHurwitzZeta_zero]; norm_num

/-- Special value `ζ_H(0, 1 / 2) = 0`. -/
theorem complexHurwitzZeta_zero_one_half : complexHurwitzZeta 0 (1 / 2) = 0 := by
  rw [complexHurwitzZeta_zero]; norm_num

/-- Complex-parameter value `ζ_H(0, 1 + i) = -1 / 2 - i`. -/
theorem complexHurwitzZeta_zero_one_add_I : complexHurwitzZeta 0 (1 + I) = -1 / 2 - I := by
  rw [complexHurwitzZeta_zero]; ring

/-- At `s = -1`, `complexHurwitzZeta (-1) c = -(c ^ 2 - c + 1 / 6) / 2`. -/
theorem complexHurwitzZeta_neg_one (c : ℂ) :
    complexHurwitzZeta (-1) c = -(c ^ 2 - c + 1 / 6) / 2 := by
  have h := complexHurwitzZeta_neg_nat_eq_aeval 1 c
  have hcoeff := hurwitzBernoulliCoeff_two c
  rw [hurwitzBernoulliCoeff_def] at hcoeff
  have hB2 : Polynomial.aeval c (Polynomial.bernoulli 2) = c ^ 2 - c + 1 / 6 := by
    have hfac : (Nat.factorial 2 : ℂ) = 2 := by norm_num
    have hp : (-1 : ℂ) ^ 2 = 1 := by norm_num
    rw [hfac, hp, one_mul] at hcoeff
    linear_combination 2 * hcoeff
  simp only [Nat.cast_one] at h
  rw [hB2] at h
  linear_combination h

/-- Special value `ζ_H(-1, 1) = -1 / 12`. -/
theorem complexHurwitzZeta_neg_one_one : complexHurwitzZeta (-1) 1 = -1 / 12 := by
  rw [complexHurwitzZeta_neg_one]; norm_num

/-! ### Analytic-uniqueness extensions away from `s = 1` -/

/-- Analytic uniqueness of `complexHurwitzZeta`: any function analytic on `{1}ᶜ` that agrees with
`complexHurwitzSeries · c` on the convergence half-plane `1 < z.re` equals
`complexHurwitzZeta · c` everywhere away from `s = 1`. -/
theorem eq_complexHurwitzZeta_of_analyticOnNhd {c : ℂ} (hc : 0 < c.re) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g {1}ᶜ)
    (heq : ∀ z : ℂ, 1 < z.re → g z = complexHurwitzSeries z c) {s : ℂ} (hs : s ≠ 1) :
    g s = complexHurwitzZeta s c := by
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2_mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hnhds : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
  refine hg.eqOn_of_preconnected_of_eventuallyEq (analyticOnNhd_complexHurwitzZeta_left hc)
    hpc h2_mem ?_ hs
  filter_upwards [hnhds] with z hz
  rw [heq z hz, complexHurwitzZeta_eq_complexHurwitzSeries hz hc]

/-- Meromorphic shift identity: for `s ≠ 1` and `0 < c.re`,
`complexHurwitzZeta s (c + 1) = complexHurwitzZeta s c - c ^ (-s)`. -/
theorem complexHurwitzZeta_add_one {s c : ℂ} (hs : s ≠ 1) (hc : 0 < c.re) :
    complexHurwitzZeta s (c + 1) = complexHurwitzZeta s c - c ^ (-s) := by
  have hc1 : 0 < (c + 1).re := by simp [add_re]; linarith
  have hcpow : AnalyticOnNhd ℂ (fun z : ℂ ↦ c ^ (-z)) {1}ᶜ := fun _ _ ↦
    analyticAt_const.cpow analyticAt_id.neg (Or.inl hc)
  symm
  exact eq_complexHurwitzZeta_of_analyticOnNhd hc1
    ((analyticOnNhd_complexHurwitzZeta_left hc).sub hcpow)
    (fun z hz ↦ by
      dsimp only [Pi.sub_apply]
      rw [complexHurwitzZeta_eq_complexHurwitzSeries hz hc, complexHurwitzSeries_add_one hz hc]) hs

/-- Global comparison with Mathlib's circle-valued `HurwitzZeta.hurwitzZeta`: for real `c ∈ (0, 1]`
and every `s ≠ 1`, `complexHurwitzZeta s c = HurwitzZeta.hurwitzZeta c s`. -/
theorem complexHurwitzZeta_ofReal_eq_hurwitzZeta {s : ℂ} (hs : s ≠ 1) {c : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1) :
    complexHurwitzZeta s c = HurwitzZeta.hurwitzZeta c s := by
  have hc_re : 0 < (c : ℂ).re := by simpa using hc.1
  have hhurw : AnalyticOnNhd ℂ (HurwitzZeta.hurwitzZeta (c : UnitAddCircle)) {1}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun z hz ↦ (HurwitzZeta.differentiableAt_hurwitzZeta _ hz).differentiableWithinAt)
      isOpen_compl_singleton
  symm
  exact eq_complexHurwitzZeta_of_analyticOnNhd hc_re hhurw
    (fun z hz ↦ (complexHurwitzSeries_ofReal_eq_hurwitzZeta hz hc).symm) hs

/-- At `c = 1` and `s ≠ 1`, `complexHurwitzZeta s 1 = riemannZeta s`. -/
theorem complexHurwitzZeta_one {s : ℂ} (hs : s ≠ 1) :
    complexHurwitzZeta s 1 = riemannZeta s := by
  have h := complexHurwitzZeta_ofReal_eq_hurwitzZeta (c := 1) hs
    (mem_Ioc.mpr ⟨zero_lt_one, le_rfl⟩)
  rw [AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero] at h
  simpa using h

/-- At `c = 1 / 2` and `s ≠ 1`, `complexHurwitzZeta s (1 / 2) = (2 ^ s - 1) * riemannZeta s`. -/
theorem complexHurwitzZeta_one_half {s : ℂ} (hs : s ≠ 1) :
    complexHurwitzZeta s (1 / 2) = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  have hpow : AnalyticOnNhd ℂ (fun z : ℂ ↦ (2 : ℂ) ^ z - 1) {1}ᶜ := fun _ _ ↦
    (analyticAt_const.cpow analyticAt_id (Or.inl (by norm_num))).sub analyticAt_const
  have hzeta : AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun z hz ↦ (differentiableAt_riemannZeta hz).differentiableWithinAt) isOpen_compl_singleton
  symm
  exact eq_complexHurwitzZeta_of_analyticOnNhd (by norm_num) (hpow.mul hzeta)
    (fun z hz ↦ (complexHurwitzSeries_one_half hz).symm) hs

/-- Joint meromorphic continuation and Bernoulli special values of the complex-parameter Hurwitz
zeta function: there exist jointly differentiable functions `H` (on `s ≠ 1`, `0 < c.re`) and `R`
(on `0 < c.re`) continuing `complexHurwitzSeries`, satisfying `R (1, c) = 1` and
`R (s, c) = (s - 1) * H (s, c)` away from `s = 1`, and taking the values
`-B_{m + 1}(c) / (m + 1)` at all nonpositive integers `-m` (including `m = 0`). -/
theorem complexHurwitzContinuation_exists :
    ∃ H R : ℂ × ℂ → ℂ,
      DifferentiableOn ℂ H {p | p.1 ≠ 1 ∧ 0 < p.2.re} ∧
      DifferentiableOn ℂ R {p | 0 < p.2.re} ∧
      ∀ c : ℂ, 0 < c.re →
        (∀ s : ℂ, 1 < s.re → H (s, c) = complexHurwitzSeries s c) ∧
        R (1, c) = 1 ∧
        (∀ s : ℂ, s ≠ 1 → R (s, c) = (s - 1) * H (s, c)) ∧
        (∀ m : ℕ, H (-(m : ℂ), c) =
          -((Polynomial.bernoulli (m + 1)).map (algebraMap ℚ ℂ)).eval c / (m + 1)) :=
  ⟨fun p ↦ complexHurwitzZeta p.1 p.2, fun p ↦ complexHurwitzReg p.1 p.2,
    differentiableOn_complexHurwitzZeta, differentiableOn_complexHurwitzReg,
    fun c hc ↦ ⟨fun _ hs ↦ complexHurwitzZeta_eq_complexHurwitzSeries hs hc,
      complexHurwitzReg_one c,
      fun _ hs ↦ complexHurwitzReg_eq_sub_one_mul hs c,
      fun m ↦ complexHurwitzZeta_neg_nat m c⟩⟩

end TauCeti

/-! ### Consequences for `HurwitzZeta.hurwitzZeta`, `ZMod.LFunction`, and `DirichletCharacter` -/

namespace HurwitzZeta

/-- Value of Mathlib's `HurwitzZeta.hurwitzZeta c` at all nonpositive integers `-m` (including
`m = 0`) for real `c ∈ (0, 1]`, closing the `k = 0` case on `(0, 1]` omitted by
`HurwitzZeta.hurwitzZeta_neg_nat_of_ne_zero`. -/
theorem hurwitzZeta_neg_nat_of_mem_Ioc {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) (m : ℕ) :
    hurwitzZeta c (-(m : ℂ)) =
      -((Polynomial.bernoulli (m + 1)).map (algebraMap ℚ ℂ)).eval (c : ℂ) / (m + 1) := by
  have hs : -(m : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re, one_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [← TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta hs hc,
    TauCeti.complexHurwitzZeta_neg_nat]

/-- Value of `HurwitzZeta.hurwitzZeta c 0 = 1 / 2 - c` for real `c ∈ (0, 1]`. -/
theorem hurwitzZeta_zero_of_mem_Ioc {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    hurwitzZeta c 0 = 1 / 2 - (c : ℂ) := by
  rw [← TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta zero_ne_one hc,
    TauCeti.complexHurwitzZeta_zero]

end HurwitzZeta

namespace ZMod

/-- Global Hurwitz decomposition of `ZMod.LFunction Φ s` away from `s = 1` in terms of the
meromorphically continued `TauCeti.complexHurwitzZeta`. -/
theorem LFunction_eq_sum_Icc_complexHurwitzZeta {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) {s : ℂ}
    (hs : s ≠ 1) :
    ZMod.LFunction Φ s =
      (N : ℂ) ^ (-s) * ∑ a ∈ Finset.Icc 1 N,
        Φ a * TauCeti.complexHurwitzZeta s ((a : ℂ) / N) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [LFunction_eq_sum_Icc_hurwitzZeta]
  congr 1
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finset.mem_Icc] at ha
  have ha_mem : (a : ℝ) / (N : ℝ) ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos (Nat.cast_pos.mpr ha.1) hN, (div_le_one hN).mpr (by exact_mod_cast ha.2)⟩
  have hcast : (((a : ℝ) / (N : ℝ) : ℝ) : ℂ) = (a : ℂ) / N := by push_cast; rfl
  rw [← hcast, TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta hs ha_mem]

end ZMod

namespace DirichletCharacter

/-- Global Hurwitz decomposition of `χ.LFunction s` away from `s = 1` in terms of
`TauCeti.complexHurwitzZeta`. -/
theorem LFunction_eq_sum_Icc_complexHurwitzZeta {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s ≠ 1) :
    χ.LFunction s =
      (N : ℂ) ^ (-s) * ∑ a ∈ Finset.Icc 1 N,
        χ a * TauCeti.complexHurwitzZeta s ((a : ℂ) / N) :=
  ZMod.LFunction_eq_sum_Icc_complexHurwitzZeta χ hs

end DirichletCharacter
