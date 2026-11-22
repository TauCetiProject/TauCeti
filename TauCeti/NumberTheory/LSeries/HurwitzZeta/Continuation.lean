/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import TauCeti.NumberTheory.LSeries.HurwitzZeta.Series
public import TauCeti.NumberTheory.LSeries.HurwitzZeta.TaylorKernel
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.HalfPlaneIdentity
import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.MellinTransform.Growth
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.IncompleteZeta
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Joint meromorphic continuation and Bernoulli values of the complex Hurwitz zeta function

For `0 < c.re`, the Dirichlet series `complexHurwitzSeries s c = ∑' n, exp (-s * log (n + c))`
on `1 < s.re` extends meromorphically in `s ∈ ℂ`, jointly holomorphically with `c` in
`{0 < c.re}`, with a single simple pole at `s = 1` of residue `1`.

Starting from the Gamma-Laplace integral on `1 < s.re` and `0 < c.re`, splitting `(0, ∞)` at
`t = 1` and subtracting the order-`M` Taylor polynomial of `hurwitzKernel c` at `t = 0` yields a
stage-`M` meromorphic representation on `{-(M : ℝ) < s.re} × {0 < c.re}`. The apparent poles at
`s = 1 - k` (`1 ≤ k ≤ M`) are cancelled by the simple zeros of `(Gamma s)⁻¹` via the entire
divided difference `dslope (fun w ↦ (Gamma w)⁻¹) (-(k - 1 : ℕ)) s`.

Consecutive stages agree identically on overlapping half-planes, gluing into canonical functions
`complexHurwitzZeta` (jointly holomorphic on `{p | p.1 ≠ 1 ∧ 0 < p.2.re}`) and
`complexHurwitzZeta₁` (jointly holomorphic on `{p | 0 < p.2.re}`), with
`complexHurwitzZeta₁ 1 c = 1`, `complexHurwitzZeta₁ s c = (s - 1) * complexHurwitzZeta s c` for
`s ≠ 1`, and nonpositive integer special values
`complexHurwitzZeta (-m) c = -B_{m + 1}(c) / (m + 1)`.

Analytic continuation off `s = 1` extends the `c ↦ c + 1` shift identity and the comparisons with
`HurwitzZeta.hurwitzZeta` on `(0, 1]` and `riemannZeta` at `c = 1` and `c = 1 / 2` (with finite
periodic and Dirichlet L-function decompositions in
`TauCeti.NumberTheory.LSeries.ZMod.LFunction`,
`TauCeti.NumberTheory.LSeries.HurwitzZeta.LFunction`, and
`TauCeti.NumberTheory.LSeries.HurwitzZeta.ZMod`).

## Main definitions and results

* `TauCeti.hurwitzHeadIntegral`, `TauCeti.hurwitzTailIntegral`, `TauCeti.hurwitzStageCore`:
  stage-`M` Taylor-subtracted head integral, exponential tail integral, and combined holomorphic
  core, with integrand convergence (`integrableOn_hurwitzHeadIntegrand`,
  `integrableOn_hurwitzTailIntegrand`), joint analyticity (`analyticOnNhd_hurwitzHeadIntegral`,
  `analyticOnNhd_hurwitzTailIntegral`, `analyticOnNhd_hurwitzStageCore`), and overlap identities
  (`hurwitzHeadIntegral_eq_add_succ`, `hurwitzStageCore_succ_eq`, `hurwitzStageCore_eq_of_le`).
* `TauCeti.complexHurwitzZeta`, `TauCeti.complexHurwitzZeta₁`: canonical continued Hurwitz zeta
  function and its `(s - 1)`-multiplied entire-in-`s` companion, with stage representations
  `complexHurwitzZeta_eq_inv_Gamma_div_add_hurwitzStageCore` and
  `complexHurwitzZeta₁_eq_inv_Gamma_add_mul_hurwitzStageCore`.
* `TauCeti.analyticOnNhd_complexHurwitzZeta`,
  `TauCeti.analyticOnNhd_complexHurwitzZeta_sub_inv_Gamma_div`,
  `TauCeti.analyticOnNhd_complexHurwitzZeta₁`, `TauCeti.differentiableOn_complexHurwitzZeta`,
  `TauCeti.differentiableOn_complexHurwitzZeta₁`, and slice regularity lemmas
  (`TauCeti.analyticAt_complexHurwitzZeta_left`, `TauCeti.differentiableOn_complexHurwitzZeta_left`,
  `TauCeti.differentiableAt_complexHurwitzZeta_left`,
  `TauCeti.differentiableAt_complexHurwitzZeta_right`,
  `TauCeti.analyticAt_complexHurwitzZeta₁_left`, `TauCeti.differentiable_complexHurwitzZeta₁_left`,
  `TauCeti.differentiableAt_complexHurwitzZeta₁_right`).
* `TauCeti.complexHurwitzZeta_eventuallyEq_nhdsNE_one`,
  `TauCeti.meromorphic_complexHurwitzZeta_left`,
  `TauCeti.meromorphicOrderAt_complexHurwitzZeta_one`,
  `TauCeti.meromorphicTrailingCoeffAt_complexHurwitzZeta_one`, and
  `TauCeti.tendsto_sub_one_mul_complexHurwitzZeta`: simple pole of order `-1` and residue `1` at
  `s = 1`.
* `TauCeti.integrableOn_hurwitzMellinIntegrand`,
  `TauCeti.complexHurwitzZeta_eq_inv_Gamma_mul_integral_Ioi`, and
  `TauCeti.complexHurwitzZeta_eq_complexHurwitzSeries`: Mellin–Laplace integrand convergence,
  integral representation, and agreement with `complexHurwitzSeries` on `1 < s.re` and `0 < c.re`.
* `TauCeti.complexHurwitzZeta_neg_nat` and `TauCeti.complexHurwitzZeta_zero_left`: Bernoulli
  polynomial values at nonpositive integers.
* `TauCeti.complexHurwitzContinuation_exists`, `TauCeti.eq_complexHurwitzZeta_of_eqOn_re_gt`,
  `TauCeti.eq_complexHurwitzZeta₁_of_eq_sub_one_mul`, and
  `TauCeti.eq_complexHurwitzZeta₁_of_eqOn_re_gt`: packaged existence (leaving `H (1, c)`
  unconstrained) and uniqueness on `0 < c.re`, where `complexHurwitzZeta` is unique off `s = 1` and
  `complexHurwitzZeta₁` is unique across the pole.
* `TauCeti.complexHurwitzZeta_add_one_right`, `TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta`,
  `TauCeti.complexHurwitzZeta_one_right`, `TauCeti.complexHurwitzZeta_one_half_right`, and
  `HurwitzZeta.hurwitzZeta_apply_zero_of_mem_Ioc`: shift identity, `c = 1` and `c = 1 / 2`
  specializations, and endpoint evaluation of `HurwitzZeta.hurwitzZeta` at `s = 0`.

## References

* J. C. Lagarias and W. C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  **24** (2012), 49–84, §9.
* J. C. Lagarias and W. C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  Res. Math. Sci. **3** (2016), Paper No. 2, §6.
* F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, §25.11.
-/

public section

open Complex Set Filter MeasureTheory Metric Asymptotics
open scoped Topology Real

namespace TauCeti

/-! ### Joint holomorphy of the subtracted head integral on `(0, 1]` -/

/-- The stage-`M` Taylor-subtracted head integral on `(0, 1]`,
`∫ t in Ioc 0 1, (t : ℂ) ^ (s + M - 1) * hurwitzTaylorQuot M c t`. -/
noncomputable def hurwitzHeadIntegral (M : ℕ) (s c : ℂ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + M - 1) * hurwitzTaylorQuot M c t

/-- Defining equation for `hurwitzHeadIntegral`. -/
theorem hurwitzHeadIntegral_def (M : ℕ) (s c : ℂ) :
    hurwitzHeadIntegral M s c =
      ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + M - 1) * hurwitzTaylorQuot M c t := (rfl)

private theorem ofReal_snd_mem_dslope_exp_ne_zero (c : ℂ) (t : ℝ) :
    (c, (t : ℂ)) ∈ {p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0} := by
  simpa using Complex.dslope_exp_ofReal_ne_zero 0 (-t)

private theorem analyticAt_hurwitzTaylorQuot_ofReal (M : ℕ) (c : ℂ) (t : ℝ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => hurwitzTaylorQuot M p.1 p.2) (c, t) :=
  analyticOnNhd_hurwitzTaylorQuot M (c, t) (ofReal_snd_mem_dslope_exp_ne_zero c t)

private theorem exists_norm_hurwitzTaylorQuot_le_Icc {K : Set ℂ} (hK : IsCompact K) (M : ℕ) :
    ∃ B ≥ 0, ∀ c ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ‖hurwitzTaylorQuot M c t‖ ≤ B := by
  let S : Set (ℂ × ℂ) := K ×ˢ (Complex.ofReal '' Icc (0 : ℝ) 1)
  have hS_comp : IsCompact S := hK.prod (isCompact_Icc.image continuous_ofReal)
  have hS_sub : S ⊆ {p : ℂ × ℂ | dslope Complex.exp 0 (-p.2) ≠ 0} := by
    rintro ⟨c, _⟩ ⟨_, t, _, rfl⟩
    exact ofReal_snd_mem_dslope_exp_ne_zero c t
  obtain ⟨B, hB0, hB⟩ := exists_norm_hurwitzTaylorQuot_le hS_comp hS_sub M
  exact ⟨B, hB0, fun c hc t ht => hB (c, t) ⟨hc, t, ht, rfl⟩⟩

private theorem norm_hurwitzHeadIntegrand_eq (M : ℕ) (s c : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s + M - 1) * hurwitzTaylorQuot M c t‖ =
      ‖hurwitzTaylorQuot M c t‖ * t ^ (s.re + M - 1) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, add_re, natCast_re, one_re, mul_comm]

private theorem aestronglyMeasurable_hurwitzHeadIntegrand (M : ℕ) (s c : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s + M - 1) * hurwitzTaylorQuot M c t)
      (volume.restrict (Ioc 0 1)) := by
  refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioc
  refine ((continuous_ofReal.continuousAt.cpow continuousAt_const
    (ofReal_mem_slitPlane.mpr ht.1)).mul (ContinuousAt.comp
      (g := fun p : ℂ × ℂ => hurwitzTaylorQuot M p.1 p.2) (f := fun u : ℝ => (c, (u : ℂ)))
      (analyticAt_hurwitzTaylorQuot_ofReal M c t).continuousAt
      (continuous_const.prodMk continuous_ofReal).continuousAt)).continuousWithinAt

/-- For `-(M : ℝ) < s.re`, the stage-`M` head integrand
`t ↦ t ^ (s + M - 1) * hurwitzTaylorQuot M c t` is integrable on `Ioc 0 1`. -/
theorem integrableOn_hurwitzHeadIntegrand (M : ℕ) {s c : ℂ} (hs : -(M : ℝ) < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s + M - 1) * hurwitzTaylorQuot M c t) (Ioc 0 1) := by
  obtain ⟨B, _, hB⟩ := exists_norm_hurwitzTaylorQuot_le_Icc (isCompact_singleton (x := c)) M
  have hint : IntegrableOn (fun t : ℝ => B * t ^ (s.re + M - 1)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul B
  refine Integrable.mono' hint (aestronglyMeasurable_hurwitzHeadIntegrand M s c) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_hurwitzHeadIntegrand_eq M s c ht.1]
  exact mul_le_mul_of_nonneg_right (hB c (mem_singleton c) t (Ioc_subset_Icc_self ht))
    (Real.rpow_nonneg ht.1.le _)

private theorem continuousOn_hurwitzHeadIntegral (M : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => hurwitzHeadIntegral M p.1 p.2)
      {p | -(M : ℝ) < p.1.re} := by
  intro p₀ hp₀
  rw [mem_ofPred_eq] at hp₀
  let δ := (p₀.1.re + (M : ℝ)) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨B, hB0, hB⟩ := exists_norm_hurwitzTaylorQuot_le_Icc (isCompact_closedBall p₀.2 1) M
  have hbint : Integrable (fun t : ℝ => B * t ^ (δ - 1)) (volume.restrict (Ioc 0 1)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul B
  have hcont_t : ∀ᶠ t : ℝ in ae (volume.restrict (Ioc 0 1)), ContinuousAt
      (fun p : ℂ × ℂ => (t : ℂ) ^ (p.1 + M - 1) * hurwitzTaylorQuot M p.2 t) p₀ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    refine (continuousAt_const.cpow ((continuous_fst.add continuous_const).sub
      continuous_const).continuousAt (ofReal_mem_slitPlane.mpr ht.1)).mul ?_
    exact (analyticAt_hurwitzTaylorQuot_ofReal M p₀.2 t).continuousAt.comp
      (f := fun p : ℂ × ℂ => (p.2, (t : ℂ)))
      (continuous_snd.prodMk continuous_const).continuousAt
  have hnhds : {p | δ - M < p.1.re} ∩ (Prod.snd ⁻¹' closedBall p₀.2 1) ∈ 𝓝 p₀ :=
    Filter.inter_mem ((isOpen_lt continuous_const (continuous_re.comp continuous_fst)).mem_nhds
      (by dsimp [δ]; linarith)) (continuous_snd.continuousAt.preimage_mem_nhds
        (closedBall_mem_nhds p₀.2 one_pos))
  refine ContinuousAt.continuousWithinAt (continuousAt_of_dominated
    (Eventually.of_forall fun p => aestronglyMeasurable_hurwitzHeadIntegrand M p.1 p.2)
    ?_ hbint hcont_t)
  filter_upwards [hnhds] with p ⟨hp1, hp2⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_hurwitzHeadIntegrand_eq M p.1 p.2 ht.1]
  exact mul_le_mul (hB p.2 hp2 t (Ioc_subset_Icc_self ht))
    (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by dsimp at hp1; linarith))
    (Real.rpow_nonneg ht.1.le _) hB0

private theorem differentiableAt_hurwitzHeadIntegral_left (M : ℕ) {s₀ c₀ : ℂ}
    (hs₀ : -(M : ℝ) < s₀.re) :
    DifferentiableAt ℂ (fun s => hurwitzHeadIntegral M s c₀) s₀ := by
  let f : ℝ → ℂ := (Ioc 0 1).indicator fun t => hurwitzTaylorQuot M c₀ t
  have hmellin : (mellin f ∘ fun s : ℂ => s + M) = fun s => hurwitzHeadIntegral M s c₀ := by
    ext s
    simp_rw [Function.comp_apply, mellin, f, ← indicator_smul, setIntegral_indicator
      measurableSet_Ioc, inter_eq_right.mpr Ioc_subset_Ioi_self, smul_eq_mul,
      hurwitzHeadIntegral_def]
  have hf_int : IntegrableOn f (Ioi 0) := by
    rw [integrableOn_indicator_iff measurableSet_Ioc.nullMeasurableSet,
      inter_eq_left.mpr Ioc_subset_Ioi_self]
    simpa [sub_add_cancel] using
      integrableOn_hurwitzHeadIntegrand M (s := 1 - M) (c := c₀) (by simp)
  have hf_top : f =O[atTop] fun t : ℝ => t ^ (-((s₀ + M).re + 1)) :=
    IsBigO.of_bound 0 (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      simp [f, indicator_of_notMem (fun h : t ∈ Ioc 0 1 => ht.not_ge h.2)])
  obtain ⟨B, _, hB⟩ := exists_norm_hurwitzTaylorQuot_le_Icc (isCompact_singleton (x := c₀)) M
  have hf_bot : f =O[𝓝[>] 0] fun t : ℝ => t ^ (-(0 : ℝ)) := by
    refine IsBigO.of_bound B ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    have ht_Ioc : t ∈ Ioc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
    simpa [f, indicator_of_mem ht_Ioc] using
      hB c₀ (mem_singleton c₀) t (Ioc_subset_Icc_self ht_Ioc)
  rw [← hmellin]
  exact DifferentiableAt.comp (g := mellin f) (f := fun s : ℂ => s + M) s₀
    (mellin_differentiableAt_of_isBigO_rpow hf_int.locallyIntegrableOn
      hf_top (lt_add_one _) hf_bot (by simp; linarith)) (differentiableAt_id.add_const (M : ℂ))

private theorem differentiableAt_hurwitzHeadIntegral_right (M : ℕ) {s₀ c₀ : ℂ}
    (hs₀ : -(M : ℝ) < s₀.re) :
    DifferentiableAt ℂ (fun c => hurwitzHeadIntegral M s₀ c) c₀ := by
  let φ : ℝ → ℂ := fun t => (projIcc (0 : ℝ) 1 zero_le_one t : ℂ)
  have hf : ∀ y ∈ ofReal '' Icc (0 : ℝ) 1,
      AnalyticAt ℂ (fun q : ℂ × ℂ => hurwitzTaylorQuot M q.1 q.2) (c₀, y) := by
    rintro _ ⟨t, _, rfl⟩
    exact analyticAt_hurwitzTaylorQuot_ofReal M c₀ t
  have hg : Integrable (fun t : ℝ => (t : ℂ) ^ (s₀ + (M : ℂ) - 1))
      (volume.restrict (Ioc 0 1)) :=
    (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) (by simp; linarith)).1
  have han := analyticAt_integral_smul (isCompact_Icc.image continuous_ofReal)
    (continuous_ofReal.comp continuous_projIcc.subtypeVal)
    (fun t => ⟨_, (projIcc (0 : ℝ) 1 zero_le_one t).property, rfl⟩) hf hg
  have heq : (fun c => ∫ t in Ioc (0 : ℝ) 1,
        ((t : ℂ) ^ (s₀ + (M : ℂ) - 1)) • hurwitzTaylorQuot M c (φ t)) =
      fun c => hurwitzHeadIntegral M s₀ c := by
    ext c; rw [hurwitzHeadIntegral_def]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    simp only [φ, smul_eq_mul, projIcc_of_mem zero_le_one (Ioc_subset_Icc_self ht)]
  rw [← heq]; exact han.differentiableAt

/-- The stage-`M` head integral is jointly analytic on `{p : ℂ × ℂ | -(M : ℝ) < p.1.re}`. -/
theorem analyticOnNhd_hurwitzHeadIntegral (M : ℕ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzHeadIntegral M p.1 p.2)
      {p | -(M : ℝ) < p.1.re} :=
  (continuousOn_hurwitzHeadIntegral M).analyticOnNhd_of_separately_differentiableAt
    (isOpen_lt continuous_const (continuous_re.comp continuous_fst))
    (fun _ hq => differentiableAt_hurwitzHeadIntegral_left M hq)
    (fun _ hq => differentiableAt_hurwitzHeadIntegral_right M hq)

/-! ### Joint holomorphy of the exponential tail integral on `(1, ∞)` -/

/-- The exponential tail integral on `(1, ∞)`,
`∫ t in Ioi 1, (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t)))`. -/
noncomputable def hurwitzTailIntegral (s c : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))

/-- Defining equation for `hurwitzTailIntegral`. -/
theorem hurwitzTailIntegral_def (s c : ℂ) :
    hurwitzTailIntegral s c =
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t))) := (rfl)

private theorem aestronglyMeasurable_hurwitzTailIntegrand (s c : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t))))
      (volume.restrict (Ioi 1)) :=
  Measurable.aestronglyMeasurable (by fun_prop)

/-- For `0 < c.re`, the tail integrand `t ↦ (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))`
is integrable on `Ioi 1`. -/
theorem integrableOn_hurwitzTailIntegrand (s : ℂ) {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))) (Ioi 1) :=
  integrableOn_cpow_smul_of_norm_le_exp_neg_mul_rpow hc one_pos
    (Measurable.aestronglyMeasurable (by fun_prop))
    (fun _ ht => by
      simpa only [Real.rpow_one] using norm_exp_neg_mul_div_one_sub_exp_neg_le one_pos ht.le c) s

private theorem continuousOn_hurwitzTailIntegral :
    ContinuousOn (fun p : ℂ × ℂ => hurwitzTailIntegral p.1 p.2) {p | 0 < p.2.re} := by
  intro p₀ hp₀
  rw [mem_ofPred_eq] at hp₀
  let η := p₀.2.re / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hbint :
      Integrable (fun t : ℝ => (1 - Real.exp (-1))⁻¹ * (t ^ p₀.1.re * Real.exp (-η * t)))
        (volume.restrict (Ioi 1)) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi_of_pos one_pos (Or.inl hη)).const_mul _
  have hcont_t : ∀ᶠ t : ℝ in ae (volume.restrict (Ioi 1)), ContinuousAt
      (fun p : ℂ × ℂ => (t : ℂ) ^ (p.1 - 1) * (exp (-p.2 * t) / (1 - exp (-t)))) p₀ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (continuousAt_const.cpow ((continuous_fst.sub continuous_const).continuousAt)
      (ofReal_mem_slitPlane.mpr (zero_lt_one.trans ht))).mul
        ((((continuous_snd.neg.mul continuous_const).cexp).div_const _).continuousAt)
  have hnhds : {p : ℂ × ℂ | p.1.re < p₀.1.re + 1 ∧ η < p.2.re} ∈ 𝓝 p₀ :=
    ((isOpen_lt (continuous_re.comp continuous_fst) continuous_const).inter
      (isOpen_lt continuous_const (continuous_re.comp continuous_snd))).mem_nhds
      ⟨lt_add_one _, by dsimp [η]; linarith⟩
  refine ContinuousAt.continuousWithinAt (continuousAt_of_dominated
    (Eventually.of_forall fun p => aestronglyMeasurable_hurwitzTailIntegrand p.1 p.2)
    ?_ hbint hcont_t)
  filter_upwards [hnhds] with p ⟨hp1, hp2⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), sub_re, one_re]
  exact rpow_mul_norm_exp_neg_mul_div_one_sub_exp_neg_le one_pos ht.le ht.le
    (by linarith [hp1]) hp2.le

private theorem differentiableAt_hurwitzTailIntegral_left (s₀ : ℂ) {c₀ : ℂ}
    (hc₀ : 0 < c₀.re) :
    DifferentiableAt ℂ (fun s => hurwitzTailIntegral s c₀) s₀ := by
  let g : ℝ → ℂ := fun t => exp (-c₀ * t) / (1 - exp (-t))
  let f : ℝ → ℂ := (Ioi 1).indicator g
  have hmellin : mellin f = fun s => hurwitzTailIntegral s c₀ := by
    ext s; simpa [f, g, hurwitzTailIntegral, smul_eq_mul] using
      mellin_indicator_Ioi g zero_le_one s
  have hf_int : IntegrableOn f (Ioi 0) := by
    simpa [MellinConvergent, f] using (mellinConvergent_indicator_Ioi_iff (f := g)
      zero_le_one (s := 1)).mpr (integrableOn_hurwitzTailIntegrand 1 hc₀)
  have hf_top : f =O[atTop] fun t : ℝ => Real.exp (-c₀.re * t) := by
    refine IsBigO.of_bound (1 - Real.exp (-1))⁻¹ ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    simp only [f, indicator_of_mem (mem_Ioi.mpr ht), Real.norm_of_nonneg (Real.exp_pos _).le]
    exact norm_exp_neg_mul_div_one_sub_exp_neg_le one_pos ht.le c₀
  have hf_bot : f =O[𝓝[>] 0] fun t : ℝ => t ^ (-(s₀.re - 1)) :=
    IsBigO.of_bound 0 (by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
      simp [f, indicator_of_notMem (fun h : t ∈ Ioi (1 : ℝ) => ht.2.not_gt h)])
  rw [← hmellin]
  exact mellin_differentiableAt_of_isBigO_rpow_exp hc₀ hf_int.locallyIntegrableOn
    hf_top hf_bot (sub_one_lt s₀.re)

private theorem differentiableAt_hurwitzTailIntegral_right (s₀ : ℂ) {c₀ : ℂ}
    (hc₀ : 0 < c₀.re) :
    DifferentiableAt ℂ (fun c => hurwitzTailIntegral s₀ c) c₀ := by
  let g : ℝ → ℂ := (Ioi 1).indicator fun t => (t : ℂ) ^ (s₀ - 1) / (1 - exp (-t))
  have hdiff : DifferentiableOn ℂ (hurwitzTailIntegral s₀) {c : ℂ | 0 < c.re} := by
    refine differentiableOn_of_hasLaplace_re_gt (f := g) fun c hc => ?_
    have heq : (fun t : ℝ => exp (-c * t) • g t) = (Ioi (1 : ℝ)).indicator
        (fun t : ℝ => (t : ℂ) ^ (s₀ - 1) * (exp (-c * t) / (1 - exp (-t)))) := by
      ext t; by_cases ht : t ∈ Ioi (1 : ℝ)
      · simp only [g, indicator_of_mem ht, smul_eq_mul]; ring
      · simp only [g, indicator_of_notMem ht, smul_zero]
    have hint : IntegrableOn (fun t : ℝ => exp (-c * t) • g t) (Ioi 0) := by
      rw [heq, integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet,
        inter_eq_left.mpr (Ioi_subset_Ioi zero_le_one)]
      exact integrableOn_hurwitzTailIntegrand s₀ hc
    refine HasLaplace.intro hint ?_
    rw [hurwitzTailIntegral_def, heq, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  exact (hdiff c₀ hc₀).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds hc₀)

/-- The exponential tail integral is jointly analytic on `{p : ℂ × ℂ | 0 < p.2.re}`. -/
theorem analyticOnNhd_hurwitzTailIntegral :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzTailIntegral p.1 p.2) {p | 0 < p.2.re} :=
  continuousOn_hurwitzTailIntegral.analyticOnNhd_of_separately_differentiableAt
    (isOpen_lt continuous_const (continuous_re.comp continuous_snd))
    (fun q hq => differentiableAt_hurwitzTailIntegral_left q.1 hq)
    (fun q hq => differentiableAt_hurwitzTailIntegral_right q.1 hq)

/-! ### Stage-`M` holomorphic core and canonical global definitions -/

/-- The stage-`M` holomorphic core on `{-(M : ℝ) < s.re} × {0 < c.re}`, cancelling the poles at
`s = 1 - k` (`1 ≤ k ≤ M`) against the zeros of `(Complex.Gamma s)⁻¹`. -/
noncomputable def hurwitzStageCore (M : ℕ) (s c : ℂ) : ℂ :=
  (Complex.Gamma s)⁻¹ * (hurwitzHeadIntegral M s c + hurwitzTailIntegral s c) +
    ∑ k ∈ Finset.Icc 1 M,
      hurwitzBernoulliCoeff k c *
        dslope (fun w : ℂ ↦ (Complex.Gamma w)⁻¹) (-((k - 1 : ℕ) : ℂ)) s

/-- Defining equation for `hurwitzStageCore`. -/
theorem hurwitzStageCore_def (M : ℕ) (s c : ℂ) :
    hurwitzStageCore M s c =
      (Complex.Gamma s)⁻¹ * (hurwitzHeadIntegral M s c + hurwitzTailIntegral s c) +
        ∑ k ∈ Finset.Icc 1 M,
          hurwitzBernoulliCoeff k c *
            dslope (fun w : ℂ ↦ (Complex.Gamma w)⁻¹) (-((k - 1 : ℕ) : ℂ)) s := (rfl)

/-- The stage-`M` holomorphic core is jointly analytic on
`{p : ℂ × ℂ | -(M : ℝ) < p.1.re ∧ 0 < p.2.re}`. -/
theorem analyticOnNhd_hurwitzStageCore (M : ℕ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzStageCore M p.1 p.2)
      {p | -(M : ℝ) < p.1.re ∧ 0 < p.2.re} := by
  have hdiff : DifferentiableOn ℂ (fun p : ℂ × ℂ =>
      (Complex.Gamma p.1)⁻¹ * (hurwitzHeadIntegral M p.1 p.2 + hurwitzTailIntegral p.1 p.2) +
        ∑ k ∈ Finset.Icc 1 M, hurwitzBernoulliCoeff k p.2 *
          dslope (fun w : ℂ ↦ (Complex.Gamma w)⁻¹) (-((k - 1 : ℕ) : ℂ)) p.1)
      {p | -(M : ℝ) < p.1.re ∧ 0 < p.2.re} := by
    intro p hp
    have hd_sum : DifferentiableAt ℂ (fun q : ℂ × ℂ => ∑ k ∈ Finset.Icc 1 M,
        hurwitzBernoulliCoeff k q.2 *
          dslope (fun w : ℂ ↦ (Complex.Gamma w)⁻¹) (-((k - 1 : ℕ) : ℂ)) q.1) p :=
      DifferentiableAt.fun_sum fun k _ =>
        ((differentiable_hurwitzBernoulliCoeff k p.2).comp p differentiableAt_snd).mul
          (((differentiableOn_univ.mp ((Complex.differentiableOn_dslope Filter.univ_mem).mpr
            Complex.differentiable_one_div_Gamma.differentiableOn)) p.1).comp
              p differentiableAt_fst)
    exact ((((Complex.differentiable_one_div_Gamma p.1).comp p differentiableAt_fst).mul
      ((analyticOnNhd_hurwitzHeadIntegral M p hp.1).differentiableAt.add
        (analyticOnNhd_hurwitzTailIntegral p hp.2).differentiableAt)).add
      hd_sum).differentiableWithinAt
  simpa only [hurwitzStageCore_def] using hdiff.analyticOnNhd_of_finiteDimensional
    ((isOpen_lt continuous_const (continuous_re.comp continuous_fst)).inter
      (isOpen_lt continuous_const (continuous_re.comp continuous_snd)))

/-- Recursive stage relation for `hurwitzHeadIntegral` on `-(M : ℝ) < s.re`. -/
theorem hurwitzHeadIntegral_eq_add_succ (M : ℕ) {s : ℂ} (hs : -(M : ℝ) < s.re) (c : ℂ) :
    hurwitzHeadIntegral M s c =
      hurwitzBernoulliCoeff (M + 1) c / (s + M) + hurwitzHeadIntegral (M + 1) s c := by
  have hint1 : IntegrableOn
      (fun t : ℝ => hurwitzBernoulliCoeff (M + 1) c * (t : ℂ) ^ (s + M - 1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) (by simp; linarith)).1.const_mul _
  have hint2 : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s + ((M + 1 : ℕ) : ℂ) - 1) * hurwitzTaylorQuot (M + 1) c t)
      (Ioc 0 1) :=
    integrableOn_hurwitzHeadIntegrand (M + 1) (by push_cast; linarith)
  have hcongr : EqOn (fun t : ℝ => (t : ℂ) ^ (s + M - 1) * hurwitzTaylorQuot M c t)
      (fun t : ℝ => hurwitzBernoulliCoeff (M + 1) c * (t : ℂ) ^ (s + M - 1) +
        (t : ℂ) ^ (s + ((M + 1 : ℕ) : ℂ) - 1) * hurwitzTaylorQuot (M + 1) c t)
      (Ioc 0 1) := fun t ht => by
    dsimp only
    have hpow : (t : ℂ) ^ (s + M - 1) * (t : ℂ) =
        (t : ℂ) ^ (s + ((M + 1 : ℕ) : ℂ) - 1) := by
      have h := (cpow_add (s + M - 1) 1 (ofReal_ne_zero.mpr ht.1.ne')).symm
      rw [cpow_one] at h; exact h.trans (congrArg _ (by push_cast; ring))
    rw [hurwitzTaylorQuot_eq_add_mul_succ M c t, mul_add, mul_comm ((t : ℂ) ^ _),
      ← mul_assoc ((t : ℂ) ^ _), hpow]
  unfold hurwitzHeadIntegral
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_add hint1 hint2, integral_const_mul,
    integral_Ioc_zero_cpow (by simp; linarith) zero_le_one]
  simp [sub_add_cancel, div_eq_mul_inv]

/-- Consecutive stages of `hurwitzStageCore` agree on `-(M : ℝ) < s.re`. -/
theorem hurwitzStageCore_succ_eq (M : ℕ) {s : ℂ} (hs : -(M : ℝ) < s.re) (c : ℂ) :
    hurwitzStageCore (M + 1) s c = hurwitzStageCore M s c := by
  have hsm_ne : s + M ≠ 0 := fun h0 => by
    have hre := congrArg Complex.re h0; simp at hre; linarith
  have hslope :
      (s + (M : ℂ)) * dslope (fun w ↦ (Gamma w)⁻¹) (-(M : ℂ)) s = (Gamma s)⁻¹ := by
    simpa [sub_neg_eq_add, smul_eq_mul, Gamma_neg_nat_eq_zero] using
      sub_smul_dslope_of_zero (f := fun w : ℂ ↦ (Gamma w)⁻¹) (a := -(M : ℂ))
        (by simp [Gamma_neg_nat_eq_zero]) s
  have hdiv : (Gamma s)⁻¹ * (hurwitzBernoulliCoeff (M + 1) c / (s + M)) =
      hurwitzBernoulliCoeff (M + 1) c * dslope (fun w ↦ (Gamma w)⁻¹) (-(M : ℂ)) s := by
    rw [← hslope]; field_simp
  unfold hurwitzStageCore
  rw [hurwitzHeadIntegral_eq_add_succ M hs c, Finset.sum_Icc_succ_top (by omega),
    Nat.add_sub_cancel]
  linear_combination -hdiv

/-- Any two stages `M ≤ N` of `hurwitzStageCore` agree on `-(M : ℝ) < s.re`. -/
theorem hurwitzStageCore_eq_of_le {M N : ℕ} (hMN : M ≤ N) {s : ℂ}
    (hs : -(M : ℝ) < s.re) (c : ℂ) :
    hurwitzStageCore N s c = hurwitzStageCore M s c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMN; clear hMN
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, hurwitzStageCore_succ_eq (M + d) (by push_cast; linarith) c, ih]

private noncomputable def hurwitzStageIndex (s : ℂ) : ℕ :=
  ⌊max 0 (1 - s.re)⌋₊ + 1

private noncomputable def hurwitzCore (s c : ℂ) : ℂ :=
  hurwitzStageCore (hurwitzStageIndex s) s c

private theorem neg_hurwitzStageIndex_lt_re (s : ℂ) : -(hurwitzStageIndex s : ℝ) < s.re := by
  unfold hurwitzStageIndex
  have h1 : 1 - s.re ≤ max 0 (1 - s.re) := le_max_right _ _
  have h2 : max 0 (1 - s.re) < (⌊max 0 (1 - s.re)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  push_cast; linarith

private theorem hurwitzCore_eq_stage {M : ℕ} {s : ℂ} (hs : -(M : ℝ) < s.re) (c : ℂ) :
    hurwitzCore s c = hurwitzStageCore M s c := by
  unfold hurwitzCore
  rcases le_total M (hurwitzStageIndex s) with hle | hge
  · exact hurwitzStageCore_eq_of_le hle hs c
  · exact (hurwitzStageCore_eq_of_le hge (neg_hurwitzStageIndex_lt_re s) c).symm

private theorem analyticOnNhd_hurwitzCore :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzCore p.1 p.2) {p | 0 < p.2.re} := by
  intro p₀ hp₀
  set N := hurwitzStageIndex p₀.1
  have hp₀_mem : p₀ ∈ {p : ℂ × ℂ | -(N : ℝ) < p.1.re ∧ 0 < p.2.re} :=
    ⟨neg_hurwitzStageIndex_lt_re p₀.1, hp₀⟩
  have hopen : {p : ℂ × ℂ | -(N : ℝ) < p.1.re ∧ 0 < p.2.re} ∈ 𝓝 p₀ :=
    ((isOpen_lt continuous_const (continuous_re.comp continuous_fst)).inter
      (isOpen_lt continuous_const (continuous_re.comp continuous_snd))).mem_nhds hp₀_mem
  refine (analyticOnNhd_hurwitzStageCore N p₀ hp₀_mem).congr ?_
  filter_upwards [hopen] with p hp
  exact (hurwitzCore_eq_stage hp.1 p.2).symm

/-- For `0 < c.re`, the canonical meromorphic continuation of `complexHurwitzSeries s c` in
`s ∈ ℂ`, jointly holomorphic on `{p : ℂ × ℂ | p.1 ≠ 1 ∧ 0 < p.2.re}`. -/
noncomputable def complexHurwitzZeta (s c : ℂ) : ℂ :=
  (Gamma s)⁻¹ / (s - 1) + hurwitzCore s c

/-- The `(s - 1)`-multiplied companion to `complexHurwitzZeta` on `{p : ℂ × ℂ | 0 < p.2.re}`,
jointly holomorphic across `s = 1` with `complexHurwitzZeta₁ 1 c = 1` and
`complexHurwitzZeta₁ s c = (s - 1) * complexHurwitzZeta s c` for `s ≠ 1`. -/
noncomputable def complexHurwitzZeta₁ (s c : ℂ) : ℂ :=
  (Gamma s)⁻¹ + (s - 1) * hurwitzCore s c

/-- Stage-`M` representation of `complexHurwitzZeta s c` on `-(M : ℝ) < s.re`. -/
theorem complexHurwitzZeta_eq_inv_Gamma_div_add_hurwitzStageCore {M : ℕ} {s : ℂ}
    (hs : -(M : ℝ) < s.re) (c : ℂ) :
    complexHurwitzZeta s c = (Gamma s)⁻¹ / (s - 1) + hurwitzStageCore M s c := by
  rw [complexHurwitzZeta, hurwitzCore_eq_stage hs c]

/-- Stage-`M` representation of `complexHurwitzZeta₁ s c` on `-(M : ℝ) < s.re`. -/
theorem complexHurwitzZeta₁_eq_inv_Gamma_add_mul_hurwitzStageCore {M : ℕ} {s : ℂ}
    (hs : -(M : ℝ) < s.re) (c : ℂ) :
    complexHurwitzZeta₁ s c = (Gamma s)⁻¹ + (s - 1) * hurwitzStageCore M s c := by
  rw [complexHurwitzZeta₁, hurwitzCore_eq_stage hs c]

/-- Away from `s = 1`, `complexHurwitzZeta₁ s c = (s - 1) * complexHurwitzZeta s c`. -/
theorem complexHurwitzZeta₁_eq_sub_one_mul {s : ℂ} (hs : s ≠ 1) (c : ℂ) :
    complexHurwitzZeta₁ s c = (s - 1) * complexHurwitzZeta s c := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold complexHurwitzZeta₁ complexHurwitzZeta
  field_simp

/-- At `s = 1`, `complexHurwitzZeta₁ 1 c = 1`. -/
@[simp]
theorem complexHurwitzZeta₁_one_left (c : ℂ) : complexHurwitzZeta₁ 1 c = 1 := by
  simp [complexHurwitzZeta₁, Gamma_one]

private theorem complexHurwitzZeta_sub_inv_Gamma_div (s c : ℂ) :
    complexHurwitzZeta s c - (Gamma s)⁻¹ / (s - 1) = hurwitzCore s c := by
  simp [complexHurwitzZeta]

/-- Subtracting the defining polar term `(Gamma s)⁻¹ / (s - 1)` from `complexHurwitzZeta s c`
yields a function jointly analytic on `{p : ℂ × ℂ | 0 < p.2.re}`. -/
theorem analyticOnNhd_complexHurwitzZeta_sub_inv_Gamma_div :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => complexHurwitzZeta p.1 p.2 - (Gamma p.1)⁻¹ / (p.1 - 1))
      {p | 0 < p.2.re} := by
  simp_rw [complexHurwitzZeta_sub_inv_Gamma_div]
  exact analyticOnNhd_hurwitzCore

/-- `(s, c) ↦ complexHurwitzZeta₁ s c` is jointly analytic on
`{p : ℂ × ℂ | 0 < p.2.re}`. -/
theorem analyticOnNhd_complexHurwitzZeta₁ :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => complexHurwitzZeta₁ p.1 p.2) {p | 0 < p.2.re} :=
  fun p hp =>
    ((differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ
      p.1 trivial).comp analyticAt_fst).add
        ((analyticAt_fst.sub analyticAt_const).mul (analyticOnNhd_hurwitzCore p hp))

/-- `(s, c) ↦ complexHurwitzZeta₁ s c` is jointly complex differentiable on
`{p : ℂ × ℂ | 0 < p.2.re}`. -/
theorem differentiableOn_complexHurwitzZeta₁ :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => complexHurwitzZeta₁ p.1 p.2) {p | 0 < p.2.re} :=
  analyticOnNhd_complexHurwitzZeta₁.differentiableOn

/-- For fixed `c` with `0 < c.re`, `s ↦ complexHurwitzZeta₁ s c` is analytic at every `s : ℂ`. -/
theorem analyticAt_complexHurwitzZeta₁_left (s : ℂ) {c : ℂ} (hc : 0 < c.re) :
    AnalyticAt ℂ (fun w => complexHurwitzZeta₁ w c) s :=
  (analyticOnNhd_complexHurwitzZeta₁ (s, c) hc).comp (f := fun w : ℂ => (w, c))
    (analyticAt_id.prod analyticAt_const)

/-- For fixed `c` with `0 < c.re`, `s ↦ complexHurwitzZeta₁ s c` is an entire function. -/
theorem differentiable_complexHurwitzZeta₁_left {c : ℂ} (hc : 0 < c.re) :
    Differentiable ℂ (fun s => complexHurwitzZeta₁ s c) := fun s =>
  (analyticAt_complexHurwitzZeta₁_left s hc).differentiableAt

/-- For any `s : ℂ`, `c ↦ complexHurwitzZeta₁ s c` is complex differentiable at every `c`
with `0 < c.re`. -/
theorem differentiableAt_complexHurwitzZeta₁_right (s : ℂ) {c : ℂ} (hc : 0 < c.re) :
    DifferentiableAt ℂ (complexHurwitzZeta₁ s) c :=
  ((analyticOnNhd_complexHurwitzZeta₁ (s, c) hc).comp (f := fun w : ℂ => (s, w))
    (analyticAt_const.prod analyticAt_id)).differentiableAt

/-- `(s, c) ↦ complexHurwitzZeta s c` is jointly analytic on
`{p : ℂ × ℂ | p.1 ≠ 1 ∧ 0 < p.2.re}`. -/
theorem analyticOnNhd_complexHurwitzZeta :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => complexHurwitzZeta p.1 p.2)
      {p | p.1 ≠ 1 ∧ 0 < p.2.re} := by
  intro p₀ hp₀
  refine ((analyticOnNhd_complexHurwitzZeta₁ p₀ hp₀.2).div
    (analyticAt_fst.sub analyticAt_const) (sub_ne_zero.mpr hp₀.1)).congr ?_
  filter_upwards [(isOpen_ne.preimage continuous_fst).mem_nhds hp₀.1] with p hp
  simp only [Pi.div_apply, Pi.sub_apply]
  rw [complexHurwitzZeta₁_eq_sub_one_mul hp p.2, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hp)]

/-- `(s, c) ↦ complexHurwitzZeta s c` is jointly complex differentiable on
`{p : ℂ × ℂ | p.1 ≠ 1 ∧ 0 < p.2.re}`. -/
theorem differentiableOn_complexHurwitzZeta :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => complexHurwitzZeta p.1 p.2)
      {p | p.1 ≠ 1 ∧ 0 < p.2.re} :=
  analyticOnNhd_complexHurwitzZeta.differentiableOn

/-- For fixed `c` with `0 < c.re`, `s ↦ complexHurwitzZeta s c` is analytic at every `s ≠ 1`. -/
theorem analyticAt_complexHurwitzZeta_left {s c : ℂ} (hs : s ≠ 1) (hc : 0 < c.re) :
    AnalyticAt ℂ (fun w => complexHurwitzZeta w c) s :=
  (analyticOnNhd_complexHurwitzZeta (s, c) ⟨hs, hc⟩).comp (f := fun w : ℂ => (w, c))
    (analyticAt_id.prod analyticAt_const)

/-- For fixed `c` with `0 < c.re`, `s ↦ complexHurwitzZeta s c` is complex differentiable on
`{1}ᶜ`. -/
theorem differentiableOn_complexHurwitzZeta_left {c : ℂ} (hc : 0 < c.re) :
    DifferentiableOn ℂ (fun s => complexHurwitzZeta s c) ({1}ᶜ : Set ℂ) := fun _ hz =>
  (analyticAt_complexHurwitzZeta_left hz hc).differentiableAt.differentiableWithinAt

/-- For fixed `c` with `0 < c.re`, `s ↦ complexHurwitzZeta s c` is complex differentiable at
every `s ≠ 1`. -/
theorem differentiableAt_complexHurwitzZeta_left {s c : ℂ} (hs : s ≠ 1) (hc : 0 < c.re) :
    DifferentiableAt ℂ (fun w => complexHurwitzZeta w c) s :=
  (analyticAt_complexHurwitzZeta_left hs hc).differentiableAt

/-- For fixed `s ≠ 1`, `c ↦ complexHurwitzZeta s c` is complex differentiable at every `c` with
`0 < c.re`. -/
theorem differentiableAt_complexHurwitzZeta_right {s c : ℂ} (hs : s ≠ 1) (hc : 0 < c.re) :
    DifferentiableAt ℂ (complexHurwitzZeta s) c :=
  ((analyticOnNhd_complexHurwitzZeta (s, c) ⟨hs, hc⟩).comp (f := fun w : ℂ => (s, w))
    (analyticAt_const.prod analyticAt_id)).differentiableAt

/-- Near `s = 1` on `𝓝[≠] 1`, `complexHurwitzZeta s c` agrees with
`(s - 1) ^ (-1 : ℤ) • complexHurwitzZeta₁ s c`. -/
theorem complexHurwitzZeta_eventuallyEq_nhdsNE_one {c : ℂ} :
    (fun s => complexHurwitzZeta s c) =ᶠ[𝓝[≠] 1]
      fun s => (s - 1) ^ (-1 : ℤ) • complexHurwitzZeta₁ s c :=
  eventually_nhdsWithin_of_forall fun s hs => by
    dsimp only
    rw [zpow_neg_one, smul_eq_mul, complexHurwitzZeta₁_eq_sub_one_mul hs c]
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    field_simp

/-- For fixed `c` with `0 < c.re`, `s ↦ complexHurwitzZeta s c` is meromorphic on `ℂ`. -/
theorem meromorphic_complexHurwitzZeta_left {c : ℂ} (hc : 0 < c.re) :
    Meromorphic (fun s => complexHurwitzZeta s c) := by
  intro s; by_cases hs : s = 1
  · subst hs
    exact MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr
      ⟨-1, fun w => complexHurwitzZeta₁ w c, analyticAt_complexHurwitzZeta₁_left 1 hc,
        complexHurwitzZeta_eventuallyEq_nhdsNE_one⟩
  · exact (analyticAt_complexHurwitzZeta_left hs hc).meromorphicAt

/-- For fixed `c` with `0 < c.re`, `s ↦ complexHurwitzZeta s c` has meromorphic order `-1` at
`s = 1`. -/
theorem meromorphicOrderAt_complexHurwitzZeta_one {c : ℂ} (hc : 0 < c.re) :
    meromorphicOrderAt (fun s => complexHurwitzZeta s c) 1 = (-1 : ℤ) :=
  (meromorphicOrderAt_eq_int_iff (meromorphic_complexHurwitzZeta_left hc 1)).mpr
    ⟨fun s => complexHurwitzZeta₁ s c, analyticAt_complexHurwitzZeta₁_left 1 hc,
      by simp [complexHurwitzZeta₁_one_left], complexHurwitzZeta_eventuallyEq_nhdsNE_one⟩

/-- For fixed `c` with `0 < c.re`, `s ↦ complexHurwitzZeta s c` has trailing coefficient `1` at
`s = 1`. -/
theorem meromorphicTrailingCoeffAt_complexHurwitzZeta_one {c : ℂ} (hc : 0 < c.re) :
    meromorphicTrailingCoeffAt (fun s => complexHurwitzZeta s c) 1 = 1 := by
  simpa [complexHurwitzZeta₁_one_left] using
    (analyticAt_complexHurwitzZeta₁_left 1 hc).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
      (by simp) complexHurwitzZeta_eventuallyEq_nhdsNE_one

/-- `complexHurwitzZeta s c` has a simple pole of residue `1` at `s = 1` for every `0 < c.re`. -/
theorem tendsto_sub_one_mul_complexHurwitzZeta {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun s => (s - 1) * complexHurwitzZeta s c) (𝓝[≠] 1) (𝓝 1) := by
  have h := (meromorphic_complexHurwitzZeta_left hc 1).tendsto_nhds_meromorphicTrailingCoeffAt
  rw [meromorphicOrderAt_complexHurwitzZeta_one hc,
    meromorphicTrailingCoeffAt_complexHurwitzZeta_one hc] at h
  exact h.congr fun s => by simp [smul_eq_mul]

/-! ### Mellin–Laplace integral representation and agreement with `complexHurwitzSeries` -/

private theorem eqOn_hurwitzStageZero_add_cpow (s c : ℂ) :
    EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * hurwitzTaylorQuot 0 c t + (t : ℂ) ^ (s - 2))
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t))))
      (Ioc 0 1) := fun t ht => by
  dsimp only
  have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
  have hdecomp := hurwitzKernel_sub_sum_eq_pow_mul_hurwitzTaylorQuot 0 c t
  simp only [Finset.range_one, Finset.sum_singleton, hurwitzBernoulliCoeff_zero, pow_zero,
    mul_one, zero_add, pow_one] at hdecomp
  have hpow : (t : ℂ) ^ (s - 1) = (t : ℂ) ^ (s - 2) * (t : ℂ) := by
    have h := cpow_add (s - 2) 1 ht_ne
    rw [cpow_one] at h; exact (congrArg _ (by ring)).trans h
  rw [hpow, mul_assoc, ← hdecomp, hurwitzKernel_of_ne_zero c ht_ne]
  ring

/-- For `1 < s.re` and `0 < c.re`, the Mellin–Laplace integrand
`t ↦ (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))` is integrable on `Ioi 0`. -/
theorem integrableOn_hurwitzMellinIntegrand {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))) (Ioi 0) := by
  have hs0 : -((0 : ℕ) : ℝ) < s.re := by simp; linarith
  have hint_Ioc : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))) (Ioc 0 1) :=
    ((integrableOn_hurwitzHeadIntegrand 0 (c := c) hs0).add
      (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) (r := s - 2)
        (by simp; linarith)).1).congr_fun
      (fun t ht => by simpa using eqOn_hurwitzStageZero_add_cpow s c ht) measurableSet_Ioc
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hint_Ioc.union (integrableOn_hurwitzTailIntegrand s hc)

private theorem hurwitzHeadIntegral_zero_add_one_div {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    hurwitzHeadIntegral 0 s c + 1 / (s - 1) =
      ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t))) := by
  have hs0 : -((0 : ℕ) : ℝ) < s.re := by simp; linarith
  have h1div : (1 : ℂ) / (s - 1) = ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 2) := by
    have hexp : s - (2 : ℂ) + 1 = s - 1 := by ring
    rw [integral_Ioc_zero_cpow (by simp; linarith) zero_le_one, hexp]
    simp
  unfold hurwitzHeadIntegral
  rw [h1div, ← integral_add (integrableOn_hurwitzHeadIntegrand 0 hs0)
    (intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1) (r := s - 2)
      (by simp; linarith)).1]
  exact setIntegral_congr_fun measurableSet_Ioc fun t ht => by
    simpa using eqOn_hurwitzStageZero_add_cpow s c ht

/-- **Mellin–Laplace integral representation of the complex Hurwitz zeta function.** For
`1 < s.re` and `0 < c.re`, `complexHurwitzZeta s c` equals `(Gamma s)⁻¹` times the integral of
`t ^ (s - 1) * exp (-c * t) / (1 - exp (-t))` over `(0, ∞)`. -/
theorem complexHurwitzZeta_eq_inv_Gamma_mul_integral_Ioi {s c : ℂ} (hs : 1 < s.re)
    (hc : 0 < c.re) :
    complexHurwitzZeta s c =
      (Gamma s)⁻¹ *
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t))) := by
  have hs0 : -((0 : ℕ) : ℝ) < s.re := by simp; linarith
  have hint_Ioc : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))) (Ioc 0 1) :=
    (integrableOn_hurwitzMellinIntegrand hs hc).mono_set Ioc_subset_Ioi_self
  rw [complexHurwitzZeta, hurwitzCore_eq_stage hs0 c]
  unfold hurwitzStageCore hurwitzTailIntegral
  rw [Finset.Icc_eq_empty_of_lt one_pos, Finset.sum_empty, add_zero]
  let tail := ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))
  have hcomb : (Gamma s)⁻¹ / (s - 1) + (Gamma s)⁻¹ * (hurwitzHeadIntegral 0 s c + tail) =
      (Gamma s)⁻¹ * ((hurwitzHeadIntegral 0 s c + 1 / (s - 1)) + tail) := by ring
  rw [hcomb, hurwitzHeadIntegral_zero_add_one_div hs c,
    ← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint_Ioc (integrableOn_hurwitzTailIntegrand s hc), Ioc_union_Ioi_eq_Ioi zero_le_one]

/-- For `1 < s.re` and `0 < c.re`, the continuation `complexHurwitzZeta s c` agrees with the
convergent series `complexHurwitzSeries s c`. -/
theorem complexHurwitzZeta_eq_complexHurwitzSeries {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    complexHurwitzZeta s c = complexHurwitzSeries s c := by
  have hs_pos : 0 < s.re := by linarith
  rw [complexHurwitzZeta_eq_inv_Gamma_mul_integral_Ioi hs hc]
  have hkernel : EqOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t))))
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (exp ((1 - c) * t) / (exp t - 1))) (Ioi 0) :=
    fun t _ => by
      dsimp only
      congr 1
      have hexp : exp (t : ℂ) - 1 = exp (t : ℂ) * (1 - exp (-(t : ℂ))) := by
        rw [mul_sub, mul_one, ← exp_add, add_neg_cancel, exp_zero]
      have hnum : exp ((1 - c) * (t : ℂ)) = exp (t : ℂ) * exp (-c * (t : ℂ)) := by
        rw [← exp_add]; congr 1; ring
      rw [hnum, hexp, mul_div_mul_left _ _ (exp_ne_zero _)]
  rw [setIntegral_congr_fun measurableSet_Ioi hkernel]
  have hsum := (hasSum_setIntegral_cpow_mul_exp_neg_mul hs hc subset_rfl).mul_left (Gamma s)⁻¹
  have hterm : (fun k : ℕ => (Gamma s)⁻¹ *
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(((k : ℂ) + c) * t))) =
      fun k : ℕ => ((k : ℂ) + c) ^ (-s) := funext fun k => by
    have hk : 0 < ((k : ℂ) + c).re := by
      simp only [add_re, natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    rw [integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs_pos hk,
      inv_mul_cancel_left₀ (Gamma_ne_zero_of_re_pos hs_pos)]
  rw [hterm] at hsum
  exact hsum.unique (hasSum_complexHurwitzSeries_of_re_pos hs hc)

/-! ### Nonpositive integer Bernoulli values -/

private theorem complexHurwitzZeta_neg_nat_eq_hurwitzBernoulliCoeff (m : ℕ) (c : ℂ) :
    complexHurwitzZeta (-(m : ℂ)) c =
      hurwitzBernoulliCoeff (m + 1) c * ((-1 : ℂ) ^ m * m.factorial) := by
  have hlt : -((m + 1 : ℕ) : ℝ) < (-(m : ℂ)).re := by push_cast; simp
  rw [complexHurwitzZeta, hurwitzCore_eq_stage hlt c]
  unfold hurwitzStageCore
  simp only [Gamma_neg_nat_eq_zero, inv_zero, zero_div, zero_mul, zero_add]
  have hterm : ∀ k ∈ Finset.Icc 1 (m + 1), hurwitzBernoulliCoeff k c *
        dslope (fun w : ℂ ↦ (Gamma w)⁻¹) (-((k - 1 : ℕ) : ℂ)) (-(m : ℂ)) =
      if k = m + 1 then hurwitzBernoulliCoeff (m + 1) c * ((-1 : ℂ) ^ m * m.factorial)
      else 0 := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [dslope_inv_Gamma_neg_nat (k - 1) m]
    have heq : (k - 1 = m) ↔ (k = m + 1) := by omega
    by_cases hkm : k = m + 1
    · subst hkm; simp
    · simp [hkm, heq.not.mpr hkm]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.Icc 1 (m + 1)) (m + 1)]
  simp

/-- At every nonpositive integer `-m`, `complexHurwitzZeta (-m) c = -B_{m + 1}(c) / (m + 1)`
(the canonical continuation value when `0 < c.re`). -/
theorem complexHurwitzZeta_neg_nat (m : ℕ) (c : ℂ) :
    complexHurwitzZeta (-(m : ℂ)) c =
      -((Polynomial.bernoulli (m + 1)).map (algebraMap ℚ ℂ)).eval c / (m + 1) := by
  rw [complexHurwitzZeta_neg_nat_eq_hurwitzBernoulliCoeff, hurwitzBernoulliCoeff_def,
    Polynomial.eval_map_algebraMap, Nat.factorial_succ]
  have hfm : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hm1 : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hsign : (-1 : ℂ) ^ (m + 1) * (-1 : ℂ) ^ m = -1 := by
    rw [pow_succ', mul_assoc, ← mul_pow]; norm_num
  push_cast; field_simp
  linear_combination Polynomial.aeval c (Polynomial.bernoulli (m + 1)) * hsign

/-- At `s = 0`, `complexHurwitzZeta 0 c = 1 / 2 - c`. -/
@[simp]
theorem complexHurwitzZeta_zero_left (c : ℂ) : complexHurwitzZeta 0 c = 1 / 2 - c := by
  simpa using complexHurwitzZeta_neg_nat_eq_hurwitzBernoulliCoeff 0 c

example : complexHurwitzZeta (-1) 1 = -1 / 12 := by
  have h := complexHurwitzZeta_neg_nat 1 1
  simp only [Nat.cast_one, Polynomial.eval_one_map, Polynomial.bernoulli_eval_one] at h
  rw [h]; norm_num

/-! ### Packaged continuation theorem -/

/-- Joint meromorphic continuation of the complex-parameter Hurwitz zeta function, with its
`(s - 1)`-multiplied companion, unit residue at `s = 1`, and Bernoulli polynomial values at all
nonpositive integers. -/
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
  ⟨fun p => complexHurwitzZeta p.1 p.2, fun p => complexHurwitzZeta₁ p.1 p.2,
    differentiableOn_complexHurwitzZeta, differentiableOn_complexHurwitzZeta₁, fun c hc =>
      ⟨fun _ hs => complexHurwitzZeta_eq_complexHurwitzSeries hs hc,
        complexHurwitzZeta₁_one_left c,
        fun _ hs => complexHurwitzZeta₁_eq_sub_one_mul hs c,
        fun m => complexHurwitzZeta_neg_nat m c⟩⟩

/-- Uniqueness of the meromorphic continuation of `complexHurwitzSeries · c` for `0 < c.re`:
any function holomorphic on `{1}ᶜ` agreeing with `complexHurwitzSeries · c` on
`{s | max 1 b < s.re}` equals `complexHurwitzZeta · c` away from `s = 1`. -/
theorem eq_complexHurwitzZeta_of_eqOn_re_gt {c : ℂ} (hc : 0 < c.re) {H : ℂ → ℂ} {b : ℝ}
    (hH : DifferentiableOn ℂ H ({1}ᶜ))
    (hagree : EqOn H (fun s => complexHurwitzSeries s c) {s | max 1 b < s.re})
    {s : ℂ} (hs : s ≠ 1) :
    H s = complexHurwitzZeta s c := by
  refine hH.eqOn_compl_singleton_of_eqOn_re_gt (b := max 1 b)
    (differentiableOn_complexHurwitzZeta_left hc) (fun z hz => ?_) hs
  dsimp only
  rw [hagree hz.2, complexHurwitzZeta_eq_complexHurwitzSeries ((le_max_left 1 b).trans_lt hz.2) hc]

/-- Uniqueness of the regularized companion `complexHurwitzZeta₁ · c` for `0 < c.re`: any
function continuous at `s = 1` and equal to `(s - 1) * complexHurwitzZeta s c` away from `s = 1`
equals `complexHurwitzZeta₁ s c` for every `s : ℂ`. -/
theorem eq_complexHurwitzZeta₁_of_eq_sub_one_mul {c : ℂ} (hc : 0 < c.re) {R : ℂ → ℂ}
    (hRc : ContinuousAt R 1)
    (hrel : ∀ {s : ℂ}, s ≠ 1 → R s = (s - 1) * complexHurwitzZeta s c) (s : ℂ) :
    R s = complexHurwitzZeta₁ s c := by
  by_cases hs : s = 1
  · subst hs
    have heq : R =ᶠ[𝓝[≠] 1] fun z => complexHurwitzZeta₁ z c :=
      eventually_mem_nhdsWithin.mono fun z hz => by
        dsimp only
        rw [hrel hz, complexHurwitzZeta₁_eq_sub_one_mul hz c]
    exact ((hRc.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (differentiable_complexHurwitzZeta₁_left hc 1).continuousAt).mp heq).eq_of_nhds
  · rw [hrel hs, complexHurwitzZeta₁_eq_sub_one_mul hs c]

/-- Uniqueness of the regularized companion `complexHurwitzZeta₁ · c` for `0 < c.re`: if `H` is
holomorphic on `{1}ᶜ` and agrees with `complexHurwitzSeries · c` on `{s | max 1 b < s.re}`, and
`R` is continuous at `1` with `R s = (s - 1) * H s` for `s ≠ 1`, then
`R s = complexHurwitzZeta₁ s c` for all `s : ℂ` (see `eq_complexHurwitzZeta_of_eqOn_re_gt` for
uniqueness of `H` off the pole). -/
theorem eq_complexHurwitzZeta₁_of_eqOn_re_gt {c : ℂ} (hc : 0 < c.re) {H R : ℂ → ℂ}
    {b : ℝ} (hH : DifferentiableOn ℂ H ({1}ᶜ)) (hRc : ContinuousAt R 1)
    (hagree : EqOn H (fun s => complexHurwitzSeries s c) {s | max 1 b < s.re})
    (hrel : ∀ {s : ℂ}, s ≠ 1 → R s = (s - 1) * H s) (s : ℂ) :
    R s = complexHurwitzZeta₁ s c :=
  eq_complexHurwitzZeta₁_of_eq_sub_one_mul hc hRc
    (fun hs => by rw [hrel hs, eq_complexHurwitzZeta_of_eqOn_re_gt hc hH hagree hs]) s

/-! ### Analytic continuation of the shift and circle comparison -/

/-- The `c ↦ c + 1` shift identity extends to all `s ≠ 1` and `0 < c.re`. -/
theorem complexHurwitzZeta_add_one_right {s c : ℂ} (hs : s ≠ 1) (hc : 0 < c.re) :
    complexHurwitzZeta s (c + 1) = complexHurwitzZeta s c - c ^ (-s) := by
  have hc1 : 0 < (c + 1).re := by simp; linarith
  have hc_ne : c ≠ 0 := fun h0 => lt_irrefl (0 : ℝ) (by rwa [h0, zero_re] at hc)
  have hdg : DifferentiableOn ℂ (fun z => complexHurwitzZeta z c - c ^ (-z)) ({1}ᶜ) :=
    fun _ hz => ((differentiableAt_complexHurwitzZeta_left hz hc).sub
      (differentiableAt_id.neg.const_cpow (Or.inl hc_ne))).differentiableWithinAt
  exact (eq_complexHurwitzZeta_of_eqOn_re_gt hc1 (b := 1) hdg (fun z hz => by
    have hz1 : 1 < z.re := by simpa using hz
    dsimp only
    rw [complexHurwitzZeta_eq_complexHurwitzSeries hz1 hc,
      complexHurwitzSeries_add_one_right hz1 hc_ne]) hs).symm

/-- For real `x ∈ (0, 1]` and `s ≠ 1`, `complexHurwitzZeta s x` agrees with Mathlib's
`HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`. -/
theorem complexHurwitzZeta_ofReal_eq_hurwitzZeta {s : ℂ} {x : ℝ} (hs : s ≠ 1)
    (hx : x ∈ Ioc 0 1) :
    complexHurwitzZeta s x = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s := by
  have hx_re : 0 < (x : ℂ).re := by simp [hx.1]
  have hdg : DifferentiableOn ℂ (HurwitzZeta.hurwitzZeta (x : UnitAddCircle))
      ({1}ᶜ : Set ℂ) :=
    fun _ hz => (HurwitzZeta.differentiableAt_hurwitzZeta _ hz).differentiableWithinAt
  exact (eq_complexHurwitzZeta_of_eqOn_re_gt hx_re (b := 1) hdg (fun z hz => by
    have hz1 : 1 < z.re := by simpa using hz
    exact (complexHurwitzSeries_ofReal_eq_hurwitzZeta hz1 hx).symm) hs).symm

/-- At `c = 1` and `s ≠ 1`, `complexHurwitzZeta s 1 = riemannZeta s`. -/
theorem complexHurwitzZeta_one_right {s : ℂ} (hs : s ≠ 1) :
    complexHurwitzZeta s 1 = riemannZeta s := by
  have h := complexHurwitzZeta_ofReal_eq_hurwitzZeta (x := 1) hs (right_mem_Ioc.mpr zero_lt_one)
  rwa [ofReal_one, AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero] at h

/-- At `c = 1 / 2` and `s ≠ 1`, `complexHurwitzZeta s (1 / 2) = (2 ^ s - 1) * riemannZeta s`. -/
theorem complexHurwitzZeta_one_half_right {s : ℂ} (hs : s ≠ 1) :
    complexHurwitzZeta s (1 / 2) = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  have hhalf_re : 0 < (1 / 2 : ℂ).re := by norm_num
  have hdg : DifferentiableOn ℂ (fun z => ((2 : ℂ) ^ z - 1) * riemannZeta z) ({1}ᶜ) :=
    fun _ hz => (((differentiableAt_id.const_cpow (Or.inl two_ne_zero)).sub
      (differentiableAt_const 1)).mul (differentiableAt_riemannZeta hz)).differentiableWithinAt
  exact (eq_complexHurwitzZeta_of_eqOn_re_gt hhalf_re (b := 1) hdg (fun z hz => by
    have hz1 : 1 < z.re := by simpa using hz
    exact (complexHurwitzSeries_one_half_right hz1).symm) hs).symm

end TauCeti

namespace HurwitzZeta

/-- For `x ∈ (0, 1]`, `hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - x`. -/
@[simp]
theorem hurwitzZeta_apply_zero_of_mem_Ioc {x : ℝ} (hx : x ∈ Ioc 0 1) :
    hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - x := by
  rw [← TauCeti.complexHurwitzZeta_ofReal_eq_hurwitzZeta zero_ne_one hx,
    TauCeti.complexHurwitzZeta_zero_left]

end HurwitzZeta

end
