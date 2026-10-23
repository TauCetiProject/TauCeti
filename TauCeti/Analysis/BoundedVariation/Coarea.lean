/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.Calculus.Rademacher
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.LayerCake

/-!
# The coarea formula for total variation

For a function `u` on an open set `Ω` of a finite-dimensional real inner product space, the
**coarea formula** `|Du|(Ω) = ∫_ℝ P({u > t}; Ω) dt` expresses the total variation of `u` as the
integral over all levels of the perimeters of its superlevel sets. Here `|Du|(Ω)` is the
variational supremum `TauCeti.totalVariationOn` and `P(·; Ω)` is `TauCeti.perimeter`, both
against an additive Haar measure; the level integral is an extended Lebesgue integral.

The formula holds for every locally integrable function, finite or infinite:

* the layer-cake formula for the distributional pairing, `∫ u div φ = ∫_ℝ (∫_{u > t} div φ) dt`,
  which follows from writing `u x = ∫_ℝ (1_{t < u x} - 1_{t < 0}) dt`, Fubini's theorem and
  `∫ div φ = 0`;
* hence the coarea inequality `|Du|(Ω) ≤ ∫_ℝ P({u > t}; Ω) dt`, testing each superlevel set
  against the same vector field;
* the reverse inequality, by smooth approximation. Around each compact subset of `Ω`, mollify a
  truncation of `u`; the mollifications `v n` converge to `u` almost everywhere and do not
  increase variation. For all levels `t` outside the countably many with `μ ({u = t} ∩ Ω) > 0`,
  the smoothed superlevel functions `ψ ((n + 1) (v n - t))`, for the smooth transition function
  `ψ`, converge to the indicator of `{u > t}` almost everywhere, so lower semicontinuity bounds
  `P({u > t}; ·)` by their variations. These are explicit integrals over `Ω × ℝ`, so Fatou's
  lemma and Tonelli's theorem integrate the bound over `t`, and a compact exhaustion of `Ω`
  passes from the local bounds to `Ω`.

For `u` locally Lipschitz on `Ω`, in particular `C¹`, the variation is `∫_Ω ‖Du‖`, so
`∫_ℝ P({u > t}; Ω) dt = ∫_Ω ‖Du‖`.

## Main declarations

* `TauCeti.integral_divergenceCLM_mul_eq_integral_integral_indicator`: the layer-cake formula for
  the pairing of `u` with `div φ`.
* `TauCeti.totalVariationOn_le_lintegral_perimeter`: the coarea inequality.
* `TauCeti.totalVariationOn_eq_lintegral_perimeter`: the coarea formula
  `|Du|(Ω) = ∫_ℝ P({u > t}; Ω) dt` for locally integrable `u`.
* `LocallyLipschitzOn.lintegral_perimeter_eq_setLIntegral_enorm_fderiv`: for locally Lipschitz
  `u`, `∫_ℝ P({u > t}; Ω) dt = ∫_Ω ‖Du‖`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.40.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.5,
  Theorem 5.9.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter TestFunction Set Metric ContinuousLinearMap
open scoped ENNReal Distributions Topology Convolution

namespace TauCeti

/-! ### The layer-cake formula and the coarea inequality -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {u : E → ℝ}

/-- **The layer-cake formula for the distributional pairing.** For `u` locally integrable on `Ω`
and a test vector field `φ` on `Ω`, the pairing of `u` with `div φ` is the integral over all
levels `t` of the pairings of the superlevel sets `{u > t}`:
`∫ u div φ = ∫_ℝ (∫_{u > t} div φ) dt`. -/
theorem integral_divergenceCLM_mul_eq_integral_integral_indicator
    (hu : LocallyIntegrableOn u Ω μ) (φ : 𝓓(Ω, E)) :
    ∫ x, divergenceCLM φ x * u x ∂μ =
      ∫ t, ∫ x, divergenceCLM φ x * {x | t < u x}.indicator 1 x ∂μ := by
  -- All pairings only see `Ω`, where `u` is a.e. measurable.
  have hrestrict (w : E → ℝ) :
      ∫ x, divergenceCLM φ x * w x ∂μ = ∫ x in Ω, divergenceCLM φ x * w x ∂μ := by
    have := setIntegral_smul_eq_integral_smul (μ := μ) (w := w) (divergenceCLM φ)
    simp only [smul_eq_mul] at this
    exact this.symm
  have hu_meas : AEMeasurable u (μ.restrict Ω) := hu.aestronglyMeasurable.aemeasurable
  have hf_int : Integrable (divergenceCLM φ) (μ.restrict Ω) :=
    ((divergenceCLM φ).integrable ((locallyIntegrable_const 1).locallyIntegrableOn _)).integrableOn
  have hf0 : ∫ x in Ω, divergenceCLM φ x ∂μ = 0 := by
    simpa using (hrestrict 1).symm.trans (by simpa using integral_divergenceCLM_eq_zero (μ := μ) φ)
  -- The integrand `div φ x * (1_{t < u x} - 1_{t < 0})` on `Ω × ℝ`; its integral in `t` is
  -- `div φ x * u x`.
  let G : E × ℝ → ℝ := fun p =>
    divergenceCLM φ p.1 * ((Iio (u p.1)).indicator 1 p.2 - (Iio 0).indicator 1 p.2)
  have hGm : AEStronglyMeasurable G ((μ.restrict Ω).prod volume) := by
    have hlt : NullMeasurableSet {p : E × ℝ | p.2 < u p.1} ((μ.restrict Ω).prod volume) :=
      nullMeasurableSet_lt measurable_snd.aemeasurable
        (hu_meas.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
    refine ((divergenceCLM φ).continuous.comp continuous_fst).aestronglyMeasurable.mul
      (((aestronglyMeasurable_const (b := (1 : ℝ))).indicator₀ hlt).sub
        (((measurable_const (a := (1 : ℝ))).indicator (measurableSet_Iio (a := (0 : ℝ)))).comp
          measurable_snd).aestronglyMeasurable)
      |>.congr (.of_forall fun p => ?_)
    simp [G, indicator_apply]
  have hG : Integrable G ((μ.restrict Ω).prod volume) := by
    rw [integrable_prod_iff hGm]
    refine ⟨.of_forall fun x =>
      (integrable_indicator_Iio_sub_indicator_Iio_zero (u x)).const_mul (divergenceCLM φ x), ?_⟩
    simp_rw [G, norm_mul, integral_const_mul]
    simpa using (integrable_smul_of_locallyIntegrableOn hu (divergenceCLM φ)).integrableOn.norm
  calc ∫ x, divergenceCLM φ x * u x ∂μ = ∫ x in Ω, ∫ t, G (x, t) ∂volume ∂μ := by
        rw [hrestrict]
        simp_rw [G, integral_const_mul, integral_indicator_Iio_sub_indicator_Iio_zero]
    _ = ∫ t, ∫ x in Ω, G (x, t) ∂μ := integral_integral_swap hG
    _ = ∫ t, ∫ x, divergenceCLM φ x * {x | t < u x}.indicator 1 x ∂μ := by
        refine integral_congr_ae (.of_forall fun t => ?_)
        have hA : Integrable (fun x => divergenceCLM φ x * {x | t < u x}.indicator 1 x)
            (μ.restrict Ω) := by
          refine hf_int.mul_bdd (c := 1) ?_ (.of_forall fun x => ?_)
          · exact aestronglyMeasurable_const.indicator₀
              (nullMeasurableSet_lt aemeasurable_const hu_meas)
          · by_cases hx : t < u x <;> simp [hx]
        simp only [G, mul_sub]
        rw [hrestrict, integral_sub, integral_mul_const, hf0]
        · simp [indicator_apply]
        · simpa [indicator_apply] using hA
        · exact hf_int.mul_const _

/-- **The coarea inequality.** For `u` locally integrable on `Ω`, against an additive Haar
measure, the total variation of `u` is at most the integral of the perimeters of its superlevel
sets: `|Du|(Ω) ≤ ∫_ℝ P({u > t}; Ω) dt`. -/
theorem totalVariationOn_le_lintegral_perimeter (hu : LocallyIntegrableOn u Ω μ) :
    totalVariationOn μ Ω u ≤ ∫⁻ t, perimeter μ Ω {x | t < u x} := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  rw [integral_divergenceCLM_mul_eq_integral_integral_indicator hu φ]
  exact TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal.trans
    (lintegral_mono fun t => (ofReal_integral_le_totalVariationOn φ hφ).trans_eq perimeter_def.symm)

/-! ### Smoothed superlevel functions -/

/-- The density in `(t, x)` of the variation of the smoothed superlevel function `ψ (c (w - t))`,
for the smooth transition function `ψ`: `c ψ'(c (w x - t)) ‖Dw x‖`. -/
private def smoothCoareaDensity (w : E → ℝ) (c t : ℝ) (x : E) : ℝ≥0∞ :=
  ENNReal.ofReal (c * deriv Real.smoothTransition (c * (w x - t))) * ‖fderiv ℝ w x‖ₑ

/-- The variation of the smoothed superlevel function `ψ (c (w - t))` of a locally Lipschitz `w`
is `∫_Ω c ψ'(c (w - t)) ‖Dw‖`. -/
private theorem totalVariationOn_smoothTransition_comp {w : E → ℝ} (hw : LocallyLipschitzOn Ω w)
    {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    totalVariationOn μ Ω (fun x => Real.smoothTransition (c * (w x - t))) =
      ∫⁻ x in Ω, smoothCoareaDensity w c t x ∂μ := by
  rw [(hw.smoothTransition_mul_sub c t).totalVariationOn_eq_setLIntegral_enorm_fderiv]
  refine setLIntegral_congr_fun_ae Ω.isOpen.measurableSet ?_
  filter_upwards [hw.ae_differentiableAt_of_mem (μ := μ) Ω.isOpen] with x hx hxΩ
  rw [smoothCoareaDensity, ((hx hxΩ).hasFDerivAt.sub_const t).const_mul c |>.smoothTransition
    |>.fderiv, smul_smul, mul_comm, enorm_smul,
    Real.enorm_of_nonneg (mul_nonneg hc Real.smoothTransition.monotone.deriv_nonneg)]

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- The density of the variation of a smoothed superlevel function is jointly measurable. -/
private theorem aemeasurable_smoothCoareaDensity {w : E → ℝ} (hw : LocallyLipschitzOn Ω w)
    (c : ℝ) :
    AEMeasurable (fun p : ℝ × E => smoothCoareaDensity w c p.1 p.2)
      (volume.prod (μ.restrict Ω)) := by
  have hw2 : AEMeasurable (fun p : ℝ × E => w p.2) (volume.prod (μ.restrict Ω)) :=
    (hw.continuousOn.aemeasurable Ω.isOpen.measurableSet).comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd
  have hψ' : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  exact (ENNReal.measurable_ofReal.comp_aemeasurable ((hψ'.measurable.comp_aemeasurable
    ((hw2.sub measurable_fst.aemeasurable).const_mul _)).const_mul _)).mul
    ((measurable_fderiv ℝ w).enorm.comp measurable_snd).aemeasurable

/-- For `c > 0` the densities `c ψ'(c (w x - t)) ‖Dw x‖` integrate over all levels `t` to
`‖Dw x‖`, so over `ℝ × Ω` to `∫_Ω ‖Dw‖`. -/
private theorem lintegral_lintegral_smoothCoareaDensity {w : E → ℝ}
    (hw : LocallyLipschitzOn Ω w) {c : ℝ} (hc : 0 < c) :
    ∫⁻ t, ∫⁻ x in Ω, smoothCoareaDensity w c t x ∂μ = ∫⁻ x in Ω, ‖fderiv ℝ w x‖ₑ ∂μ := by
  rw [lintegral_lintegral_swap (aemeasurable_smoothCoareaDensity hw c)]
  refine lintegral_congr fun x => ?_
  simp_rw [smoothCoareaDensity]
  rw [lintegral_mul_const' _ _ enorm_ne_top, Real.smoothTransition.lintegral_ofReal_mul_deriv _ hc,
    one_mul]

/-- **Lower semicontinuity along smoothed superlevel functions.** If locally Lipschitz functions
`v n` converge to a measurable `u` almost everywhere on `Ω`, then for almost every level `t` the
smoothed superlevel functions `ψ ((n + 1) (v n - t))` converge to the indicator of `{u > t}` almost
everywhere on `Ω`, so their variations bound the perimeter of `{u > t}`. The exceptional levels
are the countably many `t` with `μ ({u = t} ∩ Ω) > 0`. -/
private theorem ae_perimeter_le_liminf_lintegral_smoothCoareaDensity {v : ℕ → E → ℝ}
    (hv : ∀ n, LocallyLipschitzOn Ω (v n)) (hu : Measurable u)
    (h : ∀ᵐ x ∂μ.restrict Ω, Tendsto (fun n => v n x) atTop (𝓝 (u x))) :
    ∀ᵐ t, perimeter μ Ω {x | t < u x} ≤
      liminf (fun n : ℕ => ∫⁻ x in Ω, smoothCoareaDensity (v n) ((n : ℝ) + 1) t x ∂μ) atTop := by
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  -- Only countably many levels of `u` carry positive measure on `Ω`.
  have hlevel : ∀ᵐ t, μ.restrict Ω {x | u x = t} = 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1
      ((Measure.countable_meas_level_set_pos (μ := μ.restrict Ω) hu).measure_zero volume)]
      with t ht
    simpa using ht
  filter_upwards [hlevel] with t ht
  have hw (n : ℕ) := (hv n).smoothTransition_mul_sub ((n : ℝ) + 1) t
  have hS : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu
  rw [perimeter_def]
  refine (totalVariationOn_le_liminf
    (.of_forall fun n => (hw n).continuousOn.locallyIntegrableOn hΩm)
    (u₀ := {x | t < u x}.indicator 1)
    (((locallyIntegrable_const 1).indicator hS).locallyIntegrableOn _) fun K hK hKΩ => ?_).trans_eq
    (congrArg (liminf · atTop) <| funext fun n =>
      totalVariationOn_smoothTransition_comp (hv n) (by positivity) t)
  -- Dominated convergence on `K`: the integrands are bounded by `1` and tend to zero at every
  -- point where `v n → u` and `u ≠ t`.
  have hKm := hK.measurableSet
  have hlim := tendsto_lintegral_of_dominated_convergence' (μ := μ.restrict K) (f := 0)
    (F := fun n x => ‖Real.smoothTransition (((n : ℝ) + 1) * (v n x - t)) -
      {x | t < u x}.indicator 1 x‖ₑ) (fun _ => 1)
    (fun n => ((((hw n).continuousOn.mono hKΩ).aemeasurable hKm).sub
      (measurable_const.indicator hS).aemeasurable).enorm)
    (fun n => .of_forall fun x => ?_) (by simpa using hK.measure_lt_top.ne)
    (ae_restrict_of_ae_restrict_of_subset hKΩ
      (h.and (measure_eq_zero_iff_ae_notMem.1 ht)) |>.mono fun x hx => ?_)
  · simpa using hlim
  · have h0 := Real.smoothTransition.nonneg (((n : ℝ) + 1) * (v n x - t))
    have h1 := Real.smoothTransition.le_one (((n : ℝ) + 1) * (v n x - t))
    have hi : {x | t < u x}.indicator (1 : E → ℝ) x ∈ Icc 0 1 := by
      by_cases hxt : t < u x <;> simp [hxt]
    dsimp only
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_one]
    exact abs_sub_le_iff.2 ⟨by linarith [hi.1], by linarith [hi.2]⟩
  · obtain ⟨hx, hxt⟩ := hx
    refine tendsto_const_nhds.congr' ?_
    rcases lt_or_gt_of_ne (show u x ≠ t from hxt) with hlt | hgt
    · filter_upwards [hx.eventually (gt_mem_nhds hlt)] with n hn
      have hle : ((n : ℝ) + 1) * (v n x - t) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 hn.le)
      simp [Real.smoothTransition.zero_of_nonpos hle, not_lt.2 hlt.le]
    · have htop : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ((u x - t) / 2)) atTop atTop :=
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const
          (by linarith)
      filter_upwards [htop.eventually_ge_atTop 1,
        hx.eventually (lt_mem_nhds (show (t + u x) / 2 < u x by linarith))] with n hn hvn
      have h1 : 1 ≤ ((n : ℝ) + 1) * (v n x - t) := hn.trans (by gcongr; linarith)
      simp [Real.smoothTransition.one_of_one_le h1, hgt]

/-! ### The coarea formula -/

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The total variation on `Ω` is at most the `liminf` of the variations on open sets `U m` that
eventually contain every compact subset of `Ω`. -/
private theorem totalVariationOn_le_liminf_of_eventually_subset {w : E → ℝ} {U : ℕ → Opens E}
    (hU : ∀ K, IsCompact K → K ⊆ Ω → ∀ᶠ m in atTop, K ⊆ (U m : Set E)) :
    totalVariationOn μ Ω w ≤ liminf (fun m => totalVariationOn μ (U m) w) atTop := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hU _ φ.hasCompactSupport.isCompact φ.tsupport_subset] with m hm
  let φ' : 𝓓(U m, E) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hm⟩
  have hφ' (x : E) : divergenceCLM φ' x = divergenceCLM φ x := by simp [φ']
  simpa only [hφ'] using ofReal_integral_le_totalVariationOn (μ := μ) (u := w) φ' hφ

/-- The local half of the reverse coarea inequality: around a compact `K ⊆ Ω` there is an open set
`U` on which the perimeters of the superlevel sets of `u` are bounded almost everywhere by a
measurable function of the level whose integral is at most `|Du|(Ω)`. -/
private theorem exists_aemeasurable_ae_perimeter_le (hu : Measurable u)
    (hui : LocallyIntegrableOn u Ω μ) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ U : Opens E, K ⊆ U ∧ ∃ H : ℝ → ℝ≥0∞, AEMeasurable H ∧
      (∀ᵐ t, perimeter μ U {x | t < u x} ≤ H t) ∧ ∫⁻ t, H t ≤ totalVariationOn μ Ω u := by
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  let W : Opens E := ⟨thickening δ K, isOpen_thickening⟩
  let U : Opens E := ⟨thickening (δ / 2) K, isOpen_thickening⟩
  have hUL : (U : Set E) ⊆ cthickening δ K := thickening_subset_cthickening_of_le (by linarith) K
  have hWL : (W : Set E) ⊆ cthickening δ K := thickening_subset_cthickening_of_le le_rfl K
  -- Truncate `u` to the compact set `cthickening δ K ⊆ Ω`, and mollify with normalized bumps of
  -- outer radius `1 / (n + 1)`.
  let ũ := (cthickening δ K).indicator u
  have hũ : Integrable ũ μ :=
    (hui.integrableOn_compact_subset hKδ hK.cthickening).integrable_indicator
      isClosed_cthickening.measurableSet
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / (n + 2), 1 / (n + 1), by positivity, by gcongr; norm_num⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let v : ℕ → E → ℝ := fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] ũ
  have hv (n : ℕ) : LocallyLipschitzOn U (v n) :=
    ((φ n).hasCompactSupport_normed.contDiff_convolution_left _ ((φ n).contDiff_normed (n := 1))
      hũ.locallyIntegrable).locallyLipschitz.locallyLipschitzOn
  -- The mollifications converge to `u` almost everywhere on `U`.
  have hconv : ∀ᵐ x ∂μ.restrict U, Tendsto (fun n => v n x) atTop (𝓝 (u x)) := by
    have hratio (n : ℕ) : (φ n).rOut ≤ 2 * (φ n).rIn := by
      simp only [φ]
      field_simp
      linarith
    filter_upwards [ae_restrict_of_ae <|
      ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ (.of_forall hratio)
        hũ.locallyIntegrable, ae_restrict_mem U.isOpen.measurableSet] with x hx hxU
    rwa [show ũ x = u x from indicator_of_mem (hUL hxU) u] at hx
  -- Once its radius is below `δ / 2`, each mollification has variation on `U` at most `|Du|(Ω)`.
  have hvar : ∀ᶠ n in atTop, ∫⁻ x in U, ‖fderiv ℝ (v n) x‖ₑ ∂μ ≤ totalVariationOn μ Ω u := by
    filter_upwards [hφ.eventually (gt_mem_nhds (half_pos hδ))] with n hn
    rw [← (hv n).totalVariationOn_eq_setLIntegral_enorm_fderiv]
    refine ((φ n).totalVariationOn_normed_convolution_le (Ω := W)
      (hũ.locallyIntegrable.locallyIntegrableOn _) fun x hx y hy => ?_).trans ?_
    · obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 hx
      exact mem_thickening_iff.2 ⟨z, hz, by linarith [dist_triangle y x z, mem_closedBall.1 hy]⟩
    · rw [totalVariationOn_congr_ae (v := u) ?_]
      · exact totalVariationOn_mono fun x hx => hKδ (hWL hx)
      · filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with x hx
        exact indicator_of_mem (hWL hx) u
  refine ⟨U, self_subset_thickening (half_pos hδ) K, _,
    AEMeasurable.liminf fun n => (aemeasurable_smoothCoareaDensity (hv n) _).lintegral_prod_right',
    ae_perimeter_le_liminf_lintegral_smoothCoareaDensity hv hu hconv, ?_⟩
  -- Fatou's lemma and Tonelli's theorem.
  refine (lintegral_liminf_le' fun n =>
    (aemeasurable_smoothCoareaDensity (hv n) _).lintegral_prod_right').trans ?_
  simp_rw [lintegral_lintegral_smoothCoareaDensity (hv _) (Nat.cast_add_one_pos _)]
  exact liminf_le_of_frequently_le' hvar.frequently

/-- **The coarea formula for total variation.** For `u` locally integrable on `Ω`, against an
additive Haar measure, the total variation of `u` is the integral of the perimeters of its
superlevel sets: `|Du|(Ω) = ∫_ℝ P({u > t}; Ω) dt`, finite or infinite. -/
theorem totalVariationOn_eq_lintegral_perimeter (hu : LocallyIntegrableOn u Ω μ) :
    totalVariationOn μ Ω u = ∫⁻ t, perimeter μ Ω {x | t < u x} := by
  refine le_antisymm (totalVariationOn_le_lintegral_perimeter hu) ?_
  -- Pass to a measurable representative `hm.mk u` of `u` on `Ω`.
  have hm := hu.aestronglyMeasurable.aemeasurable
  have hu'u : u =ᵐ[μ.restrict Ω] hm.mk u := hm.ae_eq_mk
  have hlevel (t : ℝ) : perimeter μ Ω {x | t < u x} = perimeter μ Ω {x | t < hm.mk u x} :=
    perimeter_congr_ae (hu'u.mono fun x hx => by simp [hx])
  rw [totalVariationOn_congr_ae hu'u]
  simp_rw [hlevel]
  -- Local bounds around the members of a compact exhaustion of `Ω`.
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let C := CompactExhaustion.choice Ω
  have hC (m : ℕ) : IsCompact (((↑) : Ω → E) '' C m) :=
    (C.isCompact m).image continuous_subtype_val
  choose U hCU H hH hPH hHint using fun m =>
    exists_aemeasurable_ae_perimeter_le hm.measurable_mk (hu.congr hu'u) (hC m)
      (image_subset_iff.2 fun x _ => x.2)
  have hexh (K : Set E) (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∀ᶠ m in atTop, K ⊆ (U m : Set E) := by
    obtain ⟨n, hn⟩ := C.exists_superset_of_isCompact
      (Subtype.isCompact_iff.2 (by rwa [image_preimage_eq_of_subset (by simpa using hKΩ)]))
    filter_upwards [eventually_ge_atTop n] with m hm
    refine (subset_of_eq (image_preimage_eq_of_subset (by simpa using hKΩ)).symm).trans
      ((image_mono (hn.trans (C.subset hm))).trans (hCU m))
  calc ∫⁻ t, perimeter μ Ω {x | t < hm.mk u x}
      ≤ ∫⁻ t, liminf (fun m => H m t) atTop := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_all_iff.2 hPH] with t ht
        rw [perimeter_def]
        exact (totalVariationOn_le_liminf_of_eventually_subset hexh).trans
          (liminf_le_liminf (.of_forall fun m => perimeter_def.symm.trans_le (ht m)))
    _ ≤ liminf (fun m => ∫⁻ t, H m t) atTop := lintegral_liminf_le' hH
    _ ≤ totalVariationOn μ Ω (hm.mk u) := liminf_le_of_frequently_le' (.of_forall hHint)

/-! ### The coarea formula for locally Lipschitz functions -/

/-- **The coarea formula for locally Lipschitz functions.** If `u` is locally Lipschitz on `Ω`,
in particular if it is `C¹` there, then against an additive Haar measure the perimeters of its
superlevel sets integrate to the integral of the norm of its derivative:
`∫_ℝ P({u > t}; Ω) dt = ∫_Ω ‖Du‖`. -/
theorem _root_.LocallyLipschitzOn.lintegral_perimeter_eq_setLIntegral_enorm_fderiv
    (hu : LocallyLipschitzOn Ω u) :
    ∫⁻ t, perimeter μ Ω {x | t < u x} = ∫⁻ x in Ω, ‖fderiv ℝ u x‖ₑ ∂μ := by
  rw [← totalVariationOn_eq_lintegral_perimeter
      (hu.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet),
    hu.totalVariationOn_eq_setLIntegral_enorm_fderiv]

end TauCeti
