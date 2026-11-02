/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.BoundedVariation.VariationMeasure
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.Calculus.Rademacher
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.MeasureTheory.Constructions.BorelSpace.Order
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.LayerCake
import TauCeti.Topology.MetricSpace.ProperSpace
import TauCeti.Topology.Sets.Opens

/-!
# The coarea formula for total variation

For a function `u` on an open set `Ω` of a finite-dimensional real inner product space, the
**coarea formula** `|Du|(Ω) = ∫_ℝ P({u > t}; Ω) dt` expresses the total variation of `u` as the
integral over all levels of the perimeters of its superlevel sets. Here `|Du|(Ω)` is the
variational supremum `TauCeti.totalVariationOn` and `P(·; Ω)` is `TauCeti.perimeter`, both
against an additive Haar measure; the level integral is an extended Lebesgue integral.

The formula holds for every function locally integrable on `Ω`
(`TauCeti.totalVariationOn_eq_lintegral_perimeter`). The proof has three steps.

* The layer-cake formula for the distributional pairing, `∫ u div φ = ∫_ℝ (∫_{u > t} div φ) dt`,
  follows from writing `u x = ∫_ℝ (1_{t < u x} - 1_{t < 0}) dt`, Fubini's theorem and
  `∫ div φ = 0`. Testing each superlevel set against the same vector field gives the coarea
  inequality `|Du|(Ω) ≤ ∫_ℝ P({u > t}; Ω) dt`.
* For `u` locally Lipschitz on `Ω`, in particular `C¹`, the reverse inequality holds and
  `∫_ℝ P({u > t}; Ω) dt = ∫_Ω ‖Du‖`. The indicator of `{u > t}` is the pointwise limit of
  `ψ ((n + 1) (u - t))` for the smooth transition function `ψ`. Lower semicontinuity bounds
  `P({u > t}; Ω)` by the variations of these locally Lipschitz functions, and Fatou's lemma and
  Tonelli's theorem integrate the bound over `t`.
* For a general locally integrable `u`, the reverse inequality is first proved on open sets `Ω'`
  with compact closure in `Ω`. There the mollifications of `u` satisfy it by the previous step and
  the convolution estimate `ContDiffBump.totalVariationOn_normed_convolution_le`. Since
  `∫_ℝ μ (({w > t} ∆ {u > t}) ∩ K) dt = ∫_K |w - u|`, along a subsequence their superlevel sets
  converge locally in measure to those of `u` at almost every level. Lower semicontinuity of the
  perimeter and Fatou's lemma then pass the inequality to `u`. An exhaustion of `Ω`, inner
  continuity of the perimeter in the open set and monotone convergence finish the proof.

Fatou's lemma and monotone convergence need the level perimeter `t ↦ P({u > t}; Ω)` to be
measurable (`TauCeti.measurable_perimeter_setOf_lt`). It is lower semicontinuous at every level
`t` with `μ ({u = t} ∩ Ω) = 0`, so at all but countably many levels.

If `u` moreover has locally finite variation on `Ω`, the formula holds at the level of measures:
the variation measure `|Du|` (`TauCeti.variationMeasure`) is the superposition
`|Du| = ∫_ℝ |D1_{u > t}| dt` of the perimeter measures of the superlevel sets, so that
`|Du|(B) = ∫_ℝ |D1_{u > t}|(B) dt` for every Borel set `B ⊆ Ω`
(`TauCeti.variationMeasure_eq_bind`). Applying the coarea formula on each set `V j` of an
exhaustion of `Ω` by relatively compact open sets shows that almost every superlevel set has
locally finite perimeter in `Ω`. The two measures then agree on open subsets of `Ω` by the coarea
formula there, and are finite on each `V j`, so they agree on all Borel sets. Since the definition
of the variation measure involves a choice depending on local finiteness, the measurability of
`t ↦ |D1_{u > t}|` is proved separately, by a π-λ argument on each `V j`.

## Main declarations

* `TauCeti.integral_divergenceCLM_mul_eq_integral_integral_indicator`: the layer-cake formula for
  the pairing of `u` with `div φ`, in any finite-dimensional real normed space.
* `TauCeti.totalVariationOn_le_lintegral_perimeter`: the coarea inequality.
* `LocallyLipschitzOn.lintegral_perimeter_eq_setLIntegral_enorm_fderiv`: for locally Lipschitz
  `u`, `∫_ℝ P({u > t}; Ω) dt = ∫_Ω ‖Du‖`.
* `TauCeti.measurable_perimeter_setOf_lt`: the perimeter of `{u > t}` is measurable in `t`.
* `TauCeti.totalVariationOn_eq_lintegral_perimeter`: the coarea formula
  `|Du|(Ω) = ∫_ℝ P({u > t}; Ω) dt` for locally integrable `u`.
* `TauCeti.ae_perimeter_setOf_lt_lt_top`: if `|Du|(Ω) < ∞`, then `{u > t}` has finite perimeter
  in `Ω` for almost every `t`.
* `TauCeti.ae_exists_perimeter_setOf_lt_ne_top`: if `u` has locally finite variation on `Ω`, then
  `{u > t}` has locally finite perimeter in `Ω` for almost every `t`.
* `TauCeti.measurable_variationMeasure_indicator_setOf_lt`: the perimeter measure
  `|D1_{u > t}|` on `Ω` is measurable in `t`.
* `TauCeti.variationMeasure_eq_bind`, `TauCeti.variationMeasure_apply_eq_lintegral` and
  `TauCeti.lintegral_variationMeasure_eq_lintegral_lintegral`: the coarea formula
  `|Du| = ∫_ℝ |D1_{u > t}| dt` for the variation measure, on Borel sets and for integrals.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.5,
  Theorem 5.9.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter TestFunction Set Metric
open scoped ENNReal Distributions Topology Convolution symmDiff

namespace TauCeti

/-! ### The layer-cake formula and the coarea inequality -/

variable {E : Type*} [NormedAddCommGroup E]

section NormedSpace

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {u : E → ℝ}

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

end NormedSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {u : E → ℝ}

/-- **The coarea inequality.** For `u` locally integrable on `Ω`, against an additive Haar
measure, the total variation of `u` is at most the integral of the perimeters of its superlevel
sets: `|Du|(Ω) ≤ ∫_ℝ P({u > t}; Ω) dt`. -/
theorem totalVariationOn_le_lintegral_perimeter (hu : LocallyIntegrableOn u Ω μ) :
    totalVariationOn μ Ω u ≤ ∫⁻ t, perimeter μ Ω {x | t < u x} := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  rw [integral_divergenceCLM_mul_eq_integral_integral_indicator hu φ]
  exact TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal.trans
    (lintegral_mono fun t => (ofReal_integral_le_totalVariationOn φ hφ).trans_eq perimeter_def.symm)

/-! ### The coarea formula for locally Lipschitz functions -/

/-- The variation of the smoothed superlevel function `ψ (c (u - t))` of a locally Lipschitz `u`
is `∫_Ω c ψ'(c (u - t)) ‖Du‖`. -/
private theorem totalVariationOn_smoothTransition_comp (hu : LocallyLipschitzOn Ω u) {c : ℝ}
    (hc : 0 ≤ c) (t : ℝ) :
    totalVariationOn μ Ω (fun x => Real.smoothTransition (c * (u x - t))) =
      ∫⁻ x in Ω, ENNReal.ofReal (c * deriv Real.smoothTransition (c * (u x - t))) *
        ‖fderiv ℝ u x‖ₑ ∂μ := by
  rw [(hu.smoothTransition_mul_sub c t).totalVariationOn_eq_setLIntegral_enorm_fderiv]
  refine setLIntegral_congr_fun_ae Ω.isOpen.measurableSet ?_
  filter_upwards [hu.ae_differentiableAt_of_mem (μ := μ) Ω.isOpen] with x hx hxΩ
  rw [((hx hxΩ).hasFDerivAt.sub_const t).const_mul c |>.smoothTransition |>.fderiv, smul_smul,
    mul_comm, enorm_smul,
    Real.enorm_of_nonneg (mul_nonneg hc Real.smoothTransition.monotone.deriv_nonneg)]

/-- The indicator of `{u > t}` is the pointwise limit of the smoothed superlevel functions
`ψ ((n + 1) (u - t))`, so by lower semicontinuity their variations bound the perimeter of
`{u > t}`. -/
private theorem perimeter_le_liminf_totalVariationOn_smoothTransition_comp
    (hu : LocallyLipschitzOn Ω u) (t : ℝ) :
    perimeter μ Ω {x | t < u x} ≤ liminf (fun n : ℕ => totalVariationOn μ Ω
      fun x => Real.smoothTransition (((n : ℝ) + 1) * (u x - t))) atTop := by
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  have hv (n : ℕ) := hu.smoothTransition_mul_sub ((n : ℝ) + 1) t
  have hS : IsOpen ((Ω : Set E) ∩ u ⁻¹' Ioi t) :=
    hu.continuousOn.isOpen_inter_preimage Ω.isOpen isOpen_Ioi
  have hind : EqOn (((Ω : Set E) ∩ u ⁻¹' Ioi t).indicator 1)
      ({x | t < u x}.indicator (1 : E → ℝ)) Ω :=
    fun x hx => by by_cases hxt : t < u x <;> simp [hx, hxt]
  rw [perimeter_def]
  refine totalVariationOn_le_liminf
    (.of_forall fun n => (hv n).continuousOn.locallyIntegrableOn hΩm)
    ((((locallyIntegrable_const 1).indicator hS.measurableSet).locallyIntegrableOn _).congr
      ((ae_restrict_mem hΩm).mono fun x hx => hind hx)) fun K hK hKΩ => ?_
  -- Dominated convergence on `K`: the integrands are bounded by `1` and vanish eventually.
  have hKm := hK.measurableSet
  have hind_meas : AEMeasurable ({x | t < u x}.indicator (1 : E → ℝ)) (μ.restrict K) :=
    (measurable_const.indicator hS.measurableSet).aemeasurable.congr
      ((ae_restrict_mem hKm).mono fun x hx => hind (hKΩ hx))
  have hlim := tendsto_lintegral_of_dominated_convergence' (μ := μ.restrict K) (f := 0)
    (F := fun n x => ‖Real.smoothTransition (((n : ℝ) + 1) * (u x - t)) -
      {x | t < u x}.indicator 1 x‖ₑ) (fun _ => 1)
    (fun n => ((((hv n).continuousOn.mono hKΩ).aemeasurable hKm).sub hind_meas).enorm)
    (fun n => .of_forall fun x => ?_) (by simpa using hK.measure_lt_top.ne)
    (.of_forall fun x => ?_)
  · simpa using hlim
  · have h0 := Real.smoothTransition.nonneg (((n : ℝ) + 1) * (u x - t))
    have h1 := Real.smoothTransition.le_one (((n : ℝ) + 1) * (u x - t))
    have hi : {x | t < u x}.indicator (1 : E → ℝ) x ∈ Icc 0 1 := by
      by_cases hxt : t < u x <;> simp [hxt]
    dsimp only
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_one]
    exact abs_sub_le_iff.2 ⟨by linarith [hi.1], by linarith [hi.2]⟩
  · refine tendsto_const_nhds.congr' ?_
    by_cases hxt : t < u x
    · have htop : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (u x - t)) atTop atTop :=
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const
          (sub_pos.2 hxt)
      filter_upwards [htop.eventually_ge_atTop 1] with n hn
      simp [Real.smoothTransition.one_of_one_le hn, hxt]
    · refine .of_forall fun n => ?_
      have hle : ((n : ℝ) + 1) * (u x - t) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 (not_lt.1 hxt))
      simp [Real.smoothTransition.zero_of_nonpos hle, hxt]

/-- **The coarea formula for locally Lipschitz functions.** If `u` is locally Lipschitz on `Ω`,
in particular if it is `C¹` there, then against an additive Haar measure the perimeters of its
superlevel sets integrate to the integral of the norm of its derivative:
`∫_ℝ P({u > t}; Ω) dt = ∫_Ω ‖Du‖`. -/
theorem _root_.LocallyLipschitzOn.lintegral_perimeter_eq_setLIntegral_enorm_fderiv
    (hu : LocallyLipschitzOn Ω u) :
    ∫⁻ t, perimeter μ Ω {x | t < u x} = ∫⁻ x in Ω, ‖fderiv ℝ u x‖ₑ ∂μ := by
  have hΩm : MeasurableSet (Ω : Set E) := Ω.isOpen.measurableSet
  refine le_antisymm ?_ ?_
  swap
  · rw [← hu.totalVariationOn_eq_setLIntegral_enorm_fderiv]
    exact totalVariationOn_le_lintegral_perimeter (hu.continuousOn.locallyIntegrableOn hΩm)
  -- `F n t x` is the density of the variation of the smoothed superlevel function
  -- `ψ ((n + 1) (u - t))`; for each `n` it integrates over `Ω × ℝ` to `∫_Ω ‖Du‖`.
  let F : ℕ → ℝ → E → ℝ≥0∞ := fun n t x =>
    ENNReal.ofReal (((n : ℝ) + 1) * deriv Real.smoothTransition (((n : ℝ) + 1) * (u x - t))) *
      ‖fderiv ℝ u x‖ₑ
  have hF (n : ℕ) : AEMeasurable (Function.uncurry (F n)) (volume.prod (μ.restrict Ω)) := by
    have hu2 : AEMeasurable (fun p : ℝ × E => u p.2) (volume.prod (μ.restrict Ω)) :=
      (hu.continuousOn.aemeasurable hΩm).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd
    have hψ' : Continuous (deriv Real.smoothTransition) :=
      (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
    exact (ENNReal.measurable_ofReal.comp_aemeasurable ((hψ'.measurable.comp_aemeasurable
      ((hu2.sub measurable_fst.aemeasurable).const_mul _)).const_mul _)).mul
      ((measurable_fderiv ℝ u).enorm.comp measurable_snd).aemeasurable
  have hint (n : ℕ) : ∫⁻ t, ∫⁻ x in Ω, F n t x ∂μ = ∫⁻ x in Ω, ‖fderiv ℝ u x‖ₑ ∂μ := by
    rw [lintegral_lintegral_swap (hF n)]
    refine lintegral_congr fun x => ?_
    rw [lintegral_mul_const' _ _ enorm_ne_top,
      Real.smoothTransition.lintegral_ofReal_mul_deriv _ (by positivity), one_mul]
  -- Lower semicontinuity, then Fatou's lemma and Tonelli's theorem.
  calc ∫⁻ t, perimeter μ Ω {x | t < u x}
      ≤ ∫⁻ t, liminf (fun n => ∫⁻ x in Ω, F n t x ∂μ) atTop := lintegral_mono fun t =>
        (perimeter_le_liminf_totalVariationOn_smoothTransition_comp hu t).trans_eq <|
          congrArg (liminf · atTop) <| funext fun n =>
            totalVariationOn_smoothTransition_comp hu (by positivity) t
    _ ≤ liminf (fun n => ∫⁻ t, ∫⁻ x in Ω, F n t x ∂μ) atTop :=
        lintegral_liminf_le' fun n => (hF n).lintegral_prod_right'
    _ = ∫⁻ x in Ω, ‖fderiv ℝ u x‖ₑ ∂μ := by simp_rw [hint, liminf_const]

/-! ### Measurability in the level -/

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The perimeters of the superlevel sets only see `u` almost everywhere on `Ω`. -/
private theorem perimeter_setOf_lt_congr_ae {v : E → ℝ} (h : u =ᵐ[μ.restrict Ω] v) (t : ℝ) :
    perimeter μ Ω {x | t < u x} = perimeter μ Ω {x | t < v x} := by
  refine perimeter_congr_ae ?_
  filter_upwards [h] with x hx
  simp only [hx]

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- For a measurable `u`, the perimeter of `{u > t}` in `Ω` is lower semicontinuous in `t` at every
level `t` whose level set `{u = t}` is null in `Ω`. -/
private theorem lowerSemicontinuousAt_perimeter_setOf_lt [OpensMeasurableSpace E]
    [IsLocallyFiniteMeasure μ] (hu : Measurable u) {t : ℝ}
    (ht : μ.restrict Ω {x | u x = t} = 0) :
    LowerSemicontinuousAt (fun s => perimeter μ Ω {x | s < u x}) t := by
  intro y hy
  refine eventually_lt_of_lt_liminf (hy.trans_le (perimeter_le_liminf
    (.of_forall fun s => (measurableSet_lt measurable_const hu).nullMeasurableSet)
    (measurableSet_lt measurable_const hu).nullMeasurableSet fun K hK hKΩ => ?_))
  -- Between the levels `s` and `t` the values of `u` lie within `|s - t|` of `t`. On `K` these
  -- points have measure tending to `μ (K ∩ {u = t}) = 0` as `s → t`.
  have : Fact (μ K < ∞) := ⟨hK.measure_lt_top⟩
  have hlim := (tendsto_measure_cthickening_of_isCompact (μ := (μ.restrict K).map u)
    (isCompact_singleton (x := t))).comp ((continuous_sub_right t).abs.tendsto' t 0 (by simp))
  have ht0 : (μ.restrict K).map u {t} = 0 := by
    rw [Measure.map_apply hu (measurableSet_singleton t)]
    exact le_antisymm ((Measure.restrict_mono hKΩ le_rfl _).trans_eq ht) zero_le
  rw [ht0] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun s => ?_
  rw [Function.comp_apply, cthickening_singleton _ (abs_nonneg _),
    Measure.map_apply hu measurableSet_closedBall, Measure.restrict_apply' hK.measurableSet]
  refine measure_mono (inter_subset_inter_left _ fun x hx => ?_)
  rw [mem_preimage, mem_closedBall, Real.dist_eq]
  rw [mem_symmDiff] at hx
  have h₁ := le_abs_self (s - t)
  have h₂ := neg_abs_le (s - t)
  rcases hx with ⟨hx₁, hx₂⟩ | ⟨hx₁, hx₂⟩ <;> simp only [mem_ofPred_eq, not_lt] at hx₁ hx₂ <;>
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- **Measurability in the level.** For `u` almost everywhere measurable on `Ω`, the perimeter of
the superlevel set `{u > t}` in `Ω` is a measurable function of the level `t`. -/
theorem measurable_perimeter_setOf_lt [OpensMeasurableSpace E] [IsLocallyFiniteMeasure μ]
    (hu : AEMeasurable u (μ.restrict Ω)) : Measurable fun t => perimeter μ Ω {x | t < u x} := by
  simp_rw [perimeter_setOf_lt_congr_ae hu.ae_eq_mk]
  -- Lower semicontinuity can only fail at the countably many levels of positive measure.
  refine measurable_of_countable_not_lowerSemicontinuousAt
    ((Measure.countable_meas_level_set_pos (μ := μ.restrict Ω) hu.measurable_mk).mono
      fun t ht => ?_)
  by_contra h
  exact ht (lowerSemicontinuousAt_perimeter_setOf_lt hu.measurable_mk
    (nonpos_iff_eq_zero.1 (not_lt.1 h)))

/-! ### The coarea formula for locally integrable functions -/

/-- The reverse coarea inequality `∫_ℝ P({u > t}; Ω') dt ≤ |Du|(Ω)` for a measurable `u` locally
integrable on `Ω` and an open `Ω'` whose closure is a compact subset of `Ω`. -/
private theorem lintegral_perimeter_le_of_isCompact_closure (hum : Measurable u)
    (hu : LocallyIntegrableOn u Ω μ) {Ω' : Opens E} (hc : IsCompact (closure (Ω' : Set E)))
    (hsub : closure (Ω' : Set E) ⊆ Ω) :
    ∫⁻ t, perimeter μ Ω' {x | t < u x} ≤ totalVariationOn μ Ω u := by
  -- The mollifications `w n` of `u` satisfy the inequality by the locally Lipschitz case and the
  -- convolution estimate. Along a subsequence their superlevel sets converge locally in measure to
  -- those of `u` at almost every level, so lower semicontinuity of the perimeter and Fatou's lemma
  -- pass the inequality to `u`.
  obtain ⟨w, hw, hconv, hvar⟩ := exists_mollifier_seq_of_isCompact_closure hu hc hsub
  -- Along a subsequence, the superlevel sets converge in measure on `closure Ω'` at almost
  -- every level. The variation bound holds eventually along this subsequence as well.
  obtain ⟨ns, hns, hae⟩ :=
    (μ.restrict (closure (Ω' : Set E))).exists_strictMono_ae_tendsto_measure_symmDiff_setOf_lt
      (fun n => (hw n).continuous.aemeasurable) hum.aemeasurable
      (hconv _ hc Subset.rfl)
  have hsmall := hns.tendsto_atTop.eventually hvar
  -- At such levels, lower semicontinuity bounds `P({u > t}; Ω')`.
  have hlsc : ∀ᵐ t, perimeter μ Ω' {x | t < u x} ≤
      liminf (fun j => perimeter μ Ω' {x | t < w (ns j) x}) atTop := by
    filter_upwards [hae] with t ht
    refine perimeter_le_liminf (.of_forall fun j =>
      (measurableSet_lt measurable_const (hw (ns j)).continuous.measurable).nullMeasurableSet)
      (measurableSet_lt measurable_const hum).nullMeasurableSet fun K' _ hK' => ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
      fun j => ?_
    rw [Measure.restrict_apply' isClosed_closure.measurableSet]
    exact measure_mono (inter_subset_inter_right _ (hK'.trans subset_closure))
  calc ∫⁻ t, perimeter μ Ω' {x | t < u x}
      ≤ ∫⁻ t, liminf (fun j => perimeter μ Ω' {x | t < w (ns j) x}) atTop :=
        lintegral_mono_ae hlsc
    _ ≤ liminf (fun j => ∫⁻ t, perimeter μ Ω' {x | t < w (ns j) x}) atTop :=
        lintegral_liminf_le' fun j =>
          (measurable_perimeter_setOf_lt (hw (ns j)).continuous.aemeasurable).aemeasurable
    _ ≤ totalVariationOn μ Ω u :=
        (liminf_le_liminf (hsmall.mono fun j hj => by
          have hL := (hw (ns j)).locallyLipschitz.locallyLipschitzOn (s := Ω')
          rwa [hL.lintegral_perimeter_eq_setLIntegral_enorm_fderiv,
            ← hL.totalVariationOn_eq_setLIntegral_enorm_fderiv])).trans_eq (liminf_const _)

/-- **The coarea formula for total variation.** For `u` locally integrable on `Ω`, against an
additive Haar measure, the total variation of `u` is the integral of the perimeters of its
superlevel sets: `|Du|(Ω) = ∫_ℝ P({u > t}; Ω) dt`, finite or infinite. -/
theorem totalVariationOn_eq_lintegral_perimeter (hu : LocallyIntegrableOn u Ω μ) :
    totalVariationOn μ Ω u = ∫⁻ t, perimeter μ Ω {x | t < u x} := by
  refine le_antisymm (totalVariationOn_le_lintegral_perimeter hu) ?_
  -- Pass to a measurable representative `v` of `u` on `Ω`.
  have hum : AEMeasurable u (μ.restrict Ω) := hu.aestronglyMeasurable.aemeasurable
  set v := hum.mk u
  simp_rw [perimeter_setOf_lt_congr_ae hum.ae_eq_mk, totalVariationOn_congr_ae hum.ae_eq_mk]
  have hv : LocallyIntegrableOn v Ω μ := hu.congr hum.ae_eq_mk
  -- Exhaust `Ω` by open sets `Ω' j` with compact closures in `Ω`; by inner continuity and monotone
  -- convergence the level integral on `Ω` is the supremum of those on `Ω' j`.
  obtain ⟨Ω', hVc, hVΩ, hmono, hVU, -⟩ := Ω.exists_monotone_isCompact_closure_iUnion_eq
  have hΩ' : (⨆ j, Ω' j) = Ω := Opens.ext (by simpa using hVU)
  calc ∫⁻ t, perimeter μ Ω {x | t < v x}
      = ∫⁻ t, ⨆ j, perimeter μ (Ω' j) {x | t < v x} := by
        simp_rw [← perimeter_iSup hmono.directed_le, hΩ']
    _ = ⨆ j, ∫⁻ t, perimeter μ (Ω' j) {x | t < v x} :=
        lintegral_iSup (fun j => measurable_perimeter_setOf_lt hum.measurable_mk.aemeasurable)
          fun i j hij t => perimeter_mono (hmono hij)
    _ ≤ totalVariationOn μ Ω v :=
        iSup_le fun j => lintegral_perimeter_le_of_isCompact_closure hum.measurable_mk hv (hVc j)
          (hVΩ j)

/-- If `u` has finite total variation on `Ω`, then its superlevel sets `{u > t}` have finite
perimeter in `Ω` for almost every level `t`. -/
theorem ae_perimeter_setOf_lt_lt_top (hu : LocallyIntegrableOn u Ω μ)
    (h : totalVariationOn μ Ω u ≠ ∞) : ∀ᵐ t, perimeter μ Ω {x | t < u x} < ∞ :=
  ae_lt_top (measurable_perimeter_setOf_lt hu.aestronglyMeasurable.aemeasurable)
    (by rwa [← totalVariationOn_eq_lintegral_perimeter hu])

/-! ### The coarea formula for the variation measure -/

section VariationMeasure

omit [μ.IsAddHaarMeasure] in
/-- The perimeter measure `|D1_s|` of a null-measurable set `s` with locally finite perimeter in
`Ω` gives every open `U ⊆ Ω` the perimeter `P(s; U)`. -/
theorem variationMeasure_indicator_preimage_coe [IsLocallyFiniteMeasure μ] {s : Set E}
    (hs : NullMeasurableSet s (μ.restrict Ω))
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → ∃ U : Opens E, K ⊆ (U : Set E) ∧ perimeter μ U s ≠ ∞)
    {U : Opens E} (hU : U ≤ Ω) :
    variationMeasure μ Ω (s.indicator 1) ((↑) ⁻¹' (U : Set E)) = perimeter μ U s := by
  simp_rw [perimeter_def] at hfin ⊢
  exact variationMeasure_preimage_coe (locallyIntegrableOn_indicator_const hs 1) hfin hU

omit [μ.IsAddHaarMeasure] in
/-- **Measurability in the level of the perimeter measures.** For `u` almost everywhere measurable
on `Ω`, the variation measure `|D1_{u > t}|` of the indicator of the superlevel set `{u > t}` is a
measurable function of the level `t`. -/
theorem measurable_variationMeasure_indicator_setOf_lt [IsLocallyFiniteMeasure μ]
    (hu : AEMeasurable u (μ.restrict Ω)) :
    Measurable fun t => variationMeasure μ Ω ({x | t < u x}.indicator 1) := by
  obtain ⟨V, hVc, hVΩ, hVmono, hVU, hcover⟩ := Ω.exists_monotone_isCompact_closure_iUnion_eq
  have hlf (s : Set E) := forall_isCompact_exists_totalVariationOn_ne_top_iff (μ := μ)
    (w := s.indicator 1) hVc hVΩ hVmono hVU
  simp_rw [← perimeter_def] at hlf
  have hVsub (j : ℕ) : V j ≤ Ω := subset_closure.trans (hVΩ j)
  have hum {U : Opens E} (hU : U ≤ Ω) : AEMeasurable u (μ.restrict U) :=
    hu.mono_measure (Measure.restrict_mono hU le_rfl)
  -- The levels at which `{u > t}` has locally finite perimeter in `Ω` form a measurable set `G`.
  let G := ⋂ j, {t | perimeter μ (V j) {x | t < u x} ≠ ∞}
  have hG : MeasurableSet G :=
    .iInter fun j => measurable_perimeter_setOf_lt (hum (hVsub j)) (measurableSet_singleton ∞).compl
  -- On an open `U ⊆ Ω`, the variation measure is the perimeter in `U` at levels in `G`, and `0`
  -- at the other levels, where its defining local finiteness fails.
  have hopen {U : Opens E} (hU : U ≤ Ω) : Measurable fun t =>
      variationMeasure μ Ω ({x | t < u x}.indicator 1) ((↑) ⁻¹' (U : Set E)) := by
    convert (measurable_perimeter_setOf_lt (hum hU)).indicator hG using 1
    funext t
    by_cases ht : t ∈ G
    · rw [indicator_of_mem ht, variationMeasure_indicator_preimage_coe
        (nullMeasurableSet_lt aemeasurable_const hu) ((hlf _).2 (by simpa [G] using ht)) hU]
    · rw [indicator_of_notMem ht, variationMeasure_eq_zero_of_not fun h => ht ?_,
        Measure.coe_zero, Pi.zero_apply]
      simpa [G] using (hlf _).1 (by simpa only [perimeter_def] using h.2)
  -- Each open subset of `Ω` is the trace of an open subset of `E` contained in `Ω`.
  have hopen' {W : Set Ω} (hW : IsOpen W) :
      Measurable fun t => variationMeasure μ Ω ({x | t < u x}.indicator 1) W := by
    obtain ⟨U, hU, rfl⟩ := Ω.exists_le_preimage_coe_eq hW
    exact hopen hU
  -- The traces of `V j` have finite measure, so the restrictions to them are measurable in `t`.
  have hrestrict (j : ℕ) : Measurable fun t =>
      (variationMeasure μ Ω ({x | t < u x}.indicator 1)).restrict ((↑) ⁻¹' (V j : Set E)) := by
    have hK : IsCompact (((↑) : Ω → E) ⁻¹' closure (V j : Set E)) := by
      rw [Subtype.isCompact_iff, image_preimage_eq_of_subset (by simpa using hVΩ j)]
      exact hVc j
    have (t : ℝ) : IsFiniteMeasure ((variationMeasure μ Ω ({x | t < u x}.indicator 1)).restrict
        ((↑) ⁻¹' (V j : Set E))) :=
      isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top hK.measure_lt_top.ne
        (measure_mono (preimage_mono subset_closure)))
    refine .measure_of_isPiSystem BorelSpace.measurable_eq isPiSystem_isOpen
      (fun W (hW : IsOpen W) => ?_) ?_
    · simp_rw [Measure.restrict_apply hW.measurableSet]
      exact hopen' (hW.inter ((V j).isOpen.preimage continuous_subtype_val))
    · simp_rw [Measure.restrict_apply_univ]
      exact hopen' ((V j).isOpen.preimage continuous_subtype_val)
  -- A measure on `Ω` is the supremum of its restrictions to the traces of `V j`.
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  convert Measurable.iSup fun j => (Measure.measurable_coe hs).comp (hrestrict j) using 1
  funext t
  simp_rw [Function.comp_apply]
  rw [← Measure.restrict_iUnion_apply_eq_iSup ?_ hs, hcover, Measure.restrict_univ]
  exact fun i j => ⟨max i j, preimage_mono (hVmono (le_max_left i j)),
    preimage_mono (hVmono (le_max_right i j))⟩

/-- If `u` has locally finite variation on `Ω`, then for almost every level `t` the superlevel set
`{u > t}` has locally finite perimeter in `Ω`: every compact `K ⊆ Ω` has an open neighbourhood `U`
with `P({u > t}; U) < ∞`. -/
theorem ae_exists_perimeter_setOf_lt_ne_top (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞) :
    ∀ᵐ t, ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ perimeter μ U {x | t < u x} ≠ ∞ := by
  obtain ⟨V, hVc, hVΩ, hVmono, hVU, -⟩ := Ω.exists_monotone_isCompact_closure_iUnion_eq
  have hlf (w : E → ℝ) :=
    forall_isCompact_exists_totalVariationOn_ne_top_iff (μ := μ) (w := w) hVc hVΩ hVmono hVU
  have hV := (hlf u).1 hfin
  filter_upwards [ae_all_iff.2 fun j => ae_perimeter_setOf_lt_lt_top
    (hu.mono_set (subset_closure.trans (hVΩ j))) (hV j)] with t ht
  simp_rw [perimeter_def] at ht ⊢
  exact (hlf _).2 fun j => (ht j).ne

/-- **The coarea formula for the variation measure.** If `u` is locally integrable on `Ω` with
locally finite variation there, its variation measure is the superposition of the perimeter
measures of its superlevel sets: `|Du| = ∫_ℝ |D1_{u > t}| dt` as measures on `Ω`. -/
theorem variationMeasure_eq_bind (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞) :
    variationMeasure μ Ω u =
      volume.bind fun t => variationMeasure μ Ω ({x | t < u x}.indicator 1) := by
  have hum : AEMeasurable u (μ.restrict Ω) := hu.aestronglyMeasurable.aemeasurable
  obtain ⟨V, hVc, hVΩ, hVmono, hVU, hcover⟩ := Ω.exists_monotone_isCompact_closure_iUnion_eq
  have hlf (w : E → ℝ) :=
    forall_isCompact_exists_totalVariationOn_ne_top_iff (μ := μ) (w := w) hVc hVΩ hVmono hVU
  have hVsub (j : ℕ) : V j ≤ Ω := subset_closure.trans (hVΩ j)
  -- Both measures are finite on the traces of `V j`, which cover `Ω`, so it suffices to compare
  -- them on open sets, where this is the coarea formula on each open subset of `Ω`.
  refine Measure.ext_of_generateFrom_of_iUnion {W | IsOpen W} (fun j => (↑) ⁻¹' (V j : Set E))
    BorelSpace.measurable_eq isPiSystem_isOpen ?_
    (fun j => (V j).isOpen.preimage continuous_subtype_val) (fun j => ?_) fun W hW => ?_
  · exact hcover
  · rw [variationMeasure_preimage_coe hu hfin (hVsub j)]
    exact (hlf u).1 hfin j
  · obtain ⟨U, hU, rfl⟩ := Ω.exists_le_preimage_coe_eq hW
    rw [variationMeasure_preimage_coe hu hfin hU,
      totalVariationOn_eq_lintegral_perimeter (hu.mono_set hU),
      Measure.bind_apply hW.measurableSet
        (measurable_variationMeasure_indicator_setOf_lt hum).aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_exists_perimeter_setOf_lt_ne_top hu hfin] with t ht
    exact (variationMeasure_indicator_preimage_coe
      (nullMeasurableSet_lt aemeasurable_const hum) ht hU).symm

/-- **The coarea formula on Borel sets.** If `u` is locally integrable on `Ω` with locally finite
variation there, then `|Du|(B) = ∫_ℝ |D1_{u > t}|(B) dt` for every measurable `B ⊆ Ω`. -/
theorem variationMeasure_apply_eq_lintegral (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    {s : Set Ω} (hs : MeasurableSet s) :
    variationMeasure μ Ω u s = ∫⁻ t, variationMeasure μ Ω ({x | t < u x}.indicator 1) s := by
  rw [variationMeasure_eq_bind hu hfin, Measure.bind_apply hs
    (measurable_variationMeasure_indicator_setOf_lt
      hu.aestronglyMeasurable.aemeasurable).aemeasurable]

/-- **The coarea formula for integrals against the variation measure.** If `u` is locally integrable
on `Ω` with locally finite variation there, then `∫ f d|Du| = ∫_ℝ ∫ f d|D1_{u > t}| dt` for every
nonnegative `f` almost everywhere measurable for `|Du|`. -/
theorem lintegral_variationMeasure_eq_lintegral_lintegral (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f (variationMeasure μ Ω u)) :
    ∫⁻ x, f x ∂variationMeasure μ Ω u =
      ∫⁻ t, ∫⁻ x, f x ∂variationMeasure μ Ω ({x | t < u x}.indicator 1) := by
  rw [variationMeasure_eq_bind hu hfin] at hf ⊢
  exact Measure.lintegral_bind (measurable_variationMeasure_indicator_setOf_lt
    hu.aestronglyMeasurable.aemeasurable).aemeasurable hf

end VariationMeasure

end TauCeti
