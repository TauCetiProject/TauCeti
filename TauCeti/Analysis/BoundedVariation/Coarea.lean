/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.BoundedVariation.Perimeter
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

This file proves the formula's lower half for every locally integrable function and the full
formula for locally Lipschitz functions:

* the layer-cake formula for the distributional pairing, `∫ u div φ = ∫_ℝ (∫_{u > t} div φ) dt`,
  which follows from writing `u x = ∫_ℝ (1_{t < u x} - 1_{t < 0}) dt`, Fubini's theorem and
  `∫ div φ = 0`;
* hence the coarea inequality `|Du|(Ω) ≤ ∫_ℝ P({u > t}; Ω) dt`, testing each superlevel set
  against the same vector field;
* for `u` locally Lipschitz on `Ω`, in particular `C¹`, the reverse inequality, so that
  `|Du|(Ω) = ∫_ℝ P({u > t}; Ω) dt = ∫_Ω ‖Du‖`. The indicator of `{u > t}` is the pointwise limit
  of `ψ ((n + 1) (u - t))` for the smooth transition function `ψ`; lower semicontinuity bounds
  `P({u > t}; Ω)` by the variations of these locally Lipschitz functions, and Fatou's lemma and
  Tonelli's theorem integrate the bound over `t`.

## Main declarations

* `TauCeti.integral_divergenceCLM_mul_eq_integral_integral_indicator`: the layer-cake formula for
  the pairing of `u` with `div φ`.
* `TauCeti.totalVariationOn_le_lintegral_perimeter`: the coarea inequality.
* `LocallyLipschitzOn.lintegral_perimeter_eq_setLIntegral_enorm_fderiv`: for locally Lipschitz
  `u`, `∫_ℝ P({u > t}; Ω) dt = ∫_Ω ‖Du‖`.
* `LocallyLipschitzOn.totalVariationOn_eq_lintegral_perimeter`: the coarea formula
  `|Du|(Ω) = ∫_ℝ P({u > t}; Ω) dt` for locally Lipschitz `u`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.5,
  Theorem 5.9.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter TestFunction Set
open scoped ENNReal Distributions Topology

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

/-- **The coarea formula for total variation of locally Lipschitz functions.** If `u` is locally
Lipschitz on `Ω`, then against an additive Haar measure
`|Du|(Ω) = ∫_ℝ P({u > t}; Ω) dt`. -/
theorem _root_.LocallyLipschitzOn.totalVariationOn_eq_lintegral_perimeter
    (hu : LocallyLipschitzOn Ω u) :
    totalVariationOn μ Ω u = ∫⁻ t, perimeter μ Ω {x | t < u x} := by
  rw [hu.lintegral_perimeter_eq_setLIntegral_enorm_fderiv,
    hu.totalVariationOn_eq_setLIntegral_enorm_fderiv]

end TauCeti
