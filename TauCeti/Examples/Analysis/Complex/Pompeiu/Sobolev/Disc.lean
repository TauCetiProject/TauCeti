/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Sobolev.Comparison
public import TauCeti.Analysis.Complex.Pompeiu.Disc.Lp
public import Mathlib.Tactic.NormNum

/-!
# Disc indicators, product norms and degenerate Cauchy graphs

The unit-disc indicator has a Cauchy integral equal to `conj w` inside the disc and `w⁻¹`
outside. Its bounded-disc Sobolev graph is defined at every finite `1 < p < ∞`, whereas
its Cauchy integral is not globally `Lᵖ` when `p ≤ 2`. Its Beurling field has zero interior
and the negative reciprocal-square tail. The examples instantiate the constructed operators
at `p = 4/3, 2, 3` and separate a.e. graph representatives from pointwise integral formulas.

The product target retains its sup norm and two nonzero complex coefficients through a constant
frame change and continuous parameter families. Empty coefficient indices and zero input/output
radii give zero graph elements; real scalar projection recovers the real weak gradient.
-/

public noncomputable section

open TauCeti.Wirtinger
open MeasureTheory Complex ComplexConjugate Metric Set TopologicalSpace Function
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti.CauchyTransform.Examples

open TauCeti.CauchyTransform

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The unit-disc indicator with a specified coefficient. -/
def discDatum {F : Type*} [Zero F] (v : F) : ℂ → F :=
  (ball (0 : ℂ) 1).indicator fun _ ↦ v

/-- The indicator fixture has its stated pointwise values. -/
@[simp]
theorem discDatum_apply {F : Type*} [Zero F] (v : F) (z : ℂ) :
    discDatum v z = (ball (0 : ℂ) 1).indicator (fun _ ↦ v) z := by
  rw [discDatum]

/-- Disc indicator data belong to every finite-exponent input class. -/
theorem discDatum_memLp {F : Type*} [NormedAddCommGroup F] (v : F) (p : ℝ≥0∞) :
    MemLp (discDatum v) p (volume : Measure ℂ) :=
  memLp_indicator_const p measurableSet_ball.nullMeasurableSet v
    (Or.inr measure_ball_lt_top.ne)

/-- The datum is genuinely supported in the specified input disc. -/
theorem discDatum_support {F : Type*} [Zero F] (v : F) :
    support (discDatum v) ⊆ closedBall (0 : ℂ) 1 :=
  support_indicator_subset.trans ball_subset_closedBall

/-- The scalar datum is nonzero at the centre. -/
theorem discDatum_one_zero : discDatum (1 : ℂ) 0 = 1 := by
  simp [discDatum]

/-- The scalar Cauchy integral is the piecewise reciprocal-tail function. -/
theorem discDatum_one_transform (w : ℂ) :
    cauchyTransform (discDatum (1 : ℂ)) w =
      if ‖w‖ ≤ 1 then conj w else w⁻¹ := by
  simpa [cauchyTransform_apply, discDatum, smul_eq_mul] using
    (pi_inv_mul_integral_sub_inv_mul_indicator_ball (r := 1) zero_le_one (0 : ℂ) w)

/-- The graph value agrees a.e. on the output disc with the indicator Cauchy formula. -/
theorem indicator_value (hp : 1 < p) (hp_top : p ≠ ∞) :
    WeakDerivStep.prev _
      (graphL hp hp_top 0 1 2 (((discDatum_memLp (1 : ℂ) p).restrict
        (closedBall (0 : ℂ) ((1 : ℝ≥0) : ℝ))).toLp (discDatum (1 : ℂ))))
      =ᵐ[volume.restrict (disc 0 2 : Set ℂ)]
        fun w ↦ if ‖w‖ ≤ 1 then conj w else w⁻¹ := by
  exact (graphL_toLp_prev_ae hp hp_top (discDatum_memLp (1 : ℂ) p)
    (discDatum_support _) 2).trans (.of_forall discDatum_one_transform)

/-- The global Beurling output has zero interior and the negative reciprocal-square tail. -/
theorem indicator_beurling (hp : 1 < p) (hp_top : p ≠ ∞) :
    beurlingL hp hp_top ((discDatum_memLp (1 : ℂ) p).toLp (discDatum (1 : ℂ))) =ᵐ[volume]
      (closedBall (0 : ℂ) 1)ᶜ.indicator fun w ↦ -(1 : ℂ) / w ^ 2 := by
  let f : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ * ∫ z in ball (0 : ℂ) 1, (w - z)⁻¹
  have hT : cauchyTransform (discDatum (1 : ℂ)) = f := by
    funext w
    rw [discDatum_one_transform]
    exact (Complex.pi_inv_mul_integral_sub_inv_unit_ball w).symm
  have h := hasWeakFDerivOn_cauchy (c := 0) (r := 1) hp hp_top (discDatum_memLp (1 : ℂ) p)
    (discDatum_support _) ⊤
  rw [hT] at h
  have hD := h.ae_eq (hasWeakFDerivOn_pi_inv_mul_integral_sub_inv_ball zero_le_one 0)
  rw [Opens.coe_top, Measure.restrict_univ] at hD
  filter_upwards [hD, coe_global_jet hp hp_top (discDatum_memLp (1 : ℂ) p),
    ae_wirtingerDeriv_pi_inv_mul_integral_sub_inv_ball zero_le_one (0 : ℂ)] with w hD hj hw
  rw [hj, fderiv_eq_wirtingerPartsCLM] at hD
  exact (wirtingerPartsCLM_inj.mp hD).1.trans (by simpa [f] using hw)

/-- The nonzero scalar Cauchy transform is not globally `Lᵖ` at the lower test exponents. -/
theorem indicator_not_global (q : ℝ≥0∞) (hq : q ≠ 0) (hq_top : q ≠ ∞)
    (hq2 : q.toReal ≤ 2) : ¬ MemLp (cauchyTransform (discDatum (1 : ℂ))) q volume := by
  have hT : cauchyTransform (discDatum (1 : ℂ)) =
      fun w ↦ (Real.pi : ℂ)⁻¹ * ∫ z in ball (0 : ℂ) 1, (w - z)⁻¹ := by
    funext w
    rw [discDatum_one_transform]
    exact (Complex.pi_inv_mul_integral_sub_inv_unit_ball w).symm
  rw [hT, memLp_pi_inv_mul_integral_sub_inv_ball_iff zero_lt_one 0 hq hq_top]
  exact not_lt.mpr hq2

private theorem one_lt_fourThirds : 1 < (4 / 3 : ℝ≥0∞) := by
  rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
  norm_num

private theorem fourThirds_ne_top : (4 / 3 : ℝ≥0∞) ≠ ∞ :=
  ENNReal.div_ne_top (by norm_num) (by norm_num)

local instance fourThirdsFact : Fact (1 ≤ (4 / 3 : ℝ≥0∞)) := ⟨one_lt_fourThirds.le⟩
local instance twoFact : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance threeFact : Fact (1 ≤ (3 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The operators handle p=4/3, p=2 and p=3 with the same indicator source. -/
theorem indicator_three_exponents :
    (∀ᵐ w ∂volume, beurlingL (p := (4 / 3 : ℝ≥0∞)) (by
      rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
      norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))
      ((discDatum_memLp (1 : ℂ) _).toLp (discDatum (1 : ℂ))) w =
        (closedBall (0 : ℂ) 1)ᶜ.indicator (fun w ↦ -(1 : ℂ) / w ^ 2) w) ∧
    (∀ᵐ w ∂volume, beurlingL (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      ((discDatum_memLp (1 : ℂ) _).toLp (discDatum (1 : ℂ))) w =
        (closedBall (0 : ℂ) 1)ᶜ.indicator (fun w ↦ -(1 : ℂ) / w ^ 2) w) ∧
    (∀ᵐ w ∂volume, beurlingL (p := (3 : ℝ≥0∞)) (by norm_num) (by norm_num)
      ((discDatum_memLp (1 : ℂ) _).toLp (discDatum (1 : ℂ))) w =
        (closedBall (0 : ℂ) 1)ᶜ.indicator (fun w ↦ -(1 : ℂ) / w ^ 2) w) := by
  exact ⟨indicator_beurling (p := (4 / 3 : ℝ≥0∞))
      one_lt_fourThirds fourThirds_ne_top,
    indicator_beurling (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num),
    indicator_beurling (p := (3 : ℝ≥0∞)) (by norm_num) (by norm_num)⟩

/-- The p=4/3 graph has the indicator Cauchy value. -/
theorem fourThirds_graph_value :
    WeakDerivStep.prev _
      (graphL (p := (4 / 3 : ℝ≥0∞)) (by
        rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
        norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num)) 0 1 2
        (((discDatum_memLp (1 : ℂ) (4 / 3 : ℝ≥0∞)).restrict
          (closedBall (0 : ℂ) ((1 : ℝ≥0) : ℝ))).toLp (discDatum (1 : ℂ))))
      =ᵐ[volume.restrict (disc 0 2 : Set ℂ)]
        fun w ↦ if ‖w‖ ≤ 1 then conj w else w⁻¹ :=
  indicator_value one_lt_fourThirds fourThirds_ne_top

/-- The same p=4/3 source has no global Cauchy value class. -/
theorem fourThirds_not_global :
    ¬ MemLp (cauchyTransform (discDatum (1 : ℂ))) (4 / 3 : ℝ≥0∞) volume :=
  indicator_not_global _ (ne_of_gt (zero_lt_one.trans one_lt_fourThirds))
    fourThirds_ne_top (by norm_num [ENNReal.toReal_div])

end TauCeti.CauchyTransform.Examples

namespace TauCeti.CauchyTransform.VectorExamples

open TauCeti.CauchyTransform TauCeti.CauchyTransform.Examples

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The chosen target carries its original product sup norm. -/
theorem product_norm : ‖((1 : ℂ), 2 * I)‖ = 2 := by
  simp [Prod.norm_def]

/-- The coefficient is nonzero. -/
theorem product_ne_zero : ((1 : ℂ), 2 * I) ≠ 0 := by
  intro h
  have := congrArg Prod.fst h
  norm_num at this

private theorem datum_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (v : F) :
    discDatum v = fun z ↦ (ContinuousLinearMap.toSpanSingleton ℂ v) (discDatum (1 : ℂ) z) := by
  funext z
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · simp only [discDatum_apply, indicator_of_mem hz,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  · simp only [discDatum_apply, indicator_of_notMem hz,
      ContinuousLinearMap.toSpanSingleton_apply, zero_smul]

private theorem datum_toLp_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v : F) {μ : Measure ℂ} (hs : MemLp (discDatum (1 : ℂ)) p μ)
    (hv : MemLp (discDatum v) p μ) :
    hv.toLp (discDatum v) = (ContinuousLinearMap.toSpanSingleton ℂ v).compLpL p μ
      (hs.toLp (discDatum (1 : ℂ))) := by
  apply Lp.ext
  filter_upwards [hv.coeFn_toLp, hs.coeFn_toLp,
    (ContinuousLinearMap.toSpanSingleton ℂ v).coeFn_compLpL (hs.toLp _)] with z h₁ h₂ h₃
  rw [h₁, h₃, h₂, datum_line v]

/-- The Beurling operator in the product sup norm has the full nonzero vector tail. -/
theorem vector_beurling (hp : 1 < p) (hp_top : p ≠ ∞) :
    beurlingL hp hp_top
      ((discDatum_memLp ((1 : ℂ), 2 * I) p).toLp (discDatum ((1 : ℂ), 2 * I))) =ᵐ[volume]
      fun w ↦ ((closedBall (0 : ℂ) 1)ᶜ.indicator (fun w ↦ -(1 : ℂ) / w ^ 2) w) •
        ((1 : ℂ), 2 * I) := by
  rw [datum_toLp_line _ (discDatum_memLp (1 : ℂ) p), ← beurling_naturality hp hp_top]
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ ((1 : ℂ), 2 * I)).coeFn_compLpL
    (beurlingL hp hp_top ((discDatum_memLp (1 : ℂ) p).toLp (discDatum (1 : ℂ)))),
    indicator_beurling hp hp_top] with w hL hB
  simp only [hL, hB, ContinuousLinearMap.toSpanSingleton_apply]

/-- The new graph retains the exact vector Cauchy value in the original product norm. -/
theorem vector_value (hp : 1 < p) (hp_top : p ≠ ∞) :
    WeakDerivStep.prev _
      (graphL hp hp_top 0 1 2 (((discDatum_memLp ((1 : ℂ), 2 * I) p).restrict
        (closedBall (0 : ℂ) ((1 : ℝ≥0) : ℝ))).toLp (discDatum ((1 : ℂ), 2 * I))))
      =ᵐ[volume.restrict (disc 0 2 : Set ℂ)]
        fun w ↦ (if ‖w‖ ≤ 1 then conj w else w⁻¹) • ((1 : ℂ), 2 * I) := by
  rw [datum_toLp_line _ ((discDatum_memLp (1 : ℂ) p).restrict _), graphL_prev_naturality]
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ ((1 : ℂ), 2 * I)).coeFn_compLpL
    (WeakDerivStep.prev _ (graphL hp hp_top 0 1 2
      (((discDatum_memLp (1 : ℂ) p).restrict (closedBall (0 : ℂ) ((1 : ℝ≥0) : ℝ))).toLp
        (discDatum (1 : ℂ))))), indicator_value hp hp_top] with w hL hT
  simp only [hL, hT, ContinuousLinearMap.toSpanSingleton_apply]

/-- two-complex-parameter families are continuous in the original-norm graph. -/
theorem two_parameter_graph (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (u v : Lp (ℂ × ℂ) p (volume.restrict (closedBall c (r : ℝ)))) :
    Continuous fun z : ℂ × ℂ ↦ graphL hp hp_top c r R (z.1 • u + z.2 • v) := by
  exact (graphL hp hp_top c r R).continuous.comp
    ((continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const))

/-- An invertible constant frame change swaps the two nonzero output coefficients. -/
theorem swapped_frame_value (hp : 1 < p) (hp_top : p ≠ ∞) :
    let e := ContinuousLinearEquiv.prodComm ℂ ℂ ℂ
    WeakDerivStep.prev _
      (graphL hp hp_top 0 1 2
        (e.toContinuousLinearMap.compLpL p
          (volume.restrict (closedBall (0 : ℂ) ((1 : ℝ≥0) : ℝ)))
          (((discDatum_memLp ((1 : ℂ), 2 * I) p).restrict
            (closedBall (0 : ℂ) ((1 : ℝ≥0) : ℝ))).toLp (discDatum ((1 : ℂ), 2 * I)))))
      =ᵐ[volume.restrict (disc 0 2 : Set ℂ)]
        fun w ↦ (if ‖w‖ ≤ 1 then conj w else w⁻¹) • (2 * I, (1 : ℂ)) := by
  dsimp only
  rw [graphL_prev_naturality]
  filter_upwards [(ContinuousLinearEquiv.prodComm ℂ ℂ ℂ).toContinuousLinearMap.coeFn_compLpL
    (WeakDerivStep.prev _ (graphL hp hp_top 0 1 2
      (((discDatum_memLp ((1 : ℂ), 2 * I) p).restrict
        (closedBall (0 : ℂ) ((1 : ℝ≥0) : ℝ))).toLp (discDatum ((1 : ℂ), 2 * I))))),
    vector_value hp hp_top] with w he hvalue
  rw [he, hvalue, map_smul]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk]

end TauCeti.CauchyTransform.VectorExamples

namespace TauCeti.CauchyTransform.Degenerate

open TauCeti.CauchyTransform

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The empty coefficient index is accepted by the constructed graph map. -/
theorem empty_coefficients (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (u : Lp (Empty → ℂ) p (volume.restrict (closedBall c (r : ℝ)))) :
    graphL hp hp_top c r R u = 0 := by
  have hu : u = 0 := by
    apply Lp.ext
    exact .of_forall fun _ ↦ Subsingleton.elim _ _
  rw [hu, map_zero]

/-- The global original-norm Beurling map also retains the empty coefficient index. -/
theorem empty_coefficients_beurling (hp : 1 < p) (hp_top : p ≠ ∞)
    (u : Lp (Empty → ℂ) p (volume : Measure ℂ)) : beurlingL hp hp_top u = 0 := by
  have hu : u = 0 := by
    apply Lp.ext
    exact .of_forall fun _ ↦ Subsingleton.elim _ _
  rw [hu, map_zero]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- A zero-radius input is the zero input, without a nonzero-radius assumption. -/
theorem zero_input_radius (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (R : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c ((0 : ℝ≥0) : ℝ)))) :
    graphL hp hp_top c 0 R u = 0 := by
  have hfilter : ae (volume.restrict (closedBall c ((0 : ℝ≥0) : ℝ))) = ⊥ := by simp
  have hu : u = 0 := by
    apply Lp.ext
    rw [hfilter]
    exact Filter.eventually_bot
  rw [hu, map_zero]

/-- A zero-radius open output is the zero graph. -/
theorem zero_output_radius (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r : ℝ≥0)
    (u : Lp F p (volume.restrict (closedBall c (r : ℝ)))) :
    graphL hp hp_top c r 0 u = 0 := by
  have hfilter : ae (volume.restrict (disc c 0 : Set ℂ)) = ⊥ := by simp
  apply WeakDerivStep.ext
  apply Lp.ext
  rw [hfilter]
  exact Filter.eventually_bot

/-- The new complex-valued graph has the existing real scalar Sobolev projection. -/
theorem real_scalar_value (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (u : Lp ℂ p (volume.restrict (closedBall c (r : ℝ)))) :
    W1p.value (WeakDerivStep.toW1pL _ Complex.reCLM (graphL hp hp_top c r R u)) =
      Complex.reCLM.compLpL p (volume.restrict (disc c R : Set ℂ)) (valueL c r R u) := by
  rw [WeakDerivStep.value_toW1pL, ContinuousLinearMap.id_apply, graphL_prev]

/-- Its existing real gradient is the real component of the Cauchy weak jet. -/
theorem real_scalar_gradient (hp : 1 < p) (hp_top : p ≠ ∞) (c : ℂ) (r R : ℝ≥0)
    (u : Lp ℂ p (volume.restrict (closedBall c (r : ℝ)))) :
    ∀ᵐ w ∂volume.restrict (disc c R : Set ℂ), ∀ v : ℂ,
      ⟪W1p.gradient (WeakDerivStep.toW1pL _ Complex.reCLM
        (graphL hp hp_top c r R u)) w, v⟫_ℝ =
      (jetL (beurlingL hp hp_top) (zeroExtend c r u) w v).re := by
  have h := WeakDerivStep.inner_gradient_toW1pL_ae _ Complex.reCLM
    (graphL hp hp_top c r R u)
  rw [graphL_weakFDeriv] at h
  filter_upwards [h, LpToLpRestrictCLM_coeFn ℂ (disc c R : Set ℂ)
    (jetL (beurlingL hp hp_top) (zeroExtend c r u))] with w hw hD
  intro v
  simpa only [hD, Complex.reCLM_apply] using hw v

end TauCeti.CauchyTransform.Degenerate
