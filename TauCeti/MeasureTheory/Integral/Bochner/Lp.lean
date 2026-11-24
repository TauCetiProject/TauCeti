/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Integrating representatives of Lᵖ curves

On a σ-finite sample measure, an integrable curve in `Lp E p`, with `1 ≤ p ≤ ∞` and
Banach codomain `E`, can be integrated samplewise whenever its representatives are jointly
almost everywhere strongly measurable. The resulting ordinary integral represents the
Bochner integral in `Lp E p`. This connects mean-square process integrals to ordinary
time integrals, and `Lᵖ`-valued integrals of evolution semigroups on `ℝⁿ` to pointwise
integrals, without treating point evaluation as a continuous functional on `Lᵖ`. On a finite
sample measure the representatives are moreover jointly integrable.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory

/-- Testing against a bounded measurable multiplier preserves convergence of the
integrals along an `L¹`-convergent family. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm {α : Type*} [MeasurableSpace α]
    {ι : Type*} {l : Filter ι} {ν : Measure α} {u : ι → α → ℝ} {v f : α → ℝ}
    (hu : ∀ᶠ i in l, Integrable (u i) ν)
    (hv : Integrable v ν) (hf : AEStronglyMeasurable f ν) {B : ℝ} (hB : ∀ᵐ x ∂ν, ‖f x‖ ≤ B)
    (h : Tendsto (fun n ↦ eLpNorm (u n - v) 1 ν) l (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, f x * u n x ∂ν) l (𝓝 (∫ x, f x * v x ∂ν)) := by
  have hF : ∀ᶠ i in l, Integrable (fun x ↦ f x * u i x) ν :=
    hu.mono fun _ hi ↦ hi.bdd_mul hf hB
  have hG : Integrable (fun x ↦ f x * v x) ν := hv.bdd_mul hf hB
  refine tendsto_integral_of_L1' _ hF ?_
  have hmul := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal B) h (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [mul_zero] using hmul)
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [hu, hF] with i hi hiF
  rw [eLpNorm_one_eq_lintegral_eNorm (hiF.sub hG).aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_eNorm (hi.sub hv).aestronglyMeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hB] with x hx
  simp only [Pi.sub_apply, ← mul_sub, eNorm_mul]
  gcongr
  exact (Real.eNorm_eq_ofReal_abs _).le.trans (ENNReal.ofReal_le_ofReal hx)

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
  {μ : Measure α} {P : Measure Ω}
  {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : α → Lp E p P} {X : α → Ω → E}

/-- Jointly measurable representatives of an integrable Lᵖ curve, with `1 ≤ p ≤ ∞`,
are integrable on the product of the parameter measure and a finite sample measure. -/
theorem Integrable.integrable_uncurry_of_ae_eq_Lp [IsFiniteMeasure P] (hF : Integrable F μ)
    (hX : AEStronglyMeasurable (Function.uncurry X) (μ.prod P))
    (heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] X t) :
    Integrable (Function.uncurry X) (μ.prod P) := by
  refine (integrable_prod_iff hX).2 ⟨?_, ?_⟩
  · filter_upwards [heq] with t ht
    exact ((Lp.memLp (F t)).integrable Fact.out).congr ht
  · refine (hF.norm.const_mul
      ((P Set.univ ^ (1 - 1 / p.toReal)).toReal)).mono'
      hX.norm.integral_prod_right' ?_
    filter_upwards [heq] with t ht
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
      ← integral_congr_ae (ht.mono fun ω hω ↦ congrArg (‖·‖) hω)]
    exact Lp.integral_norm_le_mul_norm (F t)

variable [SFinite μ] [NormedSpace ℝ E] [CompleteSpace E]

/-- The case of a finite sample measure of `MeasureTheory.Integrable.coeFn_integral_Lp`. -/
private theorem Integrable.coeFn_integral_Lp_of_isFiniteMeasure [IsFiniteMeasure P]
    (hF : Integrable F μ)
    (hX : AEStronglyMeasurable (Function.uncurry X) (μ.prod P))
    (heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] X t) :
    ⇑(∫ t, F t ∂μ) =ᵐ[P] fun ω ↦ ∫ t, X t ω ∂μ := by
  have hi := hF.integrable_uncurry_of_ae_eq_Lp hX heq
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp _).integrable Fact.out) hi.integral_prod_right fun s hs _ ↦ ?_
  let q := ENNReal.conjExponent p
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let c := indicatorConstLp q hs (measure_ne_top P s) (1 : ℝ)
  let L := ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).flip.lpPairing P p q).flip c
  have hL (f : Lp E p P) : L f = ∫ ω in s, f ω ∂P := by
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral,
      ← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := q) (hs := hs)
      (hμs := measure_ne_top P s) (c := (1 : ℝ))] with ω hω
    by_cases hmem : ω ∈ s <;> simp [c, hω, hmem]
  rw [← hL, ← L.integral_comp_comm hF]
  have hi' : Integrable (Function.uncurry X) (μ.prod (P.restrict s)) :=
    hi.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [← integral_integral_swap hi']
  refine integral_congr_ae ?_
  filter_upwards [heq] with t ht
  rw [hL]
  exact integral_congr_ae (ae_restrict_of_ae ht)

/-- The ordinary samplewise integral of jointly measurable representatives of an
integrable Lᵖ curve, with `1 ≤ p ≤ ∞`, represents its Lᵖ-valued Bochner integral, on a
σ-finite sample measure. -/
theorem Integrable.coeFn_integral_Lp [SigmaFinite P] (hF : Integrable F μ)
    (hX : AEStronglyMeasurable (Function.uncurry X) (μ.prod P))
    (heq : ∀ᵐ t ∂μ, ⇑(F t) =ᵐ[P] X t) :
    ⇑(∫ t, F t ∂μ) =ᵐ[P] fun ω ↦ ∫ t, X t ω ∂μ := by
  -- On a set `s` of finite measure, restrict the curve to `Lp E p (P.restrict s)`.
  refine ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hs ↦ ?_
  have _ : IsFiniteMeasure (P.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  set R := LpToLpRestrictCLM Ω E ℝ P p s
  have h := (R.integrable_comp hF).coeFn_integral_Lp_of_isFiniteMeasure
    (hX.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)) <| by
      filter_upwards [heq] with t ht
      exact (LpToLpRestrictCLM_coeFn ℝ s (F t)).trans (ae_restrict_of_ae ht)
  rw [R.integral_comp_comm hF] at h
  exact (LpToLpRestrictCLM_coeFn ℝ s _).symm.trans h

end MeasureTheory
