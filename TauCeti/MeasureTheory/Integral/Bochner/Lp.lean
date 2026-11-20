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

On a finite sample measure, an integrable curve in `Lp E p`, with `1 ≤ p ≤ ∞` and
Banach codomain `E`, can be integrated samplewise whenever its representatives are jointly
almost everywhere strongly measurable. The resulting ordinary integral represents the
Bochner integral in `Lp E p`. This connects mean-square process integrals to ordinary
time integrals, without treating point evaluation as a continuous functional on `Lᵖ`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
  {μ : Measure α} {P : Measure Ω} [IsFiniteMeasure P]
  {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : α → Lp E p P} {X : α → Ω → E}

/-- Jointly measurable representatives of an integrable Lᵖ curve, with `1 ≤ p ≤ ∞`,
are integrable on the product of the parameter measure and a finite sample measure. -/
theorem Integrable.integrable_uncurry_of_ae_eq_Lp (hF : Integrable F μ)
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

/-- The ordinary samplewise integral of jointly measurable representatives of an
integrable Lᵖ curve, with `1 ≤ p ≤ ∞`, represents its Lᵖ-valued Bochner integral. -/
theorem Integrable.coeFn_integral_Lp (hF : Integrable F μ)
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

end MeasureTheory
