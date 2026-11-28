/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.VectorMeasure.RadonNikodymProperty.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.VectorMeasure.AddContent

/-!
# The Radon–Nikodým property passes to sub-σ-algebras

Let `m ≤ m0` be a sub-σ-algebra and `μ` a measure on `m0`. If a real Banach space `X` has the
Radon–Nikodým property with respect to `μ`, then it has the Radon–Nikodým property with respect to
the trimmed measure `μ.trim hm`, provided that `μ.trim hm` is σ-finite; this holds in particular
for every finite measure `μ`. This stability is an ingredient of the separable determination of
the Radon–Nikodým property.

For a finite measure, let `ν` be an `X`-valued vector measure on `m` of finite variation with
`|ν| ≪ μ.trim hm`. It extends to the vector measure

`ν' A = ∫ μ[𝟙_A | m] dν`

on `m0`, integrating the conditional expectation of the indicator of `A` against `ν`. Writing
`h = d|ν| / d(μ.trim hm)`, the pull-out property of conditional expectation gives
`‖ν' A‖ ≤ ∫_A h dμ`. Hence `ν'` is countably additive (`VectorMeasure.of_additive_of_le_measure`),
has finite variation and satisfies `|ν'| ≪ μ`. On `m`-measurable sets it agrees with `ν`. If
`ν' = μ.withDensityᵥ f`, then the conditional expectation `μ[f | m]` is an `m`-measurable density
of `ν` with respect to `μ.trim hm`. Completeness of `X` is used for the integrals defining `ν'`.

The σ-finite case reduces to the finite one: an `m`-measurable positive weight `w` with finite
integral makes `μ.withDensity w` a finite measure equivalent to `μ` whose trim is equivalent to
`μ.trim hm`. Equivalent σ-finite measures carry the same Radon–Nikodým property.

## Main declarations

* `TauCeti.HasRNPWith.trim`: the Radon–Nikodým property with respect to `μ` gives the
  Radon–Nikodým property with respect to `μ.trim hm` when the latter is σ-finite.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Lemma 1.3.17.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {S X : Type*} {m m0 : MeasurableSpace S} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {μ : Measure[m0] S}

section Finite

/-- The real density `(d|ν| / d(μ.trim hm)).toReal` of the variation of `ν`, as a function on
`S`. -/
private noncomputable abbrev variationDensity (ν : @VectorMeasure S m X _ _) (μ : Measure[m0] S)
    (hm : m ≤ m0) : S → ℝ :=
  fun x => (ν.variation.rnDeriv (μ.trim hm) x).toReal

omit [NormedSpace ℝ X] in
private theorem stronglyMeasurable_variationDensity (hm : m ≤ m0) (ν : @VectorMeasure S m X _ _) :
    StronglyMeasurable[m] (variationDensity ν μ hm) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal.stronglyMeasurable

omit [NormedSpace ℝ X] in
private theorem integrable_variationDensity (hm : m ≤ m0) (ν : @VectorMeasure S m X _ _)
    [IsFiniteMeasure ν.variation] : Integrable (variationDensity ν μ hm) μ :=
  integrable_of_integrable_trim hm Measure.integrable_toReal_rnDeriv

omit [NormedSpace ℝ X] in
/-- The conditional expectation of an indicator is integrable against `ν`, with
`∫ |μ[𝟙_A | m]| d|ν| = ∫_A (d|ν| / d(μ.trim hm)) dμ`. -/
private theorem integrable_condExp_indicator [IsFiniteMeasure μ] (hm : m ≤ m0)
    {ν : @VectorMeasure S m X _ _} [IsFiniteMeasure ν.variation] (hac : ν.variation ≪ μ.trim hm)
    {A : Set S} (hA : MeasurableSet A) :
    Integrable (μ[A.indicator (1 : S → ℝ) | m]) ν.variation ∧
      ∫ x, ‖μ[A.indicator (1 : S → ℝ) | m] x‖ ∂ν.variation =
        ∫ x in A, variationDensity ν μ hm x ∂μ := by
  set g := μ[A.indicator (1 : S → ℝ) | m]
  set h := variationDensity ν μ hm
  have hgm : StronglyMeasurable[m] g := stronglyMeasurable_condExp
  have hhm : StronglyMeasurable[m] h := stronglyMeasurable_variationDensity hm ν
  have hhi : Integrable h μ := integrable_variationDensity hm ν
  -- `0 ≤ g ≤ 1` almost everywhere, since `0 ≤ 𝟙_A ≤ 1`.
  have hg0 : 0 ≤ᵐ[μ] g := condExp_nonneg (ae_of_all _ fun x => indicator_nonneg
    (fun _ _ => zero_le_one (α := ℝ)) x)
  have hg1 : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1 := ae_bdd_norm_condExp_of_ae_bdd_norm (ae_of_all _ fun x => by
    by_cases hx : x ∈ A <;> simp [hx])
  have hint : Integrable (fun x => h x * g x) μ :=
    hhi.mul_bdd (hgm.mono hm).aestronglyMeasurable hg1
  refine ⟨(integrable_rnDeriv_smul_iff hac).1 (hint.trim hm (hhm.mul hgm)), ?_⟩
  -- Pull the `m`-measurable weight `h` into the conditional expectation.
  have hAh : A.indicator (1 : S → ℝ) * h = A.indicator h := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hi : Integrable (A.indicator (1 : S → ℝ) * h) μ := by
    rw [hAh]
    exact hhi.indicator hA
  have hpull := condExp_mul_of_stronglyMeasurable_right hhm hi ((integrable_const 1).indicator hA)
  have hnorm : (fun x => h x * ‖g x‖) =ᵐ[μ] g * h := by
    filter_upwards [hg0] with x hx
    rw [Real.norm_of_nonneg hx, mul_comm, Pi.mul_apply]
  calc ∫ x, ‖g x‖ ∂ν.variation
      = ∫ x, h x * ‖g x‖ ∂(μ.trim hm) := (integral_rnDeriv_smul hac).symm
    _ = ∫ x, h x * ‖g x‖ ∂μ := (integral_trim hm (hhm.mul hgm.norm)).symm
    _ = ∫ x, μ[A.indicator (1 : S → ℝ) * h | m] x ∂μ :=
      integral_congr_ae (hnorm.trans hpull.symm)
    _ = ∫ x, (A.indicator (1 : S → ℝ) * h) x ∂μ := integral_condExp hm
    _ = ∫ x in A, h x ∂μ := by rw [hAh, integral_indicator hA]

open scoped Classical in
/-- The set function `A ↦ ∫ μ[𝟙_A | m] dν` on `m0`, extending `ν` from `m`. -/
private noncomputable def extendSetFun (ν : @VectorMeasure S m X _ _) (μ : Measure[m0] S)
    (A : Set S) : X :=
  if MeasurableSet A then ∫ᵛ x, μ[A.indicator (1 : S → ℝ) | m] x ∂• ν else 0

private theorem extendSetFun_of_measurableSet (ν : @VectorMeasure S m X _ _) {A : Set S}
    (hA : MeasurableSet A) :
    extendSetFun ν μ A = ∫ᵛ x, μ[A.indicator (1 : S → ℝ) | m] x ∂• ν := by
  simp [extendSetFun, hA]

private theorem extendSetFun_of_not_measurableSet (ν : @VectorMeasure S m X _ _) {A : Set S}
    (hA : ¬MeasurableSet A) : extendSetFun ν μ A = 0 := by
  simp [extendSetFun, hA]

/-- The extended set function is dominated by the measure `μ.withDensity (d|ν| / d(μ.trim hm))`. -/
private theorem eNorm_extendSetFun_le [IsFiniteMeasure μ] (hm : m ≤ m0)
    {ν : @VectorMeasure S m X _ _} [IsFiniteMeasure ν.variation] (hac : ν.variation ≪ μ.trim hm)
    (A : Set S) :
    ‖extendSetFun ν μ A‖ₑ ≤
      μ.withDensity (fun x => ENNReal.ofReal (variationDensity ν μ hm x)) A := by
  by_cases hA : MeasurableSet A
  swap
  · simp [extendSetFun_of_not_measurableSet ν hA]
  have hh0 : 0 ≤ᵐ[μ] variationDensity ν μ hm := ae_of_all _ fun _ => ENNReal.toReal_nonneg
  rw [withDensity_apply _ hA, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_variationDensity hm ν).integrableOn (ae_restrict_of_ae hh0),
    ← (integrable_condExp_indicator hm hac hA).2, extendSetFun_of_measurableSet ν hA,
    ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ((VectorMeasure.norm_integral_le_integral_norm).trans ?_)
  exact mul_le_of_le_one_left (integral_nonneg fun _ => norm_nonneg _)
    ContinuousLinearMap.opNorm_lsmul_le

/-- The extended set function is additive on disjoint measurable sets. -/
private theorem extendSetFun_union [IsFiniteMeasure μ] (hm : m ≤ m0)
    {ν : @VectorMeasure S m X _ _} [IsFiniteMeasure ν.variation] (hac : ν.variation ≪ μ.trim hm)
    {A B : Set S} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    extendSetFun ν μ (A ∪ B) = extendSetFun ν μ A + extendSetFun ν μ B := by
  have hiA : Integrable (A.indicator (1 : S → ℝ)) μ := (integrable_const 1).indicator hA
  have hiB : Integrable (B.indicator (1 : S → ℝ)) μ := (integrable_const 1).indicator hB
  have hsum : μ[(A ∪ B).indicator (1 : S → ℝ) | m] =ᵐ[ν.variation]
      μ[A.indicator (1 : S → ℝ) | m] + μ[B.indicator (1 : S → ℝ) | m] := by
    refine hac.ae_eq (StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
      stronglyMeasurable_condExp (stronglyMeasurable_condExp.add stronglyMeasurable_condExp) ?_)
    rw [indicator_union_of_disjoint hAB]
    exact condExp_add hiA hiB m
  rw [extendSetFun_of_measurableSet ν (hA.union hB), extendSetFun_of_measurableSet ν hA,
    extendSetFun_of_measurableSet ν hB, VectorMeasure.integral_congr_ae hsum,
    VectorMeasure.integral_add (integrable_condExp_indicator hm hac hA).1
      (integrable_condExp_indicator hm hac hB).1]

/-- The extension of `ν` to `m0`, as a vector measure. -/
private noncomputable def extend [IsFiniteMeasure μ] (hm : m ≤ m0) (ν : @VectorMeasure S m X _ _)
    [IsFiniteMeasure ν.variation] (hac : ν.variation ≪ μ.trim hm) : VectorMeasure S X :=
  have := isFiniteMeasure_withDensity_ofReal (integrable_variationDensity (μ := μ) hm ν).2
  VectorMeasure.of_additive_of_le_measure (extendSetFun ν μ) (eNorm_extendSetFun_le hm hac)
    (fun _ _ hA hB hAB => extendSetFun_union hm hac hA hB hAB)
    (fun _ hA => extendSetFun_of_not_measurableSet ν hA)

private theorem extend_apply [IsFiniteMeasure μ] (hm : m ≤ m0) (ν : @VectorMeasure S m X _ _)
    [IsFiniteMeasure ν.variation] (hac : ν.variation ≪ μ.trim hm) (A : Set S) :
    extend hm ν hac A = extendSetFun ν μ A :=
  rfl

variable [CompleteSpace X]

/-- On an `m`-measurable set, the extension takes the value of `ν`. -/
private theorem extend_apply_of_measurableSet [IsFiniteMeasure μ] (hm : m ≤ m0)
    (ν : @VectorMeasure S m X _ _) [IsFiniteMeasure ν.variation] (hac : ν.variation ≪ μ.trim hm)
    {B : Set S} (hB : MeasurableSet[m] B) : extend hm ν hac B = ν B := by
  have hB0 : MeasurableSet B := hm B hB
  rw [extend_apply, extendSetFun_of_measurableSet ν hB0, condExp_of_stronglyMeasurable hm
    (f := B.indicator (1 : S → ℝ)) (stronglyMeasurable_const.indicator hB)
    ((integrable_const 1).indicator hB0)]
  have h1 := VectorMeasure.integral_indicator_const (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := ν) (1 : ℝ) hB
  simp only [ContinuousLinearMap.lsmul_apply, one_smul] at h1
  exact h1

/-- **The Radon–Nikodým property passes to sub-σ-algebras of a finite measure space.** -/
private theorem HasRNPWith.trim_of_isFiniteMeasure [IsFiniteMeasure μ] (hm : m ≤ m0)
    (h : HasRNPWith X μ) : @HasRNPWith S m X _ _ (μ.trim hm) := by
  refine (@hasRNPWith_def S m X _ _ (μ.trim hm)).2 fun ν _ hac => ?_
  have := isFiniteMeasure_withDensity_ofReal (integrable_variationDensity (μ := μ) hm ν).2
  have hvar : (extend hm ν hac).variation ≤
      μ.withDensity (fun x => ENNReal.ofReal (variationDensity ν μ hm x)) :=
    VectorMeasure.variation_le_of_forall_eNorm_le fun A _ => eNorm_extendSetFun_le hm hac A
  have : IsFiniteMeasure (extend hm ν hac).variation := isFiniteMeasure_of_le _ hvar
  obtain ⟨f, hf, hfν⟩ := h.exists_density (extend hm ν hac)
    ((Measure.absolutelyContinuous_of_le hvar).trans (withDensity_absolutelyContinuous _ _))
  have hfi : Integrable (μ[f | m]) (μ.trim hm) :=
    integrable_condExp.trim hm stronglyMeasurable_condExp
  refine ⟨μ[f | m], hfi, ?_⟩
  ext B hB
  rw [← extend_apply_of_measurableSet hm ν hac hB, hfν, withDensityᵥ_apply hf (hm B hB),
    withDensityᵥ_apply hfi hB, ← setIntegral_condExp hm hf hB,
    setIntegral_trim hm stronglyMeasurable_condExp hB]

end Finite

/-- **The Radon–Nikodým property passes to sub-σ-algebras.** If a real Banach space `X` has the
Radon–Nikodým property with respect to `μ`, it has the Radon–Nikodým property with respect to the
trim of `μ` to a sub-σ-algebra `m`, provided that this trim is σ-finite. This is the case for
every finite measure `μ`. -/
theorem HasRNPWith.trim [CompleteSpace X] (h : HasRNPWith X μ) (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] : @HasRNPWith S m X _ _ (μ.trim hm) := by
  have : SigmaFinite μ := SigmaFinite.of_trim hm
  -- A positive `m`-measurable weight of finite integral gives an equivalent finite measure.
  obtain ⟨w, hw_pos, hw_meas, hw_int⟩ :=
    @exists_pos_lintegral_lt_of_sigmaFinite S m (μ.trim hm) _ 1 one_ne_zero
  have hwm : Measurable[m] fun x => (w x : ℝ≥0∞) := hw_meas.coe_nnreal_ennreal
  have hw0 : ∀ x, (w x : ℝ≥0∞) ≠ 0 := fun x => ENNReal.coe_ne_zero.2 (hw_pos x).ne'
  have : IsFiniteMeasure (μ.withDensity fun x => (w x : ℝ≥0∞)) := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← lintegral_trim hm hwm]
    exact hw_int.trans ENNReal.one_lt_top⟩
  have : IsFiniteMeasure ((μ.trim hm).withDensity fun x => (w x : ℝ≥0∞)) := by
    rw [← trim_withDensity hm hwm]
    infer_instance
  have h' : HasRNPWith X (μ.withDensity fun x => (w x : ℝ≥0∞)) :=
    (hasRNPWith_congr_ac (withDensity_absolutelyContinuous' (hwm.mono hm le_rfl).aemeasurable
      (ae_of_all _ hw0)) (withDensity_absolutelyContinuous _ _)).1 h
  have h'' := HasRNPWith.trim_of_isFiniteMeasure hm h'
  rw [trim_withDensity hm hwm] at h''
  exact (@hasRNPWith_congr_ac S m X _ _ _ _ _ _ (withDensity_absolutelyContinuous _ _)
    (withDensity_absolutelyContinuous' hwm.aemeasurable (ae_of_all _ hw0))).1 h''

end TauCeti
