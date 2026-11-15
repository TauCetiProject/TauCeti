/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Multiplicity
public import TauCeti.MeasureTheory.Function.MetricDerivative.ConstantSpeed
public import TauCeti.MeasureTheory.Function.MetricDerivative.Variation
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# The area formula for curves

This file specializes the area formula with multiplicity to maps from a real interval. For a
curve Lipschitz on a compact interval, the integral of a weight against its speed is the
one-dimensional Hausdorff integral of the weight summed over each fiber, including infinite
fibers. For the constant weight one, the speed integrates to the length, and the formula becomes
the Lipschitz case of the Banach indicatrix formula `ContinuousOn.eVariationOn_eq_lintegral_encard`,
which holds for every continuous curve in an extended metric space.

When the curve is injective on the open interval `(a, b)` — covering both injective arcs and
simple closed curves — the fiber over `μHE[1]`-almost every point of the trace has cardinality
one. Consequently, pushing forward the speed-weighted interval measure `(‖deriv γ ·‖ₑ) dt` on
`[a, b]` along `γ` yields `μHE[1].restrict (γ '' Icc a b)`. For a curve of constant speed `l`,
this becomes `(l : ℝ≥0∞) • (volume.restrict (Icc a b)).map γ = μHE[1].restrict (γ '' Icc a b)`,
and for a unit-speed curve `HasUnitSpeedOn γ (Icc a b)` the interval Lebesgue measure pushes
forward directly to `μHE[1]` on the trace, identifying `μHE[1]`-integrability and Bochner
integrals over `γ '' Icc a b` with parameter integrability and integrals over `[a, b]`.

The curve need only be Lipschitz on the parameter interval. A finite-dimensional Lipschitz
extension reduces the result to the global area formula; derivatives and fiber sums are then
transported back to the original curve. The one-dimensional geometric Jacobian is identified
with the norm of the velocity.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, Section 3.3 (the area formula for Lipschitz maps).
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace LipschitzOnWith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {K : ℝ≥0} {γ : ℝ → V} {a b : ℝ}

/-- The weighted area formula for a curve Lipschitz on a compact interval. The weight is attached
to the parameter, and the right-hand side sums it over every fiber, including infinite fibers. -/
theorem lintegral_enorm_deriv_mul_eq_lintegral_tsum (hγ : LipschitzOnWith K γ (Icc a b))
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t in Icc a b, ‖deriv γ t‖ₑ * g t =
      ∫⁻ y, ∑' t : ↥(Icc a b ∩ γ ⁻¹' {y}), g t ∂μHE[1] := by
  obtain ⟨f, hf, hfeq⟩ := hγ.extend_finite_dimension
  have harea := hf.lintegral_normDet_fderiv_mul_eq_lintegral_tsum
    (nullMeasurableSet_Icc : NullMeasurableSet (Icc a b) volume) hg
  rw [Module.finrank_self] at harea
  have hsets (y : V) : Icc a b ∩ f ⁻¹' {y} = Icc a b ∩ γ ⁻¹' {y} := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact and_congr_right fun ht ↦ by rw [hfeq ht]
  have hfibers (y : V) :
      (∑' t : ↥(Icc a b ∩ f ⁻¹' {y}), g t) =
        ∑' t : ↥(Icc a b ∩ γ ⁻¹' {y}), g t := by
    rw [hsets y]
  calc
    (∫⁻ t in Icc a b, ‖deriv γ t‖ₑ * g t) =
        ∫⁻ t in Icc a b, ENNReal.ofReal (fderiv ℝ f t).normDet * g t := by
      apply setLIntegral_congr_fun_ae measurableSet_Icc
      filter_upwards [volume.ae_ne a, volume.ae_ne b] with t hta htb ht
      have ht' : t ∈ Ioo a b :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
      have heq : f =ᶠ[nhds t] γ := by
        filter_upwards [Icc_mem_nhds ht'.1 ht'.2] with x hx
        exact (hfeq hx).symm
      rw [heq.fderiv_eq, LinearMap.normDet_eq_norm_apply_one]
      rw [ofReal_norm, ContinuousLinearMap.coe_coe, fderiv_apply_one_eq_deriv]
    _ = ∫⁻ y, ∑' t : ↥(Icc a b ∩ f ⁻¹' {y}), g t ∂μHE[1] := harea
    _ = _ := lintegral_congr hfibers

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Away from the two endpoints `γ a` and `γ b`, injectivity on `(a, b)` collapses the fiber sum of
the indicator of `Icc a b ∩ γ ⁻¹' S` to the indicator of `γ '' Icc a b ∩ S`. -/
private theorem ae_tsum_fiber_indicator_eq (hinj : InjOn γ (Ioo a b)) (S : Set V) :
    (fun y => ∑' t : ↥(Icc a b ∩ γ ⁻¹' {y}),
      (Icc a b ∩ γ ⁻¹' S).indicator (1 : ℝ → ℝ≥0∞) t) =ᵐ[μHE[1]]
      (γ '' Icc a b ∩ S).indicator (1 : V → ℝ≥0∞) := by
  have := Measure.nullSingletonClass_hausdorff V zero_lt_one
  have hnull : μHE[1] ({γ a, γ b} : Set V) = 0 := by
    rw [Measure.euclideanHausdorffMeasure_one]
    exact (toFinite {γ a, γ b}).measure_zero μH[1]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
  by_cases hyCS : y ∈ γ '' Icc a b ∩ S
  · rw [indicator_of_mem hyCS]
    rcases hyCS with ⟨⟨t₀, ht₀, rfl⟩, hyS⟩
    have hIoo {t : ℝ} (ht : t ∈ Icc a b ∩ γ ⁻¹' {γ t₀}) : t ∈ Ioo a b := by
      have hty : γ t = γ t₀ := ht.2
      refine ⟨ht.1.1.lt_of_ne ?_, ht.1.2.lt_of_ne ?_⟩ <;> rintro rfl <;> simp [hty] at hy
    let _ : Unique ↥(Icc a b ∩ γ ⁻¹' {γ t₀}) :=
      { default := ⟨t₀, ht₀, rfl⟩
        uniq := fun ⟨t, ht⟩ => Subtype.ext (hinj (hIoo ht) (hIoo ⟨ht₀, rfl⟩) ht.2) }
    rw [tsum_fintype, Fintype.sum_unique]
    exact indicator_of_mem (⟨ht₀, hyS⟩ : t₀ ∈ Icc a b ∩ γ ⁻¹' S) _
  · rw [indicator_of_notMem hyCS]
    exact tsum_eq_zero_iff.2 fun ⟨t, htIcc, hty⟩ =>
      indicator_of_notMem (fun (htA : t ∈ Icc a b ∩ γ ⁻¹' S) =>
        hyCS ⟨⟨t, htIcc, hty⟩, hty ▸ htA.2⟩) _

/-- For a Lipschitz curve on `[a, b]` injective on `(a, b)` (such as an injective arc or a simple
closed curve), pushing forward the speed-weighted measure `(‖deriv γ ·‖ₑ) dt` on `[a, b]` along `γ`
yields `μHE[1]` restricted to `γ '' Icc a b`. -/
theorem map_withDensity_enorm_deriv_eq_euclideanHausdorffMeasure_restrict
    (hγ : LipschitzOnWith K γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) :
    ((volume.restrict (Icc a b)).withDensity fun t => ‖deriv γ t‖ₑ).map γ =
      μHE[1].restrict (γ '' Icc a b) := by
  have haem : AEMeasurable γ (volume.restrict (Icc a b)) :=
    hγ.continuousOn.aemeasurable measurableSet_Icc
  have haem' : AEMeasurable γ ((volume.restrict (Icc a b)).withDensity fun t => ‖deriv γ t‖ₑ) :=
    haem.mono_ac (withDensity_absolutelyContinuous _ _)
  refine Measure.ext fun S hS => ?_
  set A : Set ℝ := Icc a b ∩ γ ⁻¹' S
  have hAeq : A = ((↑) : Icc a b → ℝ) '' ((Icc a b).domRestrict γ ⁻¹' S) := by
    ext t
    exact ⟨fun ⟨ht, hS'⟩ => ⟨⟨t, ht⟩, hS', rfl⟩, by rintro ⟨⟨x, hx⟩, hxS, rfl⟩; exact ⟨hx, hxS⟩⟩
  have hAm : MeasurableSet A := hAeq ▸ (MeasurableEmbedding.subtype_coe measurableSet_Icc
    |>.measurableSet_image.2 ((continuousOn_iff_continuous_domRestrict.1 hγ.continuousOn).measurable
      hS))
  have harea := hγ.lintegral_enorm_deriv_mul_eq_lintegral_tsum
    ((measurable_one : Measurable (1 : ℝ → ℝ≥0∞)).indicator hAm)
  have hlhs : (((volume.restrict (Icc a b)).withDensity fun t => ‖deriv γ t‖ₑ).map γ) S =
      ∫⁻ t in Icc a b, ‖deriv γ t‖ₑ * A.indicator (1 : ℝ → ℝ≥0∞) t := by
    rw [Measure.map_apply_of_aemeasurable haem' hS,
      withDensity_apply₀ _ (haem.nullMeasurable hS)]
    have hres : (volume.restrict (Icc a b)).restrict (γ ⁻¹' S) =
        (volume.restrict (Icc a b)).restrict A := by
      rw [Measure.restrict_restrict₀ (haem.nullMeasurable hS), Measure.restrict_restrict hAm]
      congr 1; ext t; simp only [A, mem_inter_iff]; tauto
    rw [hres, ← lintegral_indicator hAm fun t => ‖deriv γ t‖ₑ]
    exact setLIntegral_congr_fun measurableSet_Icc fun t _ => by
      by_cases htS : t ∈ A <;> simp [htS]
  have hrhs : (∫⁻ y, ∑' t : ↥(Icc a b ∩ γ ⁻¹' {y}), A.indicator (1 : ℝ → ℝ≥0∞) t ∂μHE[1]) =
      (μHE[1].restrict (γ '' Icc a b)) S :=
    (lintegral_congr_ae (ae_tsum_fiber_indicator_eq hinj S)).trans <| by
      rw [lintegral_indicator_one
        ((isCompact_Icc.image_of_continuousOn hγ.continuousOn).measurableSet.inter hS),
        Measure.restrict_apply hS, inter_comm]
  exact hlhs.trans (harea.trans hrhs)

end LipschitzOnWith

namespace HasConstantSpeedOnWith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {l : ℝ≥0} {γ : ℝ → V} {a b : ℝ}

/-- For a curve of constant speed `l` on `[a, b]` injective on `(a, b)`, `l` times the pushforward
of Lebesgue measure on `[a, b]` equals `μHE[1]` restricted to `γ '' Icc a b`. -/
theorem smul_map_restrict_Icc_eq_euclideanHausdorffMeasure_restrict
    (hγ : HasConstantSpeedOnWith γ (Icc a b) l) (hinj : InjOn γ (Ioo a b)) :
    (l : ℝ≥0∞) • (volume.restrict (Icc a b)).map γ = μHE[1].restrict (γ '' Icc a b) := by
  rcases lt_or_ge b a with hab | hab
  · simp [Icc_eq_empty_of_lt hab]
  have hγu : HasConstantSpeedOnWith γ (uIcc a b) l := by rwa [uIcc_of_le hab]
  rw [← hγ.lipschitzOnWith.map_withDensity_enorm_deriv_eq_euclideanHausdorffMeasure_restrict hinj,
    ← Measure.map_smul _ (hγ.lipschitzOnWith.continuousOn.aemeasurable measurableSet_Icc)]
  congr 1
  have hae : (fun t => ‖deriv γ t‖ₑ) =ᵐ[volume.restrict (Icc a b)] fun _ => (l : ℝ≥0∞) := by
    have hnorm := hγu.ae_norm_deriv_eq
    rw [uIcc_of_le hab] at hnorm
    filter_upwards [hnorm] with t ht
    rw [← ofReal_norm, ht.2, ENNReal.ofReal_coe_nnreal]
  rw [withDensity_congr_ae hae, withDensity_const]

end HasConstantSpeedOnWith

namespace HasUnitSpeedOn

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F]
  {γ : ℝ → V} {a b : ℝ}

/-- For a unit-speed curve on `[a, b]` injective on `(a, b)`, the pushforward of Lebesgue measure
on `[a, b]` along `γ` is `μHE[1]` restricted to `γ '' Icc a b`. -/
theorem map_restrict_Icc_eq_euclideanHausdorffMeasure_restrict
    (hγ : HasUnitSpeedOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) :
    (volume.restrict (Icc a b)).map γ = μHE[1].restrict (γ '' Icc a b) := by
  simpa using hγ.smul_map_restrict_Icc_eq_euclideanHausdorffMeasure_restrict hinj

/-- Pushing forward Lebesgue measure on `Ioo a b` along `(Ioo a b).domRestrict γ` recovers
`μHE[1].restrict (γ '' Icc a b)` for a unit-speed curve injective on `(a, b)`. -/
private theorem map_domRestrict_Ioo_eq_euclideanHausdorffMeasure_restrict
    (hγ : HasUnitSpeedOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) :
    Measure.map ((Ioo a b).domRestrict γ) (volume.comap ((↑) : Ioo a b → ℝ)) =
      μHE[1].restrict (γ '' Icc a b) := by
  have haem : AEMeasurable γ (volume.restrict (Ioo a b)) :=
    (hγ.lipschitzOnWith.continuousOn.mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo
  have hmap : Measure.map ((Ioo a b).domRestrict γ) (volume.comap ((↑) : Ioo a b → ℝ)) =
      (volume.restrict (Ioo a b)).map γ := by
    have hcomp : (Ioo a b).domRestrict γ = γ ∘ ((↑) : Ioo a b → ℝ) := rfl
    rw [← map_comap_subtype_coe measurableSet_Ioo] at haem ⊢
    rw [hcomp, AEMeasurable.map_map_of_aemeasurable haem measurable_subtype_coe.aemeasurable]
  rw [hmap, Measure.restrict_congr_set Ioo_ae_eq_Icc,
    hγ.map_restrict_Icc_eq_euclideanHausdorffMeasure_restrict hinj]

/-- **Bochner line-integrability along a unit-speed curve.** For a unit-speed curve on `[a, b]`
injective on `(a, b)` and any `f : V → F`, `f` is `μHE[1]`-integrable on `γ '' Icc a b` if and only
if `t ↦ f (γ t)` is Lebesgue integrable on `Icc a b`. -/
theorem integrableOn_image_euclideanHausdorffMeasure_iff
    (hγ : HasUnitSpeedOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) (f : V → F) :
    IntegrableOn f (γ '' Icc a b) μHE[1] ↔ IntegrableOn (fun t => f (γ t)) (Icc a b) := by
  have he := ContinuousOn.measurableEmbedding measurableSet_Ioo
    (hγ.lipschitzOnWith.continuousOn.mono Ioo_subset_Icc_self) hinj
  have hc := MeasurableEmbedding.subtype_coe (measurableSet_Ioo (a := a) (b := b))
  rw [IntegrableOn, ← hγ.map_domRestrict_Ioo_eq_euclideanHausdorffMeasure_restrict hinj,
    he.integrable_map_iff]
  simp only [domRestrict_eq, ← Function.comp_assoc]
  rw [← hc.integrable_map_iff, map_comap_subtype_coe measurableSet_Ioo,
    Measure.restrict_congr_set Ioo_ae_eq_Icc]
  rfl

/-- **Bochner line-integral transport along a unit-speed curve.** For a unit-speed curve on `[a, b]`
injective on `(a, b)` and any `f : V → F`, the `μHE[1]`-integral of `f` over `γ '' Icc a b` equals
`∫ t in Icc a b, f (γ t)`. -/
theorem setIntegral_euclideanHausdorffMeasure_image_eq [NormedSpace ℝ F]
    (hγ : HasUnitSpeedOn γ (Icc a b)) (hinj : InjOn γ (Ioo a b)) (f : V → F) :
    ∫ y in γ '' Icc a b, f y ∂μHE[1] = ∫ t in Icc a b, f (γ t) := by
  have he := ContinuousOn.measurableEmbedding measurableSet_Ioo
    (hγ.lipschitzOnWith.continuousOn.mono Ioo_subset_Icc_self) hinj
  have hc := MeasurableEmbedding.subtype_coe (measurableSet_Ioo (a := a) (b := b))
  rw [← hγ.map_domRestrict_Ioo_eq_euclideanHausdorffMeasure_restrict hinj, he.integral_map]
  simp only [domRestrict_apply, ← Function.comp_apply (f := f)]
  rw [← hc.integral_map, map_comap_subtype_coe measurableSet_Ioo,
    integral_Icc_eq_integral_Ioo]

end HasUnitSpeedOn
