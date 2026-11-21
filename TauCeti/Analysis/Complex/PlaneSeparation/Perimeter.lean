/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Representation
public import TauCeti.Analysis.BoundedVariation.Space
public import TauCeti.Analysis.Green.Jordan
public import TauCeti.MeasureTheory.Function.AreaFormula.Curve
public import TauCeti.Topology.JordanCurve.Length
public import TauCeti.Topology.MetricSpace.Arclength.SimpleClosed
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Subtype

/-!
# Perimeter, variation measure, and outer normal of planar Jordan domains

Let `C ⊆ ℂ` be a rectifiable Jordan curve (`TauCeti.IsJordanCurve C`, `μHE[1] C ≠ ∞`), with bounded
inside `D = TauCeti.filledHull C \ C`. This file identifies the De Giorgi measure-theoretic boundary
invariants of `D` unconditionally and without orientation hypotheses:

* **Perimeter measure**: for every open set `Ω : Opens ℂ`,
  `variationMeasure volume Ω (D.indicator 1) = (μHE[1].restrict C).comap ((↑) : Ω → ℂ)`, and the
  same holds for `filledHull C` since `μHE[1] C ≠ ∞` forces `volume C = 0`.
* **Relative and global perimeter**: `perimeter volume U D = μHE[1] (C ∩ U)` for every
  `U : Opens ℂ`, and `perimeter volume ⊤ D = perimeter volume ⊤ (filledHull C) = μHE[1] C`. In
  particular `MemBV volume U (D.indicator 1)` holds on every open `U : Opens ℂ`.
* **Reduced boundary and outward unit normal**: `μHE[1]`-almost every point of `C` lies in
  `reducedBoundary volume ⊤ D`. Along any unit-speed simple closed parametrization `α` of `C` on
  `[a, b]`, for almost every `s ∈ [a, b]`,
  `outerNormal volume ⊤ D (α s) = -(Contour.jordanSign α a b : ℝ) • (I * deriv α s)`, so reversing
  orientation flips both `jordanSign` and `deriv α` while leaving `outerNormal` and the perimeter
  unchanged.
* **Gauss–Green formula on `D`**: for every open neighbourhood `W ⊇ filledHull C` and every `C¹`
  vector field `φ : ℂ → ℂ` on `W` (not necessarily compactly supported), both sides are integrable
  and `∫ z in D, tr(Dφ z) = ∫ z in C, ⟪φ z, outerNormal volume ⊤ D z⟫_ℝ ∂μHE[1]`.

Parametrized counterparts are also provided for unit-speed simple closed curves (`HasUnitSpeedOn`:
variation measure, relative and global perimeter including `ENNReal.ofReal (b - a)`, reduced
boundary concentration, and a.e. outward normal) and for continuous bounded-variation simple closed
curves (`BoundedVariationOn`: variation measure, relative perimeter, global perimeter equal to
`eVariationOn γ (Icc a b)`, `MemBV`, and a.e. outward normal along `naturalParameterization`).

## Main results

* `HasUnitSpeedOn.variationMeasure_filledHull_sdiff`,
  `HasUnitSpeedOn.perimeter_filledHull_sdiff`,
  `HasUnitSpeedOn.perimeter_filledHull_sdiff_eq_ofReal_sub`,
  `HasUnitSpeedOn.ae_mem_reducedBoundary_filledHull_sdiff`, and
  `HasUnitSpeedOn.ae_outerNormal_filledHull_sdiff`: perimeter measure, perimeter, reduced boundary,
  and a.e. outward normal `-(jordanSign α a b : ℝ) • (I * deriv α s)` along a unit-speed simple
  closed curve.
* `BoundedVariationOn.variationMeasure_filledHull_sdiff`,
  `BoundedVariationOn.perimeter_filledHull_sdiff`, `BoundedVariationOn.memBV_filledHull_sdiff`, and
  `BoundedVariationOn.ae_outerNormal_naturalParameterization`: perimeter measure, perimeter,
  `MemBV`, and a.e. outward normal for continuous rectifiable simple closed curves.
* `TauCeti.IsJordanCurve.variationMeasure_filledHull_sdiff`,
  `TauCeti.IsJordanCurve.perimeter_filledHull_sdiff`,
  `TauCeti.IsJordanCurve.ae_mem_reducedBoundary_filledHull_sdiff`,
  `TauCeti.IsJordanCurve.integrableOn_inner_outerNormal_filledHull_sdiff`, and
  `TauCeti.IsJordanCurve.setIntegral_filledHull_sdiff_trace_fderiv_eq`: intrinsic Jordan-curve
  theorems independent of parametrization.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Proposition 12.1 and Chapter 15.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Oxford University Press, 2000, §3.1 and §3.5.
* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §2.
-/

public section

noncomputable section

open Complex MeasureTheory TopologicalSpace TestFunction Set Filter
open scoped ENNReal NNReal Distributions RealInnerProductSpace

namespace TauCeti

/-- When `C ⊆ ℂ` has finite one-dimensional Hausdorff measure, `filledHull C` and `filledHull C \ C`
agree Lebesgue-almost everywhere because `volume C = 0`. -/
theorem filledHull_ae_eq_filledHull_sdiff {C : Set ℂ} (hfin : μHE[1] C ≠ ∞) :
    filledHull C =ᵐ[volume] filledHull C \ C :=
  (sdiff_null_ae_eq_self
    (volume_eq_zero_of_euclideanHausdorffMeasure_ne_top
      (by rw [Complex.finrank_real_complex]; exact one_lt_two) hfin)).symm

end TauCeti

namespace HasUnitSpeedOn

variable {α : ℝ → ℂ} {a b : ℝ}

/-- Candidate outward normal field on `ℂ` extended by `0` off `α '' Ico a b` from a unit-speed
simple closed curve `α`. -/
private def candidateNormal (α : ℝ → ℂ) (a b : ℝ) : ℂ → ℂ :=
  Function.extend ((Ico a b).domRestrict α)
    (fun s : Ico a b => -(TauCeti.Contour.jordanSign α a b : ℝ) • (I * deriv α s)) 0

/-- `candidateNormal α a b` is Borel measurable when `α` is unit-speed and injective on `[a, b)`. -/
private theorem measurable_candidateNormal (hα : HasUnitSpeedOn α (Icc a b))
    (hinj : InjOn α (Ico a b)) :
    Measurable (candidateNormal α a b) :=
  (ContinuousOn.measurableEmbedding measurableSet_Ico
    (hα.lipschitzOnWith.continuousOn.mono Ico_subset_Icc_self) hinj).measurable_extend
    (by fun_prop) measurable_const

/-- Along `Ico a b`, `candidateNormal α a b (α s)` recovers `-(jordanSign α a b : ℝ) • (I * α' s)`.
-/
private theorem candidateNormal_apply (hinj : InjOn α (Ico a b)) {s : ℝ} (hs : s ∈ Ico a b) :
    candidateNormal α a b (α s) = -(TauCeti.Contour.jordanSign α a b : ℝ) • (I * deriv α s) :=
  (injOn_iff_injective.1 hinj).extend_apply _ _ (⟨s, hs⟩ : Ico a b)

/-- `candidateNormal α a b` has unit norm `μHE[1]`-almost everywhere on `α '' Icc a b`. -/
private theorem ae_norm_candidateNormal_eq_one (hab : a < b) (hα : HasUnitSpeedOn α (Icc a b))
    (hclosed : α a = α b) (hinj : InjOn α (Ico a b)) :
    ∀ᵐ z ∂μHE[1].restrict (α '' Icc a b), ‖candidateNormal α a b z‖ = 1 := by
  have hαu : HasUnitSpeedOn α (uIcc a b) := by rwa [uIcc_of_le hab.le]
  have hnorm := hαu.ae_norm_deriv_eq
  rw [uIcc_of_le hab.le] at hnorm
  have hσ1 : |(TauCeti.Contour.jordanSign α a b : ℝ)| = 1 := by
    rcases hαu.lipschitzOnWith.absolutelyContinuousOnInterval.jordanSign_eq_one_or_neg_one
      hab hclosed hinj with h | h <;> simp [h]
  rw [← hα.map_restrict_Icc_eq_euclideanHausdorffMeasure_restrict
    (hinj.mono Ioo_subset_Ico_self)]
  refine (ae_map_iff (hα.lipschitzOnWith.continuousOn.aemeasurable measurableSet_Icc)
    (measurableSet_eq_fun (measurable_candidateNormal hα hinj).norm measurable_const)).2 ?_
  filter_upwards [hnorm, ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne b)] with s hs hsIcc hsb
  rw [candidateNormal_apply hinj ⟨hsIcc.1, hsIcc.2.lt_of_ne hsb⟩, norm_smul, norm_neg,
    Real.norm_eq_abs, hσ1, one_mul, norm_mul, norm_I, one_mul, hs.2, NNReal.coe_one]

/-- Distributional Gauss–Green identity on any open `Ω : Opens ℂ` for the bounded inside of a
unit-speed simple closed curve. -/
private theorem setIntegral_divergenceCLM_filledHull_sdiff_eq (hab : a < b)
    (hα : HasUnitSpeedOn α (Icc a b)) (hclosed : α a = α b) (hinj : InjOn α (Ico a b))
    (Ω : Opens ℂ) (φ : 𝓓(Ω, ℂ)) :
    ∫ z in TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b, divergenceCLM φ z =
      ∫ x : Ω, ⟪φ x, candidateNormal α a b x⟫
        ∂((μHE[1].restrict (α '' Icc a b)).comap ((↑) : Ω → ℂ)) := by
  set C := α '' Icc a b
  have hαu : HasUnitSpeedOn α (uIcc a b) := by rwa [uIcc_of_le hab.le]
  have hgreen := hαu.lipschitzOnWith.absolutelyContinuousOnInterval
    |>.setIntegral_filledHull_sdiff_trace_fderiv_eq hab hclosed hinj isOpen_univ (subset_univ _)
    (φ.contDiff.of_le (by simp)).contDiffOn
  rw [uIcc_of_le hab.le] at hgreen
  have hsupp : ∀ z ∉ (Ω : Set ℂ), ⟪(φ : ℂ → ℂ) z, candidateNormal α a b z⟫ = 0 := fun z hz => by
    have h0 : (φ : ℂ → ℂ) z = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hz (φ.tsupport_subset h)
    simp [h0]
  calc ∫ z in TauCeti.filledHull C \ C, divergenceCLM φ z
      = ∫ t in a..b,
          ⟪φ (α t), -(TauCeti.Contour.jordanSign α a b : ℝ) • (I * deriv α t)⟫ := by
        simp_rw [divergenceCLM_apply]
        exact hgreen
    _ = ∫ t in Icc a b, ⟪φ (α t), candidateNormal α a b (α t)⟫ := by
        rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
        refine setIntegral_congr_ae measurableSet_Icc ?_
        filter_upwards [volume.ae_ne b] with t htb ht
        rw [candidateNormal_apply hinj ⟨ht.1, ht.2.lt_of_ne htb⟩]
    _ = ∫ z in C, ⟪φ z, candidateNormal α a b z⟫ ∂μHE[1] :=
        (hα.setIntegral_euclideanHausdorffMeasure_image_eq (hinj.mono Ioo_subset_Ico_self)
          fun z => ⟪φ z, candidateNormal α a b z⟫).symm
    _ = ∫ z in (Ω : Set ℂ), ⟪φ z, candidateNormal α a b z⟫ ∂(μHE[1].restrict C) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μHE[1].restrict C) hsupp).symm
    _ = ∫ x : Ω, ⟪φ x, candidateNormal α a b x⟫ ∂((μHE[1].restrict C).comap ((↑) : Ω → ℂ)) :=
        (integral_subtype_comap Ω.isOpen.measurableSet _).symm

/-- `filledHull (α '' Icc a b) \ α '' Icc a b` is Borel measurable for a unit-speed curve `α`. -/
private theorem measurableSet_filledHull_sdiff (hα : HasUnitSpeedOn α (Icc a b)) :
    MeasurableSet (TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b) :=
  (isCompact_Icc.image_of_continuousOn hα.lipschitzOnWith.continuousOn).isClosed
    |>.isOpen_filledHull_sdiff.measurableSet

/-- **Perimeter measure of the inside of a unit-speed simple closed curve.** On every open set
`Ω : Opens ℂ`, the variation measure of the indicator of `filledHull C \ C` is the pullback to `Ω`
of `μHE[1]` restricted to `C = α '' Icc a b`. -/
theorem variationMeasure_filledHull_sdiff (hab : a < b) (hα : HasUnitSpeedOn α (Icc a b))
    (hclosed : α a = α b) (hinj : InjOn α (Ico a b)) (Ω : Opens ℂ) :
    TauCeti.variationMeasure volume Ω
        ((TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b).indicator 1) =
      (μHE[1].restrict (α '' Icc a b)).comap ((↑) : Ω → ℂ) := by
  have := hα.isFiniteMeasure_euclideanHausdorffMeasure_restrict
  exact TauCeti.variationMeasure_indicator_eq_of_forall_setIntegral_divergenceCLM_eq
    hα.measurableSet_filledHull_sdiff.nullMeasurableSet
    ((measurable_candidateNormal hα hinj).comp measurable_subtypeVal).aestronglyMeasurable
    ((ae_restrict_iff_subtype Ω.isOpen.measurableSet).1
      (ae_restrict_of_ae (ae_norm_candidateNormal_eq_one hab hα hclosed hinj)))
    (setIntegral_divergenceCLM_filledHull_sdiff_eq hab hα hclosed hinj Ω)

/-- **Relative perimeter of the inside of a unit-speed simple closed curve.** For every open set
`U : Opens ℂ`, the perimeter of `filledHull C \ C` in `U` equals `μHE[1] (C ∩ U)`. -/
theorem perimeter_filledHull_sdiff_opens (hab : a < b) (hα : HasUnitSpeedOn α (Icc a b))
    (hclosed : α a = α b) (hinj : InjOn α (Ico a b)) (U : Opens ℂ) :
    TauCeti.perimeter volume U (TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b) =
      μHE[1] (α '' Icc a b ∩ U) := by
  have := hα.isFiniteMeasure_euclideanHausdorffMeasure_restrict
  rw [TauCeti.perimeter_eq_of_forall_setIntegral_divergenceCLM_eq (Ω := ⊤)
    hα.measurableSet_filledHull_sdiff.nullMeasurableSet
    ((measurable_candidateNormal hα hinj).comp measurable_subtypeVal).aestronglyMeasurable
    ((ae_restrict_iff_subtype (⊤ : Opens ℂ).isOpen.measurableSet).1
      (ae_restrict_of_ae (ae_norm_candidateNormal_eq_one hab hα hclosed hinj)))
    (setIntegral_divergenceCLM_filledHull_sdiff_eq hab hα hclosed hinj ⊤) le_top]
  rw [comap_subtypeVal_apply (⊤ : Opens ℂ).isOpen.measurableSet]
  trans ((μHE[1].restrict (α '' Icc a b)) (U : Set ℂ))
  · congr 1; ext z; simp
  · rw [Measure.restrict_apply U.isOpen.measurableSet, inter_comm]

/-- **Perimeter of the inside of a unit-speed simple closed curve.** For a unit-speed simple closed
curve `α` on `[a, b]` (`a < b`), the global perimeter of `filledHull C \ C` equals `μHE[1] C`. -/
theorem perimeter_filledHull_sdiff (hab : a < b) (hα : HasUnitSpeedOn α (Icc a b))
    (hclosed : α a = α b) (hinj : InjOn α (Ico a b)) :
    TauCeti.perimeter volume ⊤ (TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b) =
      μHE[1] (α '' Icc a b) := by
  simpa using hα.perimeter_filledHull_sdiff_opens hab hclosed hinj ⊤

/-- **Perimeter of the inside of a unit-speed simple closed curve in terms of arclength.** For a
unit-speed simple closed curve `α` on `[a, b]` (`a < b`), the global perimeter of
`filledHull (α '' Icc a b) \ α '' Icc a b` is `ENNReal.ofReal (b - a)`. -/
theorem perimeter_filledHull_sdiff_eq_ofReal_sub (hab : a < b) (hα : HasUnitSpeedOn α (Icc a b))
    (hclosed : α a = α b) (hinj : InjOn α (Ico a b)) :
    TauCeti.perimeter volume ⊤ (TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b) =
      ENNReal.ofReal (b - a) := by
  rw [hα.perimeter_filledHull_sdiff hab hclosed hinj]
  have hmap := congr_arg (fun μ : Measure ℂ => μ univ)
    (hα.map_restrict_Icc_eq_euclideanHausdorffMeasure_restrict (hinj.mono Ioo_subset_Ico_self))
  simpa [Measure.map_apply_of_aemeasurable
    (hα.lipschitzOnWith.continuousOn.aemeasurable measurableSet_Icc) MeasurableSet.univ,
    Real.volume_Icc] using hmap.symm

/-- Almost every point of the trace of a unit-speed simple closed curve with respect to `μHE[1]`
belongs to the reduced boundary of `filledHull C \ C`, where `outerNormal` agrees with
`candidateNormal α a b`. -/
private theorem ae_mem_reducedBoundary_and_outerNormal_eq_candidateNormal (hab : a < b)
    (hα : HasUnitSpeedOn α (Icc a b)) (hclosed : α a = α b) (hinj : InjOn α (Ico a b)) :
    ∀ᵐ z ∂μHE[1].restrict (α '' Icc a b),
      z ∈ TauCeti.reducedBoundary volume ⊤ (TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b) ∧
        TauCeti.outerNormal volume ⊤ (TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b) z =
          candidateNormal α a b z := by
  have := hα.isFiniteMeasure_euclideanHausdorffMeasure_restrict
  have hc1 := (ae_restrict_iff_subtype (⊤ : Opens ℂ).isOpen.measurableSet).1
    (ae_restrict_of_ae (ae_norm_candidateNormal_eq_one hab hα hclosed hinj))
  have hdiv := setIntegral_divergenceCLM_filledHull_sdiff_eq hab hα hclosed hinj ⊤
  have hred := TauCeti.ae_mem_reducedBoundary_of_forall_setIntegral_divergenceCLM_eq (Ω := ⊤)
    hα.measurableSet_filledHull_sdiff.nullMeasurableSet
    ((measurable_candidateNormal hα hinj).comp measurable_subtypeVal).aestronglyMeasurable
    hc1 hdiv
  have hout := TauCeti.ae_outerNormal_eq_of_forall_setIntegral_divergenceCLM_eq (Ω := ⊤)
    hα.measurableSet_filledHull_sdiff.nullMeasurableSet
    ((measurable_candidateNormal hα hinj).comp measurable_subtypeVal).aestronglyMeasurable
    hc1 hdiv
  have hae' := (ae_restrict_iff_subtype (⊤ : Opens ℂ).isOpen.measurableSet (p := fun z =>
    z ∈ TauCeti.reducedBoundary volume ⊤ (TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b) ∧
      TauCeti.outerNormal volume ⊤ (TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b) z =
        candidateNormal α a b z)).2 (hred.and hout)
  simpa [Opens.coe_top, Measure.restrict_univ] using hae'

/-- **Reduced boundary concentration along a unit-speed simple closed curve.** Almost every
parameter `s ∈ [a, b]` maps into `reducedBoundary volume ⊤ (filledHull C \ C)`. -/
theorem ae_mem_reducedBoundary_filledHull_sdiff (hab : a < b)
    (hα : HasUnitSpeedOn α (Icc a b)) (hclosed : α a = α b) (hinj : InjOn α (Ico a b)) :
    ∀ᵐ s ∂volume.restrict (Icc a b),
      α s ∈
        TauCeti.reducedBoundary volume ⊤ (TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b) := by
  have haeC := (hα.ae_mem_reducedBoundary_and_outerNormal_eq_candidateNormal hab hclosed hinj).mono
    fun _ h => h.1
  rw [← hα.map_restrict_Icc_eq_euclideanHausdorffMeasure_restrict
    (hinj.mono Ioo_subset_Ico_self)] at haeC
  exact ae_of_ae_map (hα.lipschitzOnWith.continuousOn.aemeasurable measurableSet_Icc) haeC

/-- **Outer normal along a unit-speed simple closed curve.** Almost everywhere on `[a, b]`, the
measure-theoretic outer normal to `filledHull C \ C` at `α s` is
`-(Contour.jordanSign α a b : ℝ) • (I * deriv α s)`. -/
theorem ae_outerNormal_filledHull_sdiff (hab : a < b) (hα : HasUnitSpeedOn α (Icc a b))
    (hclosed : α a = α b) (hinj : InjOn α (Ico a b)) :
    ∀ᵐ s ∂volume.restrict (Icc a b),
      TauCeti.outerNormal volume ⊤ (TauCeti.filledHull (α '' Icc a b) \ α '' Icc a b) (α s) =
        -(TauCeti.Contour.jordanSign α a b : ℝ) • (I * deriv α s) := by
  have haeC := (hα.ae_mem_reducedBoundary_and_outerNormal_eq_candidateNormal hab hclosed hinj).mono
    fun _ h => h.2
  rw [← hα.map_restrict_Icc_eq_euclideanHausdorffMeasure_restrict
    (hinj.mono Ioo_subset_Ico_self)] at haeC
  have haem : AEMeasurable α (volume.restrict (Icc a b)) :=
    hα.lipschitzOnWith.continuousOn.aemeasurable measurableSet_Icc
  filter_upwards [ae_of_ae_map haem haeC, ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne b)] with s hs hsIcc hsb
  exact hs.trans (candidateNormal_apply hinj ⟨hsIcc.1, hsIcc.2.lt_of_ne hsb⟩)

end HasUnitSpeedOn

namespace BoundedVariationOn

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- **Perimeter measure of the inside of a rectifiable simple closed curve.** For a continuous
simple closed curve of bounded variation on `[a, b]` (`a < b`), the variation measure on any open
`Ω : Opens ℂ` of the indicator of `filledHull C \ C` is the pullback of `μHE[1]` restricted to
`C = γ '' Icc a b`. -/
theorem variationMeasure_filledHull_sdiff (hab : a < b) (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (Ω : Opens ℂ) :
    TauCeti.variationMeasure volume Ω
        ((TauCeti.filledHull (γ '' Icc a b) \ γ '' Icc a b).indicator 1) =
      (μHE[1].restrict (γ '' Icc a b)).comap ((↑) : Ω → ℂ) := by
  have hL : 0 < (eVariationOn γ (Icc a b)).toReal :=
    hγ.toReal_eVariationOn_pos_of_injOn_Ioo hab (hinj.mono Ioo_subset_Ico_self)
  rw [← hγ.image_naturalParameterization_Icc hcont hab.le]
  exact (hγ.hasUnitSpeedOn_naturalParameterization hcont hab.le)
    |>.variationMeasure_filledHull_sdiff hL
    (hγ.naturalParameterization_zero_eq_naturalParameterization_toReal_eVariationOn hab.le hclosed)
    (hγ.injOn_naturalParameterization_Ico hcont hinj hab.le) Ω

/-- **Relative perimeter of the inside of a rectifiable simple closed curve.** For every open set
`U : Opens ℂ`, the perimeter of `filledHull C \ C` in `U` equals `μHE[1] (C ∩ U)`. -/
theorem perimeter_filledHull_sdiff_opens (hab : a < b) (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (U : Opens ℂ) :
    TauCeti.perimeter volume U (TauCeti.filledHull (γ '' Icc a b) \ γ '' Icc a b) =
      μHE[1] (γ '' Icc a b ∩ U) := by
  have hL : 0 < (eVariationOn γ (Icc a b)).toReal :=
    hγ.toReal_eVariationOn_pos_of_injOn_Ioo hab (hinj.mono Ioo_subset_Ico_self)
  rw [← hγ.image_naturalParameterization_Icc hcont hab.le]
  exact (hγ.hasUnitSpeedOn_naturalParameterization hcont hab.le)
    |>.perimeter_filledHull_sdiff_opens hL
    (hγ.naturalParameterization_zero_eq_naturalParameterization_toReal_eVariationOn hab.le hclosed)
    (hγ.injOn_naturalParameterization_Ico hcont hinj hab.le) U

/-- **Perimeter of the inside of a rectifiable simple closed curve.** For a continuous simple closed
curve `γ` of bounded variation on `[a, b]` (`a < b`), the global perimeter of
`filledHull (γ '' Icc a b) \ γ '' Icc a b` equals the total variation `eVariationOn γ (Icc a b)`. -/
theorem perimeter_filledHull_sdiff (hab : a < b) (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    TauCeti.perimeter volume ⊤ (TauCeti.filledHull (γ '' Icc a b) \ γ '' Icc a b) =
      eVariationOn γ (Icc a b) := by
  rw [hγ.perimeter_filledHull_sdiff_opens hab hcont hclosed hinj ⊤, Opens.coe_top, inter_univ,
    ← hcont.eVariationOn_eq_euclideanHausdorffMeasure_image (hinj.mono Ioo_subset_Ico_self)]

/-- **BV membership for the inside of a rectifiable simple closed curve.** The indicator of
`filledHull (γ '' Icc a b) \ γ '' Icc a b` belongs to `MemBV volume U` on every open `U : Opens ℂ`.
-/
theorem memBV_filledHull_sdiff (hab : a < b) (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (U : Opens ℂ) :
    TauCeti.MemBV volume U
      ((TauCeti.filledHull (γ '' Icc a b) \ γ '' Icc a b).indicator 1) := by
  set C := γ '' Icc a b
  have hK : IsCompact C := isCompact_Icc.image_of_continuousOn hcont
  have hD : MeasurableSet (TauCeti.filledHull C \ C) :=
    hK.isClosed.isOpen_filledHull_sdiff.measurableSet
  have hvol : volume (TauCeti.filledHull C \ C) < ∞ :=
    ((TauCeti.isBounded_filledHull.2 hK.isBounded).subset sdiff_subset).measure_lt_top
  have hint : Integrable ((TauCeti.filledHull C \ C).indicator (1 : ℂ → ℝ)) volume :=
    (integrable_indicator_iff hD).2 (integrableOn_const (C := (1 : ℝ)) (hs := hvol.ne))
  refine TauCeti.memBV_iff.2 ⟨hint.integrableOn, ?_⟩
  rw [← TauCeti.perimeter_def]
  exact ((TauCeti.perimeter_mono (Ω := ⊤) le_top).trans_eq
    (hγ.perimeter_filledHull_sdiff hab hcont hclosed hinj)).trans_lt hγ.lt_top

/-- **Outer normal along the arclength parametrization of a rectifiable simple closed curve.** Let
`α = naturalParameterization γ (Icc a b) a` and `L = (eVariationOn γ (Icc a b)).toReal`. Almost
everywhere on `[0, L]`, the measure-theoretic outer normal to `filledHull (γ '' Icc a b) \ C` at
`α s` is `-(Contour.jordanSign α 0 L : ℝ) • (I * deriv α s)`. -/
theorem ae_outerNormal_naturalParameterization (hab : a < b) (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    ∀ᵐ s ∂volume.restrict (Icc 0 (eVariationOn γ (Icc a b)).toReal),
      TauCeti.outerNormal volume ⊤ (TauCeti.filledHull (γ '' Icc a b) \ γ '' Icc a b)
        (naturalParameterization γ (Icc a b) a s) =
        -(TauCeti.Contour.jordanSign (naturalParameterization γ (Icc a b) a) 0
            (eVariationOn γ (Icc a b)).toReal : ℝ) •
          (I * deriv (naturalParameterization γ (Icc a b) a) s) := by
  have hL : 0 < (eVariationOn γ (Icc a b)).toReal :=
    hγ.toReal_eVariationOn_pos_of_injOn_Ioo hab (hinj.mono Ioo_subset_Ico_self)
  rw [← hγ.image_naturalParameterization_Icc hcont hab.le]
  exact (hγ.hasUnitSpeedOn_naturalParameterization hcont hab.le).ae_outerNormal_filledHull_sdiff
    hL (hγ.naturalParameterization_zero_eq_naturalParameterization_toReal_eVariationOn hab.le
      hclosed) (hγ.injOn_naturalParameterization_Ico hcont hinj hab.le)

end BoundedVariationOn

namespace TauCeti

section JordanCurve

variable {C : Set ℂ}

/-- **Perimeter measure of the bounded inside of a rectifiable Jordan curve.** For every open set
`Ω : Opens ℂ`, the variation measure of the indicator of `filledHull C \ C` is the pullback to `Ω`
of `μHE[1]` restricted to `C`. -/
theorem IsJordanCurve.variationMeasure_filledHull_sdiff (hC : IsJordanCurve C)
    (hfin : μHE[1] C ≠ ∞) (Ω : Opens ℂ) :
    variationMeasure volume Ω ((filledHull C \ C).indicator 1) =
      (μHE[1].restrict C).comap ((↑) : Ω → ℂ) := by
  obtain ⟨L, α, hL, hα, hclosed, hinj, rfl⟩ :=
    hC.exists_unitSpeed_simpleClosed (Measure.euclideanHausdorffMeasure_one (X := ℂ) ▸ hfin.lt_top)
  exact hα.variationMeasure_filledHull_sdiff hL hclosed hinj Ω

/-- **Perimeter measure of `filledHull C` for a rectifiable Jordan curve.** Because `volume C = 0`,
`filledHull C` has the same variation measure as `filledHull C \ C` on every open `Ω : Opens ℂ`. -/
theorem IsJordanCurve.variationMeasure_filledHull (hC : IsJordanCurve C)
    (hfin : μHE[1] C ≠ ∞) (Ω : Opens ℂ) :
    variationMeasure volume Ω ((filledHull C).indicator 1) =
      (μHE[1].restrict C).comap ((↑) : Ω → ℂ) := by
  rw [variationMeasure_congr_ae
    (indicator_ae_eq_of_ae_eq_set (ae_restrict_of_ae (filledHull_ae_eq_filledHull_sdiff hfin)))]
  exact hC.variationMeasure_filledHull_sdiff hfin Ω

/-- **Relative perimeter of the bounded inside of a rectifiable Jordan curve.** For every open set
`U : Opens ℂ`, the perimeter of `filledHull C \ C` in `U` equals `μHE[1] (C ∩ U)`. -/
theorem IsJordanCurve.perimeter_filledHull_sdiff_opens (hC : IsJordanCurve C)
    (hfin : μHE[1] C ≠ ∞) (U : Opens ℂ) :
    perimeter volume U (filledHull C \ C) = μHE[1] (C ∩ U) := by
  obtain ⟨L, α, hL, hα, hclosed, hinj, rfl⟩ :=
    hC.exists_unitSpeed_simpleClosed (Measure.euclideanHausdorffMeasure_one (X := ℂ) ▸ hfin.lt_top)
  exact hα.perimeter_filledHull_sdiff_opens hL hclosed hinj U

/-- **Perimeter of the bounded inside of a rectifiable Jordan curve.** For every rectifiable Jordan
curve `C ⊆ ℂ`, the De Giorgi perimeter of `filledHull C \ C` in `ℂ` equals `μHE[1] C`. -/
theorem IsJordanCurve.perimeter_filledHull_sdiff (hC : IsJordanCurve C) (hfin : μHE[1] C ≠ ∞) :
    perimeter volume ⊤ (filledHull C \ C) = μHE[1] C := by
  simpa using hC.perimeter_filledHull_sdiff_opens hfin ⊤

/-- **Perimeter of `filledHull C` for a rectifiable Jordan curve.** Because `volume C = 0`, the
perimeter of `filledHull C` in `ℂ` also equals `μHE[1] C`. -/
theorem IsJordanCurve.perimeter_filledHull (hC : IsJordanCurve C) (hfin : μHE[1] C ≠ ∞) :
    perimeter volume ⊤ (filledHull C) = μHE[1] C := by
  rw [perimeter_congr_ae (ae_restrict_of_ae (filledHull_ae_eq_filledHull_sdiff hfin))]
  exact hC.perimeter_filledHull_sdiff hfin

/-- **Finite perimeter and BV membership for a rectifiable Jordan domain.** For every rectifiable
Jordan curve `C ⊆ ℂ` and every open `U : Opens ℂ`, the indicator of `filledHull C \ C` belongs to
`MemBV volume U`. -/
theorem IsJordanCurve.memBV_filledHull_sdiff (hC : IsJordanCurve C) (hfin : μHE[1] C ≠ ∞)
    (U : Opens ℂ) :
    MemBV volume U ((filledHull C \ C).indicator 1) := by
  obtain ⟨γ, hcont, hclosed, hinj, hγ, rfl⟩ :=
    (isJordanCurve_and_hausdorffMeasure_lt_top_iff zero_lt_one).1
      ⟨hC, Measure.euclideanHausdorffMeasure_one (X := ℂ) ▸ hfin.lt_top⟩
  exact hγ.memBV_filledHull_sdiff zero_lt_one hcont hclosed hinj U

/-- **Reduced boundary concentration on a rectifiable Jordan curve.** `μHE[1]`-almost every point of
`C` belongs to `reducedBoundary volume ⊤ (filledHull C \ C)`. -/
theorem IsJordanCurve.ae_mem_reducedBoundary_filledHull_sdiff (hC : IsJordanCurve C)
    (hfin : μHE[1] C ≠ ∞) :
    ∀ᵐ z ∂μHE[1].restrict C, z ∈ reducedBoundary volume ⊤ (filledHull C \ C) := by
  obtain ⟨L, α, hL, hα, hclosed, hinj, rfl⟩ :=
    hC.exists_unitSpeed_simpleClosed (Measure.euclideanHausdorffMeasure_one (X := ℂ) ▸ hfin.lt_top)
  exact (hα.ae_mem_reducedBoundary_and_outerNormal_eq_candidateNormal hL hclosed hinj).mono
    fun _ h => h.1

/-- The divergence `tr(Dφ)` of a `C¹` vector field on an open neighbourhood of `filledHull C` is
integrable on `filledHull C \ C` for every rectifiable Jordan curve `C`. -/
theorem IsJordanCurve.integrableOn_filledHull_sdiff_trace_fderiv (hC : IsJordanCurve C)
    (hfin : μHE[1] C ≠ ∞) {W : Set ℂ} {φ : ℂ → ℂ} (hW : IsOpen W)
    (hregion : filledHull C ⊆ W) (hφ : ContDiffOn ℝ 1 φ W) :
    IntegrableOn (fun z => LinearMap.trace ℝ ℂ (fderiv ℝ φ z).toLinearMap) (filledHull C \ C) := by
  obtain ⟨L, α, hL, hα, hclosed, hinj, rfl⟩ :=
    hC.exists_unitSpeed_simpleClosed (Measure.euclideanHausdorffMeasure_one (X := ℂ) ▸ hfin.lt_top)
  have hαu : HasUnitSpeedOn α (uIcc 0 L) := by rwa [uIcc_of_le hL.le]
  have hint := hαu.lipschitzOnWith.absolutelyContinuousOnInterval
    |>.integrableOn_filledHull_sdiff_trace_fderiv hL hclosed hinj hW
    (by simpa [uIcc_of_le hL.le] using hregion) hφ
  rwa [uIcc_of_le hL.le] at hint

/-- For a rectifiable Jordan curve `C` and a `C¹` vector field `φ` on an open neighbourhood of
`filledHull C`, the normal flux `⟪φ, outerNormal volume ⊤ (filledHull C \ C)⟫` is
`μHE[1]`-integrable on `C`. -/
theorem IsJordanCurve.integrableOn_inner_outerNormal_filledHull_sdiff (hC : IsJordanCurve C)
    (hfin : μHE[1] C ≠ ∞) {W : Set ℂ} {φ : ℂ → ℂ} (hW : IsOpen W)
    (hregion : filledHull C ⊆ W) (hφ : ContDiffOn ℝ 1 φ W) :
    IntegrableOn (fun z => ⟪φ z, outerNormal volume ⊤ (filledHull C \ C) z⟫) C μHE[1] := by
  obtain ⟨L, α, hL, hα, hclosed, hinj, rfl⟩ :=
    hC.exists_unitSpeed_simpleClosed (Measure.euclideanHausdorffMeasure_one (X := ℂ) ▸ hfin.lt_top)
  have hαu : HasUnitSpeedOn α (uIcc 0 L) := by rwa [uIcc_of_le hL.le]
  have hintIoc := (intervalIntegrable_iff_integrableOn_Icc_of_le hL.le).1
    (hαu.lipschitzOnWith.absolutelyContinuousOnInterval
      |>.intervalIntegrable_inner_jordanSign_smul_I_mul_deriv hL hclosed hinj hW
      (by simpa [uIcc_of_le hL.le] using hregion) hφ)
  rw [hα.integrableOn_image_euclideanHausdorffMeasure_iff (hinj.mono Ioo_subset_Ico_self)]
  refine hintIoc.congr ?_
  filter_upwards [hα.ae_outerNormal_filledHull_sdiff hL hclosed hinj] with s hs
  rw [hs]

/-- **Gauss–Green theorem for a rectifiable Jordan domain.** For every rectifiable Jordan curve
`C ⊆ ℂ`, every open neighbourhood `W` of `filledHull C`, and every `C¹` vector field `φ : ℂ → ℂ` on
`W`, `∫_{filledHull C \ C} tr(Dφ) = ∫_C ⟪φ, outerNormal volume ⊤ (filledHull C \ C)⟫ ∂μHE[1]`. -/
theorem IsJordanCurve.setIntegral_filledHull_sdiff_trace_fderiv_eq (hC : IsJordanCurve C)
    (hfin : μHE[1] C ≠ ∞) {W : Set ℂ} {φ : ℂ → ℂ} (hW : IsOpen W)
    (hregion : filledHull C ⊆ W) (hφ : ContDiffOn ℝ 1 φ W) :
    (∫ z in filledHull C \ C, LinearMap.trace ℝ ℂ (fderiv ℝ φ z).toLinearMap) =
      ∫ z in C, ⟪φ z, outerNormal volume ⊤ (filledHull C \ C) z⟫ ∂μHE[1] := by
  obtain ⟨L, α, hL, hα, hclosed, hinj, rfl⟩ :=
    hC.exists_unitSpeed_simpleClosed (Measure.euclideanHausdorffMeasure_one (X := ℂ) ▸ hfin.lt_top)
  have hαu : HasUnitSpeedOn α (uIcc 0 L) := by rwa [uIcc_of_le hL.le]
  have hgreen := hαu.lipschitzOnWith.absolutelyContinuousOnInterval
    |>.setIntegral_filledHull_sdiff_trace_fderiv_eq hL hclosed hinj hW
    (by simpa [uIcc_of_le hL.le] using hregion) hφ
  rw [uIcc_of_le hL.le] at hgreen
  rw [hgreen, intervalIntegral.integral_of_le hL.le, ← integral_Icc_eq_integral_Ioc,
    hα.setIntegral_euclideanHausdorffMeasure_image_eq (hinj.mono Ioo_subset_Ico_self)]
  refine setIntegral_congr_ae measurableSet_Icc ?_
  filter_upwards [ae_imp_of_ae_restrict (hα.ae_outerNormal_filledHull_sdiff hL hclosed hinj)]
    with s hs hsIcc
  rw [hs hsIcc]

end JordanCurve

end TauCeti
