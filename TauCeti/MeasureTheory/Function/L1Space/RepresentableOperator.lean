/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.VectorMeasure.AddContent
import Mathlib.MeasureTheory.Integral.SetToL1.ChangeMeasure
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.VectorMeasure.Operations

/-!
# Operators on scalar `L¹` and dominated vector measures

Let `μ` be a finite measure and `X` a Banach space. A bounded operator `T : L¹(μ) → X` on scalar
`L¹` defines the vector measure `m_T(s) = T 𝟙_s`, whose variation satisfies `|m_T| ≤ ‖T‖ μ`.
Conversely, a vector measure `m` with `|m| ≤ C μ` integrates scalar `L¹(μ)` functions,
`φ ↦ ∫ φ dm`, with operator norm at most `C`; this needs no finiteness of `μ`. The two
constructions are mutually inverse, so on a finite measure space bounded operators `L¹(μ) → X` are
the same as `X`-valued vector measures dominated by a multiple of `μ`, and `‖T‖` is the least
such multiple.

An essentially bounded density `g ∈ L∞(μ; X)` represents the operator `φ ↦ ∫ φ • g`. Its vector
measure is the vector measure `μ.withDensityᵥ g` with density `g`, so the densities of `m_T` in
`L∞(μ; X)` are exactly the representing densities of `T`. Moreover every integrable density of
`m_T` is essentially bounded by `‖T‖`. These facts reduce the representability of operators on
`L¹` to the existence of densities of vector measures, which is the Radon–Nikodým property of `X`.

## Main declarations

* `ContinuousLinearMap.toVectorMeasure`: the vector measure `s ↦ T 𝟙_s` of a bounded operator
  `T : L¹(μ) → X`, for a finite measure `μ`.
* `ContinuousLinearMap.variation_toVectorMeasure_le`: `|m_T| ≤ ‖T‖ μ`.
* `ContinuousLinearMap.toVectorMeasure_injective`: an operator is determined by its vector measure.
* `MeasureTheory.VectorMeasure.integralL1CLM`: for `|m| ≤ C μ`, the operator `φ ↦ ∫ φ dm` on
  scalar `L¹(μ)`, of norm at most `C` (`MeasureTheory.VectorMeasure.norm_integralL1CLM_le`). By
  `MeasureTheory.VectorMeasure.integralL1CLM_apply` it is Mathlib's integral against `m`.
* `MeasureTheory.VectorMeasure.toVectorMeasure_integralL1CLM` and
  `ContinuousLinearMap.integralL1CLM_toVectorMeasure`: the two constructions are inverse.
* `ContinuousLinearMap.opNNNorm_le_iff_variation_toVectorMeasure_le`: `‖T‖ ≤ C` if and only if
  `|m_T| ≤ C μ`.
* `MeasureTheory.Lp.representableOperatorMap`: the operator `φ ↦ ∫ φ • g` on scalar `L¹(μ)`
  represented by `g ∈ L∞(μ; X)`.
* `MeasureTheory.Lp.representableOperatorMap_eq_iff`: `g` represents `T` if and only if `g` is a
  density of `m_T`.
* `ContinuousLinearMap.exists_representableOperatorMap_eq_of_toVectorMeasure_eq_withDensityᵥ`: an
  integrable density of `m_T` is essentially bounded and represents `T`.

## References

* J. Diestel and J. J. Uhl, Jr., *Vector Measures*, Mathematical Surveys 15, AMS, 1977,
  Chapter III, §1.
* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I, Springer,
  2016, §1.3.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

variable {𝕜 S X : Type*} [MeasurableSpace S] {μ : Measure S} [NormedAddCommGroup X]

namespace ContinuousLinearMap

section ToVectorMeasure

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 X] [IsFiniteMeasure μ] (T : Lp 𝕜 1 μ →L[𝕜] X)

omit [IsFiniteMeasure μ] in
/-- The bound `‖T 𝟙_s‖ ≤ ‖T‖ μ(s)` for an operator on scalar `L¹`. -/
private theorem eNorm_apply_indicatorConstLp_one_le {s : Set S} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) : ‖T (indicatorConstLp 1 hs hμs (1 : 𝕜))‖ₑ ≤ (‖T‖₊ • μ) s := by
  calc ‖T (indicatorConstLp 1 hs hμs (1 : 𝕜))‖ₑ
      ≤ ‖T‖ₑ * ‖indicatorConstLp 1 hs hμs (1 : 𝕜)‖ₑ := T.le_opENorm _
    _ ≤ ‖T‖ₑ * μ s := by
      gcongr
      simpa using eNorm_indicatorConstLp_le (p := 1) (hs := hs) (hμs := hμs) (c := (1 : 𝕜))
    _ = (‖T‖₊ • μ) s := by
      rw [smul_apply, ENNReal.smul_def, smul_eq_mul, eNorm_eq_nnNorm]

open Classical in
/-- The vector measure `s ↦ T 𝟙_s` of a bounded operator `T` on scalar `L¹` of a finite measure.
It is countably additive because it is dominated by the finite measure `‖T‖ μ`. -/
def toVectorMeasure : VectorMeasure S X :=
  VectorMeasure.of_additive_of_le_measure (μ := ‖T‖₊ • μ)
    (fun s ↦ if hs : MeasurableSet s then T (indicatorConstLp 1 hs (measure_ne_top μ s) 1) else 0)
    (fun s ↦ by
      split_ifs with hs
      · exact eNorm_apply_indicatorConstLp_one_le T hs _
      · simp)
    (fun s t hs ht hst ↦ by
      simp only [hs, ht, hs.union ht, dite_true]
      rw [indicatorConstLp_disjoint_union hs ht (measure_ne_top μ s) (measure_ne_top μ t) hst,
        map_add])
    (fun _ hs ↦ by simp [hs])

/-- The vector measure of `T` evaluates `T` on the indicator class of a measurable set. -/
@[simp]
theorem toVectorMeasure_apply {s : Set S} (hs : MeasurableSet s) :
    T.toVectorMeasure s = T (indicatorConstLp 1 hs (measure_ne_top μ s) 1) := by
  -- Mathlib has no evaluation lemma for `of_additive_of_le_measure`, whose values are those of
  -- the given set function, so we unfold it.
  simp [toVectorMeasure, VectorMeasure.of_additive_of_le_measure, hs]

/-- An operator on scalar `L¹` sends the indicator class `c 𝟙_s` to `c` times the value of its
vector measure at `s`. -/
theorem apply_indicatorConstLp_eq_smul_toVectorMeasure {s : Set S} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) :
    T (indicatorConstLp 1 hs hμs c) = c • T.toVectorMeasure s := by
  rw [toVectorMeasure_apply, ← map_smul, ← TauCeti.indicatorConstLp_smul, smul_eq_mul, mul_one]

/-- The variation of the vector measure of `T` is at most `‖T‖ μ`. -/
theorem variation_toVectorMeasure_le : T.toVectorMeasure.variation ≤ ‖T‖₊ • μ :=
  VectorMeasure.variation_le_of_forall_eNorm_le fun s hs ↦ by
    rw [toVectorMeasure_apply T hs]
    exact eNorm_apply_indicatorConstLp_one_le T hs _

instance isFiniteMeasure_variation_toVectorMeasure :
    IsFiniteMeasure T.toVectorMeasure.variation :=
  isFiniteMeasure_of_le _ T.variation_toVectorMeasure_le

/-- The variation of the vector measure of `T` is absolutely continuous with respect to `μ`. -/
theorem variation_toVectorMeasure_absolutelyContinuous : T.toVectorMeasure.variation ≪ μ :=
  Measure.absolutelyContinuous_of_le_smul (by
    simpa only [ENNReal.smul_def] using T.variation_toVectorMeasure_le)

/-- An operator on scalar `L¹` of a finite measure is determined by its vector measure. -/
theorem toVectorMeasure_injective :
    Function.Injective (toVectorMeasure : (Lp 𝕜 1 μ →L[𝕜] X) → VectorMeasure S X) := by
  intro T T' h
  refine ext_indicatorConstLp ENNReal.one_ne_top fun s hs hμs c ↦ ?_
  rw [apply_indicatorConstLp_eq_smul_toVectorMeasure,
    apply_indicatorConstLp_eq_smul_toVectorMeasure, h]

/-- The vector measure of `T` determines `T`. -/
theorem toVectorMeasure_inj {T' : Lp 𝕜 1 μ →L[𝕜] X} :
    T.toVectorMeasure = T'.toVectorMeasure ↔ T = T' :=
  toVectorMeasure_injective.eq_iff

/-- Composing with a bounded operator `L` on the target applies `L` to the vector measure. -/
theorem toVectorMeasure_comp {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] (L : X →L[𝕜] Y) :
    (L ∘L T).toVectorMeasure = VectorMeasure.mapRangeL L T.toVectorMeasure := by
  ext s hs
  rw [toVectorMeasure_apply _ hs, VectorMeasure.mapRangeL_apply,
    toVectorMeasure_apply _ hs, comp_apply]

end ToVectorMeasure

end ContinuousLinearMap

variable [RCLike 𝕜] [NormedSpace 𝕜 X]

namespace MeasureTheory.VectorMeasure

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] (m : VectorMeasure S X) {C : ℝ≥0}

/-- If `|m| ≤ C μ`, the set function `s ↦ (c ↦ c • m s)` is dominated by `C μ`. -/
private theorem dominatedFinMeasAdditive_transpose_lsmul (hm : m.variation ≤ C • μ) :
    DominatedFinMeasAdditive μ (m.transpose (ContinuousLinearMap.lsmul ℝ 𝕜))
      (C * ‖(ContinuousLinearMap.lsmul ℝ 𝕜 : 𝕜 →L[ℝ] X →L[ℝ] X)‖) := by
  simpa using (dominatedFinMeasAdditive_cbmApplyMeasure m
    (ContinuousLinearMap.lsmul ℝ 𝕜)).of_measure_le_smul ENNReal.coe_ne_top
      (by simpa only [ENNReal.smul_def] using hm) (by positivity)

@[simp]
private theorem transpose_lsmul_apply (s : Set S) (c : 𝕜) :
    m.transpose (ContinuousLinearMap.lsmul ℝ 𝕜) s c = c • m s := by
  rw [transpose_eq_cbmApplyMeasure, cbmApplyMeasure_apply, ContinuousLinearMap.lsmul_apply]

variable [CompleteSpace X]

variable (𝕜) in
/-- The bounded operator `φ ↦ ∫ φ dm` on scalar `L¹(μ)` defined by a vector measure `m` with
`|m| ≤ C μ`. It is the extension to `L¹(μ)` of `c 𝟙_s ↦ c • m s`; its values do not depend on the
bound `C` (`MeasureTheory.VectorMeasure.integralL1CLM_apply`). -/
def integralL1CLM (hm : m.variation ≤ C • μ) : Lp 𝕜 1 μ →L[𝕜] X :=
  L1.setToL1' 𝕜 (m.dominatedFinMeasAdditive_transpose_lsmul hm) fun c s x ↦ by
    simp only [transpose_lsmul_apply, smul_eq_mul, mul_smul]

variable {m}

/-- The operator `integralL1CLM` sends `c 𝟙_s` to `c • m s`. -/
@[simp]
theorem integralL1CLM_indicatorConstLp (hm : m.variation ≤ C • μ) {s : Set S}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : 𝕜) :
    m.integralL1CLM 𝕜 hm (indicatorConstLp 1 hs hμs c) = c • m s := by
  rw [integralL1CLM, ← L1.setToL1_eq_setToL1', L1.setToL1_indicatorConstLp,
    transpose_lsmul_apply]

/-- The operator `integralL1CLM` is the integral against the vector measure `m`. -/
theorem integralL1CLM_apply (hm : m.variation ≤ C • μ) (φ : Lp 𝕜 1 μ) :
    m.integralL1CLM 𝕜 hm φ = ∫ᵛ x, φ x ∂[ContinuousLinearMap.lsmul ℝ 𝕜; m] := by
  rw [integralL1CLM, ← L1.setToL1_eq_setToL1', ← L1.setToFun_eq_setToL1,
    integral_eq_setToFun]
  exact setToFun_congr_measure_of_integrable C ENNReal.coe_ne_top
    (by simpa only [ENNReal.smul_def] using hm) _ _ _ (L1.integrable_coeFn φ)

/-- The operator `integralL1CLM` has norm at most `C`. -/
theorem norm_integralL1CLM_le (hm : m.variation ≤ C • μ) : ‖m.integralL1CLM 𝕜 hm‖ ≤ C := by
  have hB : ‖(ContinuousLinearMap.lsmul ℝ 𝕜 : 𝕜 →L[ℝ] X →L[ℝ] X)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_lsmul_le
  refine ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg fun φ ↦ ?_
  rw [integralL1CLM, ← L1.setToL1_eq_setToL1']
  refine (L1.norm_setToL1_le_mul_norm _ (by positivity) φ).trans ?_
  gcongr
  exact mul_le_of_le_one_right C.coe_nonneg hB

/-- On a finite measure space, the vector measure of `integralL1CLM` is `m`. -/
@[simp]
theorem toVectorMeasure_integralL1CLM [IsFiniteMeasure μ] (hm : m.variation ≤ C • μ) :
    (m.integralL1CLM 𝕜 hm).toVectorMeasure = m := by
  ext s hs
  rw [ContinuousLinearMap.toVectorMeasure_apply _ hs, integralL1CLM_indicatorConstLp, one_smul]

end MeasureTheory.VectorMeasure

namespace ContinuousLinearMap

variable [IsFiniteMeasure μ] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]
  (T : Lp 𝕜 1 μ →L[𝕜] X)

/-- On a finite measure space, integrating against the vector measure of `T` recovers `T`. -/
@[simp]
theorem integralL1CLM_toVectorMeasure :
    T.toVectorMeasure.integralL1CLM 𝕜 T.variation_toVectorMeasure_le = T :=
  toVectorMeasure_injective (VectorMeasure.toVectorMeasure_integralL1CLM _)

/-- The operator norm of `T` is at most `C` if and only if the variation of its vector measure is
at most `C μ`. -/
theorem opNNNorm_le_iff_variation_toVectorMeasure_le {C : ℝ≥0} :
    ‖T‖₊ ≤ C ↔ T.toVectorMeasure.variation ≤ C • μ := by
  refine ⟨fun h ↦ T.variation_toVectorMeasure_le.trans fun s ↦ ?_, fun h ↦ ?_⟩
  · simp only [smul_apply, ENNReal.smul_def, smul_eq_mul]
    gcongr
  · have hT : T.toVectorMeasure.integralL1CLM 𝕜 h = T :=
      toVectorMeasure_injective (VectorMeasure.toVectorMeasure_integralL1CLM h)
    rw [← NNReal.coe_le_coe, coe_nnNorm, ← hT]
    exact VectorMeasure.norm_integralL1CLM_le h

end ContinuousLinearMap

namespace MeasureTheory.Lp

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]

variable (𝕜) in
/-- The operator on scalar `L¹(μ)` represented by an essentially bounded density `g ∈ L∞(μ; X)`:
it sends `φ` to `∫ φ • g`. This is the integral pairing `ContinuousLinearMap.lpPairing` of the
scalar multiplication `(c, x) ↦ c • x`. -/
def representableOperatorMap : Lp X ∞ μ →L[𝕜] Lp 𝕜 1 μ →L[𝕜] X :=
  (ContinuousLinearMap.lsmul 𝕜 𝕜 : 𝕜 →L[𝕜] X →L[𝕜] X).flip.lpPairing μ ∞ 1

/-- The operator represented by `g` sends `φ` to `∫ φ • g`. -/
theorem representableOperatorMap_apply (g : Lp X ∞ μ) (φ : Lp 𝕜 1 μ) :
    representableOperatorMap 𝕜 g φ = ∫ x, φ x • g x ∂μ := by
  simp [representableOperatorMap, ContinuousLinearMap.lpPairing_eq_integral]

/-- The operator represented by `g` sends `c 𝟙_s` to `c • ∫_s g`. -/
@[simp]
theorem representableOperatorMap_indicatorConstLp (g : Lp X ∞ μ) {s : Set S}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : 𝕜) :
    representableOperatorMap 𝕜 g (indicatorConstLp 1 hs hμs c) = c • ∫ x in s, g x ∂μ := by
  rw [representableOperatorMap_apply, ← integral_smul, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := c)] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- On a finite measure space, the vector measure of the operator represented by `g` is the
vector measure with density `g`. -/
@[simp]
theorem toVectorMeasure_representableOperatorMap [IsFiniteMeasure μ] (g : Lp X ∞ μ) :
    (representableOperatorMap 𝕜 g).toVectorMeasure = μ.withDensityᵥ g := by
  ext s hs
  rw [ContinuousLinearMap.toVectorMeasure_apply _ hs, representableOperatorMap_indicatorConstLp,
    one_smul, withDensityᵥ_apply ((Lp.memLp g).integrable le_top) hs]

/-- On a finite measure space, `g ∈ L∞(μ; X)` represents `T` if and only if `g` is a density of the
vector measure of `T`. -/
theorem representableOperatorMap_eq_iff [IsFiniteMeasure μ] {g : Lp X ∞ μ}
    {T : Lp 𝕜 1 μ →L[𝕜] X} :
    representableOperatorMap 𝕜 g = T ↔ T.toVectorMeasure = μ.withDensityᵥ g := by
  rw [← ContinuousLinearMap.toVectorMeasure_inj, toVectorMeasure_representableOperatorMap,
    eq_comm]

end MeasureTheory.Lp

namespace ContinuousLinearMap

variable [IsFiniteMeasure μ] [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]
  (T : Lp 𝕜 1 μ →L[𝕜] X)

omit [IsScalarTower ℝ 𝕜 X] in
/-- An integrable density `f` of the vector measure of `T` is essentially bounded by `‖T‖`, since
`∫_s ‖f‖ = |m_T|(s) ≤ ‖T‖ μ(s)` for every measurable `s`. -/
theorem ae_eNorm_le_of_toVectorMeasure_eq_withDensityᵥ {f : S → X} (hf : Integrable f μ)
    (hT : T.toVectorMeasure = μ.withDensityᵥ f) : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖T‖₊ := by
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hf.aestronglyMeasurable.eNorm
    fun s hs _ ↦ ?_
  rw [setLIntegral_const, ← withDensity_apply _ hs, ← Measure.variation_withDensityᵥ hf, ← hT]
  refine (T.variation_toVectorMeasure_le s).trans_eq ?_
  rw [smul_apply, ENNReal.smul_def, smul_eq_mul]

/-- An integrable density `f` of the vector measure of `T` is essentially bounded, and its class
in `L∞(μ; X)` represents `T` and has norm at most `‖T‖`. -/
theorem exists_representableOperatorMap_eq_of_toVectorMeasure_eq_withDensityᵥ {f : S → X}
    (hf : Integrable f μ) (hT : T.toVectorMeasure = μ.withDensityᵥ f) :
    ∃ g : Lp X ∞ μ, ⇑g =ᵐ[μ] f ∧ ‖g‖ ≤ ‖T‖ ∧ Lp.representableOperatorMap 𝕜 g = T := by
  have hbound := T.ae_eNorm_le_of_toVectorMeasure_eq_withDensityᵥ hf hT
  have hnorm : eLpNorm f ∞ μ ≤ ‖T‖₊ := by
    rw [eLpNorm_exponent_top hf.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_eNorm_bound hbound
  have hmem : MemLp f ∞ μ := hnorm.trans_lt ENNReal.coe_lt_top
  refine ⟨hmem.toLp f, hmem.coeFn_toLp, ?_, ?_⟩
  · rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_coe_of_le_coe hnorm
  · rw [Lp.representableOperatorMap_eq_iff, hT]
    exact ((Lp.memLp _).integrable le_top).withDensityᵥ_eq_iff hf |>.2 hmem.coeFn_toLp |>.symm

end ContinuousLinearMap
