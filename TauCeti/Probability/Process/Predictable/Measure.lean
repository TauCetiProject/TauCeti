/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.TimeMeasure
public import TauCeti.Probability.Process.Predictable.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The finite-horizon predictable time-product measure

For a filtration `ℱ`, `ℱ.predictableMeasure P T` is the restriction of Lebesgue-time × `P`
to `(0,T]`, trimmed to the predictable sigma-algebra. No Brownian process, usual conditions,
or completion of the sample space are needed for this construction. Its native `Lp ℝ 2`
space is the expected-square-energy space for Brownian integrands.

The measure agrees with the ambient product measure on predictable sets. In particular,
`(s,t] × A`, with `A` known at `s` and `t ≤ T`, has mass `(t-s) P(A)`. The initial-time
slice has mass zero, and restricting to a shorter horizon commutes with trimming.
Filtered measure-preserving sample maps preserve these predictable measures, even with
different ambient measurable spaces.
Native `lintegral_trim`, `integral_trim`, and `eLpNorm_trim` then identify predictable
integrands' energies and norms with their ambient time-product counterparts; the dictionary
lemmas below retain the predictable measurability hypothesis, since trimming does not preserve
integrals of arbitrary ambient-product-measurable functions. For `ℱ s`-strongly measurable
variables in `Lᵖ(P)`, extending by zero outside `(s, t]` lands in predictable `Lᵖ` with exact
`Lᵖ` norm determined by the truncated interval length and the spatial `Lᵖ` integral.

The horizon operators `predictableMeasureExtendLp` and `predictableMeasureRestrictLp`
transport native predictable `Lᵖ` classes without exposing measure-equality casts. Extension
by zero is an isometry; restriction is a contraction and is a left inverse to extension.
The extension construction transports `TauCeti.extendByZeroLpₗᵢ` together with its
representative identity, and its API follows the deterministic `timeMeasureExtendLp` API.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

open MeasureTheory Set TauCeti.Probability
open scoped NNReal ENNReal

namespace MeasureTheory.Filtration

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The finite-horizon time-product measure on the predictable sigma-algebra.
It is the expected-energy measure for Brownian stochastic integrands. -/
noncomputable def predictableMeasure (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) (T : ℝ≥0) :
    @Measure (ℝ≥0 × Ω) ℱ.predictable :=
  ((timeMeasure T).prod P).trim ℱ.predictable_le_prod

/-- The predictable measure is the trim of the finite-horizon time-product measure. -/
theorem predictableMeasure_def (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) (T : ℝ≥0) :
    ℱ.predictableMeasure P T = ((timeMeasure T).prod P).trim ℱ.predictable_le_prod :=
  (rfl)

/-- On predictable sets, trimming does not change time-product mass. -/
theorem predictableMeasure_apply (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) (T : ℝ≥0)
    {A : Set (ℝ≥0 × Ω)} (hA : MeasurableSet[ℱ.predictable] A) :
    ℱ.predictableMeasure P T A = (timeMeasure T).prod P A := by
  rw [predictableMeasure_def, trim_measurableSet_eq _ hA]

/-- A filtered measure-preserving sample map preserves finite-horizon predictable
measures. The ambient spaces and the filtrations on its two sides may differ. -/
theorem measurePreserving_prodMap_predictableMeasure {Ω' : Type*} {m' : MeasurableSpace Ω'}
    (ℱ : Filtration ℝ≥0 m) (𝒢 : Filtration ℝ≥0 m')
    {P : Measure Ω} {Q : Measure Ω'} [SFinite P] {f : Ω → Ω'}
    (hf : MeasurePreserving f P Q) (hℱ : ∀ t, Measurable[ℱ t, 𝒢 t] f) (T : ℝ≥0) :
    @MeasurePreserving (ℝ≥0 × Ω) (ℝ≥0 × Ω') ℱ.predictable 𝒢.predictable
      (Prod.map id f) (ℱ.predictableMeasure P T) (𝒢.predictableMeasure Q T) := by
  have hm := ℱ.measurable_prodMap_predictable 𝒢 hℱ
  refine @MeasurePreserving.mk _ _ ℱ.predictable 𝒢.predictable _ _ _ hm ?_
  apply @Measure.ext _ 𝒢.predictable
  intro A hA
  rw [Measure.map_apply hm hA, ℱ.predictableMeasure_apply P T (hm hA),
    𝒢.predictableMeasure_apply Q T hA]
  exact ((MeasurePreserving.id (timeMeasure T)).prod hf).measure_preimage
    (𝒢.predictable_le_prod A hA).nullMeasurableSet

/-- Under a probability measure, the time projection of the predictable measure is
the finite-horizon time measure. Its native `Lp` pullback embeds deterministic integrands
isometrically into predictable integrands. -/
theorem measurePreserving_fst_predictableMeasure (ℱ : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0) :
    @MeasurePreserving _ _ ℱ.predictable _ Prod.fst
      (ℱ.predictableMeasure P T) (timeMeasure T) := by
  have hprod (A : Set ℝ≥0) (hA : MeasurableSet A) :
      (timeMeasure T).prod P (Prod.fst ⁻¹' A) = timeMeasure T A :=
    (measurePreserving_fst (μ := timeMeasure T) (ν := P)).measure_preimage hA.nullMeasurableSet
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  refine ⟨ℱ.measurable_fst_predictable, ?_⟩
  ext A hA
  rw [Measure.map_apply ℱ.measurable_fst_predictable hA,
    predictableMeasure_apply _ _ _ (hA.preimage ℱ.measurable_fst_predictable)]
  exact hprod A hA

/-- Predictable rectangles have time length times event probability, clipped at the horizon. -/
@[simp]
theorem predictableMeasure_Ioc_prod (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
    (T s t : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ℱ.predictableMeasure P T (Ioc s t ×ˢ A) =
      ENNReal.ofReal ((min t T : ℝ≥0) - (s : ℝ)) * P A := by
  rw [predictableMeasure_apply _ _ _ (measurableSet_predictable_Ioc_prod _ _ hA),
    Measure.prod_prod, timeMeasure_Ioc]

/-- At a horizon beyond the right endpoint, a predictable rectangle has its full time length. -/
theorem predictableMeasure_Ioc_prod_of_le (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
    {T s t : ℝ≥0} (ht : t ≤ T) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ℱ.predictableMeasure P T (Ioc s t ×ˢ A) = ENNReal.ofReal ((t : ℝ) - s) * P A := by
  simp [predictableMeasure_Ioc_prod ℱ P T s t hA, min_eq_left ht]

/-- The total predictable mass is the horizon length times the total sample-space mass. -/
@[simp]
theorem predictableMeasure_univ (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
    (T : ℝ≥0) : ℱ.predictableMeasure P T univ = T * P univ := by
  rw [predictableMeasure_apply _ _ _ MeasurableSet.univ, ← univ_prod_univ,
    Measure.prod_prod, timeMeasure_univ]

/-- A finite underlying measure gives a finite predictable measure on every finite horizon. -/
instance (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ≥0) :
    IsFiniteMeasure (ℱ.predictableMeasure P T) := by
  rw [predictableMeasure_def]
  infer_instance

/-- At horizon zero the predictable measure is zero. -/
@[simp]
theorem predictableMeasure_zero (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) :
    ℱ.predictableMeasure P 0 = 0 := by
  simp [predictableMeasure_def]

/-- There is no predictable mass at the initial time, even when the initial event is nontrivial. -/
@[simp]
theorem predictableMeasure_singleton_zero_prod (ℱ : Filtration ℝ≥0 m) (P : Measure Ω)
    [SFinite P] (T : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    ℱ.predictableMeasure P T ({0} ×ˢ A) = 0 := by
  have hzero : MeasurableSet[ℱ.predictable] ({0} ×ˢ A) := by
    simpa only [NNReal.bot_eq_zero] using measurableSet_predictable_singleton_bot_prod hA
  rw [predictableMeasure_apply _ _ _ hzero, Measure.prod_prod,
    timeMeasure_singleton_zero, zero_mul]

/-- Restricting the predictable measure to `(0,S]` clips its horizon to `min S T`. -/
@[simp]
theorem predictableMeasure_restrict (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
    (T S : ℝ≥0) :
    (ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ) =
      ℱ.predictableMeasure P (min S T) := by
  have hS : MeasurableSet[ℱ.predictable] (Ioc 0 S ×ˢ (univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod _ _ MeasurableSet.univ
  rw [predictableMeasure_def, restrict_trim ℱ.predictable_le_prod _ hS,
    ← Measure.restrict_prod_eq_prod_univ, timeMeasure_restrict, predictableMeasure_def]

/-- Restricting to a shorter deterministic horizon gives its predictable measure. -/
theorem predictableMeasure_restrict_of_le (ℱ : Filtration ℝ≥0 m) (P : Measure Ω)
    [SFinite P] {S T : ℝ≥0} (hST : S ≤ T) :
    (ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ) = ℱ.predictableMeasure P S := by
  rw [predictableMeasure_restrict, min_eq_left hST]

/-- Almost every predictable time/sample pair lies in the positive-time horizon. -/
theorem ae_mem_Ioc_prod_predictableMeasure (ℱ : Filtration ℝ≥0 m) (P : Measure Ω)
    [SFinite P] (T : ℝ≥0) :
    ∀ᵐ x ∂ℱ.predictableMeasure P T, x ∈ Ioc 0 T ×ˢ (univ : Set Ω) := by
  have h := ae_restrict_mem (μ := ℱ.predictableMeasure P T)
    (measurableSet_predictable_Ioc_prod (𝓕 := ℱ) 0 T MeasurableSet.univ)
  rwa [ℱ.predictableMeasure_restrict_of_le P le_rfl] at h

/-- Predictable measures increase with the horizon. -/
theorem predictableMeasure_mono (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
    {S T : ℝ≥0} (hST : S ≤ T) : ℱ.predictableMeasure P S ≤ ℱ.predictableMeasure P T := by
  rw [← ℱ.predictableMeasure_restrict_of_le P hST]
  exact Measure.restrict_le_self

section ExtendLp

variable (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
  {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
  [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {S T U : ℝ≥0}

variable (𝕜) in
/-- Extend a predictable `Lᵖ` class by zero from `S` to `T`, preserving its norm. -/
noncomputable def predictableMeasureExtendLp (hST : S ≤ T) :
    Lp E p (ℱ.predictableMeasure P S) →ₗᵢ[𝕜] Lp E p (ℱ.predictableMeasure P T) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  exact (TauCeti.castLpₗᵢ (𝕜 := 𝕜)
    (Measure.restrict_univ (μ := ℱ.predictableMeasure P T))).toLinearIsometry.comp
      ((TauCeti.extendByZeroLpₗᵢ 𝕜 (ℱ.predictableMeasure P T)
        (measurableSet_predictable_Ioc_prod 0 S MeasurableSet.univ).nullMeasurableSet
          (subset_univ _)).comp
          (TauCeti.castLpₗᵢ (𝕜 := 𝕜)
            (ℱ.predictableMeasure_restrict_of_le P hST).symm).toLinearIsometry)

/-- The horizon extension is represented by the original function cut off to `(0,S]`. -/
theorem coeFn_predictableMeasureExtendLp (hST : S ≤ T)
    (f : Lp E p (ℱ.predictableMeasure P S)) :
    ⇑(ℱ.predictableMeasureExtendLp P 𝕜 hST f) =ᵐ[ℱ.predictableMeasure P T]
      (Ioc 0 S ×ˢ univ).indicator f := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have h := TauCeti.coeFn_extendByZeroLpₗᵢ 𝕜
    (measurableSet_predictable_Ioc_prod (𝓕 := ℱ) 0 S MeasurableSet.univ).nullMeasurableSet
    (subset_univ _)
    (TauCeti.castLpₗᵢ (𝕜 := 𝕜) (ℱ.predictableMeasure_restrict_of_le P hST).symm f)
  have h' := h.filter_mono (le_of_eq
    (congrArg ae (Measure.restrict_univ (μ := ℱ.predictableMeasure P T))).symm)
  have hcast := funext (TauCeti.coeFn_castLpₗᵢ (𝕜 := 𝕜)
    (ℱ.predictableMeasure_restrict_of_le P hST).symm f)
  filter_upwards [h'] with x hx
  simpa only [predictableMeasureExtendLp, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, TauCeti.coeFn_castLpₗᵢ, hcast] using hx

/-- Any representative on the shorter horizon may be used to compute the extension. -/
theorem coeFn_predictableMeasureExtendLp_of_ae_eq (hST : S ≤ T)
    {f : Lp E p (ℱ.predictableMeasure P S)} {h : ℝ≥0 × Ω → E}
    (hf : f =ᵐ[ℱ.predictableMeasure P S] h) :
    ⇑(ℱ.predictableMeasureExtendLp P 𝕜 hST f) =ᵐ[ℱ.predictableMeasure P T]
      (Ioc 0 S ×ˢ univ).indicator h := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hf' : f =ᵐ[(ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ)] h := by
    rw [ℱ.predictableMeasure_restrict_of_le P hST]
    exact hf
  exact (ℱ.coeFn_predictableMeasureExtendLp P (𝕜 := 𝕜) hST f).trans
    ((ae_eq_restrict_iff_indicator_ae_eq
      (measurableSet_predictable_Ioc_prod 0 S MeasurableSet.univ)).mp hf')

/-- On the shorter horizon the extension represents the original class. -/
theorem coeFn_predictableMeasureExtendLp_restrict (hST : S ≤ T)
    (f : Lp E p (ℱ.predictableMeasure P S)) :
    ⇑(ℱ.predictableMeasureExtendLp P 𝕜 hST f) =ᵐ[ℱ.predictableMeasure P S] f := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have h : ⇑(ℱ.predictableMeasureExtendLp P 𝕜 hST f)
      =ᵐ[(ℱ.predictableMeasure P T).restrict (Ioc 0 S ×ˢ univ)]
        (Ioc 0 S ×ˢ univ).indicator f :=
    ae_restrict_of_ae (ℱ.coeFn_predictableMeasureExtendLp P (𝕜 := 𝕜) hST f)
  have h' := h.trans (indicator_ae_eq_restrict
    (measurableSet_predictable_Ioc_prod 0 S MeasurableSet.univ).nullMeasurableSet)
  rwa [ℱ.predictableMeasure_restrict_of_le P hST] at h'

/-- Extension to the same horizon is the identity. -/
@[simp]
theorem predictableMeasureExtendLp_self (f : Lp E p (ℱ.predictableMeasure P S)) :
    ℱ.predictableMeasureExtendLp P 𝕜 le_rfl f = f :=
  Lp.ext (ℱ.coeFn_predictableMeasureExtendLp_restrict P (𝕜 := 𝕜) le_rfl f)

/-- Two successive horizon extensions equal the direct extension. -/
@[simp]
theorem predictableMeasureExtendLp_predictableMeasureExtendLp (hST : S ≤ T) (hTU : T ≤ U)
    (f : Lp E p (ℱ.predictableMeasure P S)) :
    ℱ.predictableMeasureExtendLp P 𝕜 hTU (ℱ.predictableMeasureExtendLp P 𝕜 hST f) =
      ℱ.predictableMeasureExtendLp P 𝕜 (hST.trans hTU) f := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  apply Lp.ext
  filter_upwards [ℱ.coeFn_predictableMeasureExtendLp_of_ae_eq P (𝕜 := 𝕜) hTU
    (ℱ.coeFn_predictableMeasureExtendLp P (𝕜 := 𝕜) hST f),
    ℱ.coeFn_predictableMeasureExtendLp P (𝕜 := 𝕜) (hST.trans hTU) f] with x hx hy
  rw [hx, hy, indicator_indicator,
    inter_eq_self_of_subset_right (prod_mono_left (Ioc_subset_Ioc_right hST))]

/-- A longer-horizon indicator representative characterizes the zero-extension. -/
theorem predictableMeasureExtendLp_eq_of_ae_eq_indicator (hST : S ≤ T)
    {f : Lp E p (ℱ.predictableMeasure P S)} {g : Lp E p (ℱ.predictableMeasure P T)}
    (hfg : g =ᵐ[ℱ.predictableMeasure P T] (Ioc 0 S ×ˢ univ).indicator f) :
    ℱ.predictableMeasureExtendLp P 𝕜 hST f = g :=
  Lp.ext ((ℱ.coeFn_predictableMeasureExtendLp P (𝕜 := 𝕜) hST f).trans hfg.symm)

/-- The zero-extension vanishes after the shorter horizon. -/
theorem ae_predictableMeasureExtendLp_eq_zero (hST : S ≤ T)
    (f : Lp E p (ℱ.predictableMeasure P S)) :
    ∀ᵐ x ∂ℱ.predictableMeasure P T, S < x.1 → ℱ.predictableMeasureExtendLp P 𝕜 hST f x = 0 := by
  filter_upwards [ℱ.coeFn_predictableMeasureExtendLp P (𝕜 := 𝕜) hST f] with x hx hS
  rw [hx, indicator_of_notMem]
  exact fun h ↦ (not_le_of_gt hS) h.1.2

/-- Shorter-horizon agreement and a vanishing tail characterize the zero-extension. -/
theorem predictableMeasureExtendLp_eq_of_ae_eq_of_ae_eq_zero (hST : S ≤ T)
    {f : Lp E p (ℱ.predictableMeasure P S)} {g : Lp E p (ℱ.predictableMeasure P T)}
    (hfg : g =ᵐ[ℱ.predictableMeasure P S] f)
    (hg : ∀ᵐ x ∂ℱ.predictableMeasure P T, S < x.1 → g x = 0) :
    ℱ.predictableMeasureExtendLp P 𝕜 hST f = g := by
  apply Lp.ext
  filter_upwards [ℱ.coeFn_predictableMeasureExtendLp_of_ae_eq P (𝕜 := 𝕜) hST hfg.symm,
    hg, ℱ.ae_mem_Ioc_prod_predictableMeasure P T] with x hx hz hxt
  rw [hx]
  by_cases hS : x ∈ Ioc 0 S ×ˢ (univ : Set Ω)
  · exact indicator_of_mem hS _
  · rw [indicator_of_notMem hS, hz (lt_of_not_ge fun hle ↦
      hS ⟨⟨hxt.1.1, hle⟩, mem_univ _⟩)]

/-- Extension clips a rectangle indicator's right endpoint to the shorter horizon. -/
@[simp]
theorem predictableMeasureExtendLp_indicatorConstLp_Ioc_prod
    (hST : S ≤ T) (s t : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A)
    {hμ : ℱ.predictableMeasure P S (Ioc s t ×ˢ A) ≠ ∞} (c : E) :
    ℱ.predictableMeasureExtendLp P 𝕜 hST
        (indicatorConstLp p (measurableSet_predictable_Ioc_prod s t hA) hμ c) =
      indicatorConstLp p (measurableSet_predictable_Ioc_prod s (min t S) hA)
        (by rwa [ℱ.predictableMeasure_Ioc_prod P T s (min t S) hA, min_assoc,
          min_eq_left hST, ← ℱ.predictableMeasure_Ioc_prod P S s t hA]) c := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  apply Lp.ext
  filter_upwards [ℱ.coeFn_predictableMeasureExtendLp_of_ae_eq P (𝕜 := 𝕜) hST
    (indicatorConstLp_coeFn (p := p) (hs := measurableSet_predictable_Ioc_prod s t hA)
      (hμs := hμ) (c := c)),
    indicatorConstLp_coeFn (μ := ℱ.predictableMeasure P T) (p := p)
      (hs := measurableSet_predictable_Ioc_prod s (min t S) hA)
      (hμs := _) (c := c)] with x hx hy
  rw [hx, hy, indicator_indicator, prod_inter_prod, univ_inter, Ioc_inter_Ioc,
    max_eq_right (zero_le : (0 : ℝ≥0) ≤ s), min_comm]

/-- Extension preserves a finite-mass rectangle ending before the shorter horizon. -/
theorem predictableMeasureExtendLp_indicatorConstLp_Ioc_prod_of_le
    (hST : S ≤ T) {s t : ℝ≥0} (ht : t ≤ S) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) {hμ : ℱ.predictableMeasure P S (Ioc s t ×ˢ A) ≠ ∞}
    (c : E) :
    ℱ.predictableMeasureExtendLp P 𝕜 hST
        (indicatorConstLp p (measurableSet_predictable_Ioc_prod s t hA) hμ c) =
      indicatorConstLp p (measurableSet_predictable_Ioc_prod s t hA)
        (by rwa [ℱ.predictableMeasure_Ioc_prod_of_le P (ht.trans hST) hA,
          ← ℱ.predictableMeasure_Ioc_prod_of_le P ht hA]) c := by
  simpa only [min_eq_left ht] using
    ℱ.predictableMeasureExtendLp_indicatorConstLp_Ioc_prod P (𝕜 := 𝕜) hST s t hA (hμ := hμ) c

end ExtendLp

section RestrictLp

variable (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
  {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
  [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {S T U : ℝ≥0}

variable (𝕜) in
/-- Restrict a predictable `Lᵖ` class to a shorter horizon as a continuous linear map. -/
noncomputable def predictableMeasureRestrictLp (hST : S ≤ T) :
    Lp E p (ℱ.predictableMeasure P T) →L[𝕜] Lp E p (ℱ.predictableMeasure P S) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  exact (TauCeti.castLpₗᵢ (𝕜 := 𝕜)
    (ℱ.predictableMeasure_restrict_of_le P hST)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (LpToLpRestrictCLM (ℝ≥0 × Ω) E 𝕜 (ℱ.predictableMeasure P T) p (Ioc 0 S ×ˢ univ))

/-- Restriction keeps the representative on the shorter horizon. -/
theorem coeFn_predictableMeasureRestrictLp (hST : S ≤ T)
    (f : Lp E p (ℱ.predictableMeasure P T)) :
    ⇑(ℱ.predictableMeasureRestrictLp P 𝕜 hST f) =ᵐ[ℱ.predictableMeasure P S] f := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have h := LpToLpRestrictCLM_coeFn 𝕜 (Ioc 0 S ×ˢ univ) f
  have h' := h.filter_mono (le_of_eq
    (congrArg ae (ℱ.predictableMeasure_restrict_of_le P hST)).symm)
  filter_upwards [h'] with x hx
  simpa only [predictableMeasureRestrictLp, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, TauCeti.coeFn_castLpₗᵢ] using hx

/-- Restricting a class does not increase its norm. -/
theorem norm_predictableMeasureRestrictLp_apply_le (hST : S ≤ T)
    (f : Lp E p (ℱ.predictableMeasure P T)) :
    ‖ℱ.predictableMeasureRestrictLp P 𝕜 hST f‖ ≤ ‖f‖ := by
  simp only [predictableMeasureRestrictLp, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.norm_map]
  exact norm_Lp_toLp_restrict_le _ f

/-- Restricting to the same horizon is the identity. -/
@[simp]
theorem predictableMeasureRestrictLp_self (f : Lp E p (ℱ.predictableMeasure P S)) :
    ℱ.predictableMeasureRestrictLp P 𝕜 le_rfl f = f :=
  Lp.ext (ℱ.coeFn_predictableMeasureRestrictLp P (𝕜 := 𝕜) le_rfl f)

/-- Two successive horizon restrictions equal the direct restriction. -/
@[simp]
theorem predictableMeasureRestrictLp_predictableMeasureRestrictLp (hST : S ≤ T)
    (hTU : T ≤ U) (f : Lp E p (ℱ.predictableMeasure P U)) :
    ℱ.predictableMeasureRestrictLp P 𝕜 hST (ℱ.predictableMeasureRestrictLp P 𝕜 hTU f) =
      ℱ.predictableMeasureRestrictLp P 𝕜 (hST.trans hTU) f :=
  Lp.ext ((ℱ.coeFn_predictableMeasureRestrictLp P (𝕜 := 𝕜) hST _).trans
    (((ℱ.coeFn_predictableMeasureRestrictLp P (𝕜 := 𝕜) hTU f).filter_mono
      (ae_mono (ℱ.predictableMeasure_mono P hST))).trans
        (ℱ.coeFn_predictableMeasureRestrictLp P (𝕜 := 𝕜) (hST.trans hTU) f).symm))

/-- Restricting a zero-extension recovers the original class. -/
@[simp]
theorem predictableMeasureRestrictLp_predictableMeasureExtendLp (hST : S ≤ T)
    (f : Lp E p (ℱ.predictableMeasure P S)) :
    ℱ.predictableMeasureRestrictLp P 𝕜 hST (ℱ.predictableMeasureExtendLp P 𝕜 hST f) = f :=
  Lp.ext ((ℱ.coeFn_predictableMeasureRestrictLp P (𝕜 := 𝕜) hST _).trans
    (ℱ.coeFn_predictableMeasureExtendLp_restrict P (𝕜 := 𝕜) hST f))

/-- Extending a restriction is the original class cut off to the shorter horizon. -/
theorem coeFn_predictableMeasureExtendLp_predictableMeasureRestrictLp (hST : S ≤ T)
    (f : Lp E p (ℱ.predictableMeasure P T)) :
    ⇑(ℱ.predictableMeasureExtendLp P 𝕜 hST (ℱ.predictableMeasureRestrictLp P 𝕜 hST f))
      =ᵐ[ℱ.predictableMeasure P T] (Ioc 0 S ×ˢ univ).indicator f :=
  ℱ.coeFn_predictableMeasureExtendLp_of_ae_eq P (𝕜 := 𝕜) hST
    (ℱ.coeFn_predictableMeasureRestrictLp P (𝕜 := 𝕜) hST f)

/-- Restriction preserves finite-mass indicator classes. -/
@[simp]
theorem predictableMeasureRestrictLp_indicatorConstLp (hST : S ≤ T)
    {A : Set (ℝ≥0 × Ω)} (hA : MeasurableSet[ℱ.predictable] A)
    {hμ : ℱ.predictableMeasure P T A ≠ ∞} (c : E) :
    ℱ.predictableMeasureRestrictLp P 𝕜 hST (indicatorConstLp p hA hμ c) =
      indicatorConstLp p hA
        (ne_top_of_le_ne_top hμ (ℱ.predictableMeasure_mono P hST A)) c := by
  apply Lp.ext
  exact (ℱ.coeFn_predictableMeasureRestrictLp P (𝕜 := 𝕜) hST _).trans
    (((indicatorConstLp_coeFn (p := p) (hs := hA) (hμs := hμ) (c := c)).filter_mono
      (ae_mono (ℱ.predictableMeasure_mono P hST))).trans indicatorConstLp_coeFn.symm)

/-- Extending the restriction recovers a class whose tail vanishes. -/
theorem predictableMeasureExtendLp_predictableMeasureRestrictLp_of_ae_eq_zero
    (hST : S ≤ T) {f : Lp E p (ℱ.predictableMeasure P T)}
    (hf : ∀ᵐ x ∂ℱ.predictableMeasure P T, S < x.1 → f x = 0) :
    ℱ.predictableMeasureExtendLp P 𝕜 hST (ℱ.predictableMeasureRestrictLp P 𝕜 hST f) = f :=
  ℱ.predictableMeasureExtendLp_eq_of_ae_eq_of_ae_eq_zero P hST
    (ℱ.coeFn_predictableMeasureRestrictLp P (𝕜 := 𝕜) hST f).symm hf

/-- The range of zero-extension consists exactly of classes vanishing after `S`. -/
theorem mem_range_predictableMeasureExtendLp_iff (hST : S ≤ T)
    {f : Lp E p (ℱ.predictableMeasure P T)} :
    f ∈ Set.range (ℱ.predictableMeasureExtendLp P 𝕜 hST) ↔
      ∀ᵐ x ∂ℱ.predictableMeasure P T, S < x.1 → f x = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ℱ.ae_predictableMeasureExtendLp_eq_zero P hST g
  · intro hf
    exact ⟨_, ℱ.predictableMeasureExtendLp_predictableMeasureRestrictLp_of_ae_eq_zero P hST hf⟩

/-- Classes agreeing on the initial horizon split into zero-extension and a complementary cutoff. -/
theorem eq_predictableMeasureExtendLp_add_of_ae_eq_indicator_compl (hST : S ≤ T)
    {f : Lp E p (ℱ.predictableMeasure P T)} {g : Lp E p (ℱ.predictableMeasure P S)}
    {k : Lp E p (ℱ.predictableMeasure P T)}
    (hfg : f =ᵐ[ℱ.predictableMeasure P S] g)
    (hk : k =ᵐ[ℱ.predictableMeasure P T] (Ioc 0 S ×ˢ univ)ᶜ.indicator f) :
    f = ℱ.predictableMeasureExtendLp P 𝕜 hST g + k := by
  have hrestrict : ℱ.predictableMeasureRestrictLp P 𝕜 hST f = g :=
    Lp.ext ((ℱ.coeFn_predictableMeasureRestrictLp P (𝕜 := 𝕜) hST f).trans hfg)
  have hsub : f - ℱ.predictableMeasureExtendLp P 𝕜 hST g = k := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub f (ℱ.predictableMeasureExtendLp P 𝕜 hST g),
      ℱ.coeFn_predictableMeasureExtendLp_predictableMeasureRestrictLp P (𝕜 := 𝕜) hST f,
      hk] with x hsub hext hkx
    rw [hrestrict] at hext
    rw [hsub, Pi.sub_apply, hext, hkx, indicator_compl, Pi.sub_apply]
  exact sub_eq_iff_eq_add'.mp hsub

end RestrictLp

/-- Horizon restriction has operator norm at most one over a nontrivially normed field. -/
theorem norm_predictableMeasureRestrictLp_le (ℱ : Filtration ℝ≥0 m) (P : Measure Ω)
    [SFinite P] {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {S T : ℝ≥0} (hST : S ≤ T) :
    ‖(ℱ.predictableMeasureRestrictLp P 𝕜 hST :
      Lp E p (ℱ.predictableMeasure P T) →L[𝕜] Lp E p (ℱ.predictableMeasure P S))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using ℱ.norm_predictableMeasureRestrictLp_apply_le P (𝕜 := 𝕜) hST f

/-- The identity from a larger predictable sigma-algebra to a smaller one preserves
finite-horizon time-product measure. Its native Lᵖ pullback embeds the smaller integrand space
isometrically into the larger one. No finiteness assumption on the sample measure is needed. -/
theorem measurePreserving_id_predictableMeasure {ℱ 𝒢 : Filtration ℝ≥0 m}
    (h : ℱ ≤ 𝒢) (P : Measure Ω) (T : ℝ≥0) :
    @MeasurePreserving (ℝ≥0 × Ω) (ℝ≥0 × Ω) 𝒢.predictable ℱ.predictable
      id (𝒢.predictableMeasure P T) (ℱ.predictableMeasure P T) := by
  have hm : @Measurable (ℝ≥0 × Ω) (ℝ≥0 × Ω) 𝒢.predictable ℱ.predictable id :=
    measurable_id'' (predictable_mono h)
  refine @MeasurePreserving.mk _ _ 𝒢.predictable ℱ.predictable _ _ _ hm ?_
  apply @Measure.ext _ ℱ.predictable
  intro A hA
  rw [Measure.map_apply hm hA, Set.preimage_id,
    𝒢.predictableMeasure_apply P T (predictable_mono h _ hA),
    ℱ.predictableMeasure_apply P T hA]

section Dictionary

variable (ℱ : Filtration ℝ≥0 m) (P : Measure Ω)

/-- The predictable integral is the ambient time-product integral for predictable functions. -/
theorem integral_predictableMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ≥0 × Ω → E} (hf : StronglyMeasurable[ℱ.predictable] f) (T : ℝ≥0) :
    ∫ p, f p ∂ℱ.predictableMeasure P T = ∫ p, f p ∂(timeMeasure T).prod P :=
  (integral_trim ℱ.predictable_le_prod hf).symm

/-- Nonnegative predictable integrals can be computed by ordinary time/sample integration.
Unlike a real Bochner energy, the lower integral records infinite square energy faithfully. -/
theorem lintegral_predictableMeasure [SFinite P] {f : ℝ≥0 × Ω → ℝ≥0∞}
    (hf : Measurable[ℱ.predictable] f) (T : ℝ≥0) :
    ∫⁻ p, f p ∂ℱ.predictableMeasure P T = ∫⁻ t, ∫⁻ ω, f (t, ω) ∂P ∂timeMeasure T := by
  rw [predictableMeasure_def, lintegral_trim ℱ.predictable_le_prod hf]
  exact lintegral_prod _ (hf.mono ℱ.predictable_le_prod le_rfl).aemeasurable

/-- Equality of predictable representatives almost everywhere is the same for the
predictable measure and the ambient time-product measure. -/
theorem ae_eq_predictableMeasure_iff {E : Type*} [MeasurableSpace E] [MeasurableEq E]
    {f g : ℝ≥0 × Ω → E} (hf : Measurable[ℱ.predictable] f)
    (hg : Measurable[ℱ.predictable] g) (T : ℝ≥0) :
    f =ᵐ[ℱ.predictableMeasure P T] g ↔ f =ᵐ[(timeMeasure T).prod P] g :=
  ⟨ae_eq_of_ae_eq_trim, ae_eq_trim_of_measurable ℱ.predictable_le_prod hf hg⟩

/-- For predictable functions the native `MemLp` condition can be tested in the ambient
product measure, at every exponent (in particular exponent two). -/
theorem memLp_predictableMeasure_iff {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {f : ℝ≥0 × Ω → E} (hf : StronglyMeasurable[ℱ.predictable] f) (T : ℝ≥0) (p : ℝ≥0∞) :
    MemLp f p (ℱ.predictableMeasure P T) ↔ MemLp f p ((timeMeasure T).prod P) := by
  simp only [MemLp, predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hf]

end Dictionary

/-- A left-endpoint-measurable `Lᵖ` height, extended by zero outside `(s,t]`, belongs to
predictable `Lᵖ` on every finite horizon. Empty or reversed intervals are allowed. -/
theorem memLp_indicator_Ioc_predictableMeasure {E : Type*} [TopologicalSpace E]
    [ESeminormedAddMonoid E]
    (ℱ : Filtration ℝ≥0 m) {P : Measure Ω} [SFinite P] {p : ℝ≥0∞}
    (T s t : ℝ≥0) {a : Ω → E} (ha : StronglyMeasurable[ℱ s] a) (haLp : MemLp a p P) :
    MemLp (fun q : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ a q.2) q.1)
      p (ℱ.predictableMeasure P T) := by
  apply (ℱ.memLp_predictableMeasure_iff P
    (ℱ.stronglyMeasurable_indicator_Ioc_predictable s t ha) T p).2
  convert (haLp.comp_snd (timeMeasure T)).indicator
    ((measurableSet_Ioc (a := s) (b := t)).prod MeasurableSet.univ).nullMeasurableSet using 1
  ext q
  by_cases hq : q.1 ∈ Ioc s t <;> simp [hq]

/-- For `0 < p < ∞`, the `p`-th power of the predictable `Lᵖ` norm of an `ℱ s`-strongly measurable
`Lᵖ(P)` function extended by zero outside `(s, t]` equals `(timeMeasure T).real (Ioc s t)` times
the spatial `Lᵖ` integral. -/
theorem norm_toLp_indicator_Ioc_rpow (ℱ : Filtration ℝ≥0 m) (P : Measure Ω) [SFinite P]
    {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (T s t : ℝ≥0)
    {ξ : Ω → E} (hξ : StronglyMeasurable[ℱ s] ξ) (hξp : MemLp ξ p P) :
    ‖(ℱ.memLp_indicator_Ioc_predictableMeasure T s t hξ hξp).toLp
      (fun q : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ ξ q.2) q.1)‖ ^ p.toReal =
      (timeMeasure T).real (Ioc s t) * ∫ ω, ‖ξ ω‖ ^ p.toReal ∂P := by
  have hmem := ℱ.memLp_indicator_Ioc_predictableMeasure T s t hξ hξp
  have h1 : ‖hmem.toLp (fun q : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ ξ q.2) q.1)‖ ^ p.toReal =
      ∫ q, ‖(Ioc s t).indicator (fun _ ↦ ξ q.2) q.1‖ ^ p.toReal ∂ℱ.predictableMeasure P T := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    rw [← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp]
    exact integral_congr_ae <| hmem.coeFn_toLp.mono fun _ h ↦ by dsimp only; rw [h]
  have hsm : StronglyMeasurable[ℱ.predictable]
      (fun q : ℝ≥0 × Ω ↦ (Ioc s t).indicator (fun _ ↦ ξ q.2) q.1) :=
    ℱ.stronglyMeasurable_indicator_Ioc_predictable s t hξ
  rw [h1, ℱ.integral_predictableMeasure P
    ((Real.continuous_rpow_const ENNReal.toReal_nonneg).comp_stronglyMeasurable hsm.norm) T]
  have hmul : (fun q : ℝ≥0 × Ω ↦ ‖(Ioc s t).indicator (fun _ ↦ ξ q.2) q.1‖ ^ p.toReal) =
      fun q ↦ (Ioc s t).indicator (1 : ℝ≥0 → ℝ) q.1 * ‖ξ q.2‖ ^ p.toReal := by
    ext ⟨r, ω⟩
    by_cases hr : r ∈ Ioc s t <;> simp [hr, Real.zero_rpow (ENNReal.toReal_pos hp0 hp).ne']
  rw [hmul, integral_prod_mul ((Ioc s t).indicator (1 : ℝ≥0 → ℝ)) (fun ω ↦ ‖ξ ω‖ ^ p.toReal),
    integral_indicator_one measurableSet_Ioc]

end MeasureTheory.Filtration
