/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import TauCeti.MeasureTheory.Function.L2Space.MeanZero
public import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv

/-!
# Pullback isometry on `L²` and its conditional expectation adjoint

For a measurable map `m : Y → X` and an arbitrary measure `η` on `Y`, composition with `m` defines
an isometric `𝕜`-linear map
`MeasureTheory.Measure.pullbackL2 η 𝕜 m hm : Lp E 2 (η.map m) →L[𝕜] Lp E 2 η`, the `L²`
specialization of Mathlib's `MeasureTheory.Lp.compMeasurePreservingₗᵢ`.
When `E` is a Hilbert space over `𝕜`, its adjoint
`MeasureTheory.Measure.condExpOperator η 𝕜 m hm : Lp E 2 η →L[𝕜] Lp E 2 (η.map m)` is defined for
an arbitrary measure `η` as a surjective contraction that inverts `pullbackL2` on the left; both
operators satisfy identity and composition laws up to the canonical pushforward measure transports
`TauCeti.castLpₗᵢ`.

For arbitrary `η`, `pullbackL2` preserves integrals and applying `pullbackL2` to
`condExpOperator η 𝕜 m hm b` agrees with Mathlib's `L²` conditional expectation `condExpL2`. When
the trimmed measure `η.trim hm.comap_le` is σ-finite and `b` is integrable (in particular, for
every `b` when `η` is a finite measure), `condExpOperator` preserves integrals and applying
`pullbackL2` to `condExpOperator η 𝕜 m hm b` yields `η[b | σ(m)]` almost everywhere. On finite
measure spaces, `condExpOperator` maps `L²₀(η)` onto `L²₀(η.map m)`.

## Main definitions

* `MeasureTheory.Measure.pullbackL2`: pullback along a measurable map `m : Y → X` as an `L²`
  isometry (the `L²` specialization of `MeasureTheory.Lp.compMeasurePreservingₗᵢ`).
* `MeasureTheory.Measure.condExpOperator`: Hilbert-space adjoint of `pullbackL2` for an arbitrary
  measure `η` (the conditional expectation operator given `m`).

## Main results

* `MeasureTheory.Measure.pullbackL2_apply`, `MeasureTheory.Measure.isometry_pullbackL2`,
  `MeasureTheory.Measure.norm_pullbackL2`, `MeasureTheory.Measure.inner_pullbackL2`:
  `pullbackL2` evaluates to `Lp.compMeasurePreserving` and is an `L²` isometry.
* `MeasureTheory.Measure.pullbackL2_id`, `MeasureTheory.Measure.pullbackL2_comp`,
  `MeasureTheory.Measure.condExpOperator_id`, `MeasureTheory.Measure.condExpOperator_comp`:
  operator-level identity and composition laws via `TauCeti.castLpₗᵢ` for `Measure.map_id` and
  `Measure.map_map`.
* `MeasureTheory.Measure.condExpOperator_comp_pullbackL2`,
  `MeasureTheory.Measure.condExpOperator_surjective`,
  `MeasureTheory.Measure.norm_condExpOperator_le_one`: `condExpOperator` is a surjective contraction
  and a left inverse of `pullbackL2`.
* `MeasureTheory.Measure.range_pullbackL2`,
  `MeasureTheory.Measure.pullbackL2_condExpOperator_eq_condExpL2`,
  `MeasureTheory.Measure.pullbackL2_condExpOperator_ae_eq`,
  `MeasureTheory.Measure.pullbackL2_condExpOperator_ae_eq_of_isFiniteMeasure`: the range of
  `pullbackL2` is `lpMeas`, and applying `pullbackL2` to `condExpOperator η 𝕜 m hm b` equals
  `condExpL2` for arbitrary `η`, and yields `η[b | σ(m)]` almost everywhere for integrable `b` when
  `η.trim hm.comap_le` is σ-finite (in particular for finite `η`).
* `MeasureTheory.Measure.integral_pullbackL2`, `MeasureTheory.Measure.integral_condExpOperator`,
  `MeasureTheory.Measure.integral_condExpOperator_of_isFiniteMeasure`,
  `MeasureTheory.Measure.map_meanZeroL2_condExpOperator`: `pullbackL2` preserves integrals for
  arbitrary `η`, `condExpOperator` preserves integrals for integrable `b` when `η.trim hm.comap_le`
  is σ-finite (in particular for finite `η`), and for finite `η` `condExpOperator` maps `L²₀(η)`
  onto `L²₀(η.map m)`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §25.5, p. 375,
  for the score pullback and conditional-expectation adjoint pair on `L²`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace MeasureTheory.Measure

section PullbackL2

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

section NormedModule

variable {𝕜 E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Composition with a measurable map `m : Y → X`, as an isometry
`Lp E 2 (η.map m) →L[𝕜] Lp E 2 η`: the `L²` specialization of Mathlib's
`MeasureTheory.Lp.compMeasurePreservingₗᵢ`. -/
def pullbackL2 (η : Measure Y) (𝕜 : Type*) {E : Type*} [NormedRing 𝕜] [NormedAddCommGroup E]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (m : Y → X) (hm : Measurable m) :
    Lp E 2 (η.map m) →L[𝕜] Lp E 2 η :=
  (Lp.compMeasurePreservingₗᵢ 𝕜 m (hm.measurePreserving η)).toContinuousLinearMap

theorem pullbackL2_def (η : Measure Y) (𝕜 : Type*) {E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (m : Y → X) (hm : Measurable m) :
    pullbackL2 η 𝕜 (E := E) m hm =
      (Lp.compMeasurePreservingₗᵢ 𝕜 m (hm.measurePreserving η)).toContinuousLinearMap :=
  (rfl)

/-- `pullbackL2` evaluates to `MeasureTheory.Lp.compMeasurePreserving`. -/
theorem pullbackL2_apply (η : Measure Y) (𝕜 : Type*) {E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (m : Y → X) (hm : Measurable m)
    (g : Lp E 2 (η.map m)) :
    pullbackL2 η 𝕜 m hm g = Lp.compMeasurePreserving m (hm.measurePreserving η) g := by
  rw [pullbackL2_def, LinearIsometry.coe_toContinuousLinearMap, Lp.compMeasurePreservingₗᵢ_apply]

/-- `pullbackL2` agrees almost everywhere with precomposition by `m`. -/
theorem coeFn_pullbackL2 (η : Measure Y) (𝕜 : Type*) {E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (m : Y → X) (hm : Measurable m)
    (g : Lp E 2 (η.map m)) : (pullbackL2 η 𝕜 m hm g : Y → E) =ᵐ[η] g ∘ m := by
  rw [pullbackL2_apply]
  exact Lp.coeFn_compMeasurePreserving g (hm.measurePreserving η)

/-- `pullbackL2` is an isometry. -/
theorem isometry_pullbackL2 (η : Measure Y) (𝕜 : Type*) {E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (m : Y → X) (hm : Measurable m) :
    Isometry (pullbackL2 η 𝕜 (E := E) m hm) := by
  rw [pullbackL2_def, LinearIsometry.coe_toContinuousLinearMap]
  exact (Lp.compMeasurePreservingₗᵢ 𝕜 m (hm.measurePreserving η)).isometry

/-- `pullbackL2` preserves `L²` norms. -/
@[simp]
theorem norm_pullbackL2 (η : Measure Y) (𝕜 : Type*) {E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (m : Y → X) (hm : Measurable m)
    (g : Lp E 2 (η.map m)) : ‖pullbackL2 η 𝕜 m hm g‖ = ‖g‖ := by
  rw [pullbackL2_apply]
  exact Lp.norm_compMeasurePreserving g (hm.measurePreserving η)

/-- `pullbackL2` maps an indicator function to the indicator of its preimage. -/
theorem pullbackL2_indicatorConstLp (η : Measure Y) (𝕜 : Type*) {E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (m : Y → X) (hm : Measurable m)
    {s : Set X} (hs : MeasurableSet s) (hμs : (η.map m) s ≠ ∞) (c : E) :
    pullbackL2 η 𝕜 m hm (indicatorConstLp 2 hs hμs c) =
      indicatorConstLp 2 (hm hs)
        (by rwa [(hm.measurePreserving η).measure_preimage hs.nullMeasurableSet]) c := by
  rw [pullbackL2_apply]
  exact Lp.indicatorConstLp_compMeasurePreserving hs hμs c (hm.measurePreserving η)

/-- `pullbackL2` sends constant functions to constant functions. -/
@[simp]
theorem pullbackL2_const (η : Measure Y) [IsFiniteMeasure η] (𝕜 : Type*) {E : Type*}
    [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (m : Y → X) (hm : Measurable m) (c : E) :
    pullbackL2 η 𝕜 m hm (Lp.const 2 (η.map m) c) = Lp.const 2 η c := by
  rw [← indicatorConstLp_univ, ← indicatorConstLp_univ]
  exact pullbackL2_indicatorConstLp η 𝕜 m hm .univ (measure_ne_top _ _) c

/-- Pullback along the identity map is the canonical measure-transport equivalence along
`Measure.map_id`. -/
theorem pullbackL2_id (η : Measure Y) (𝕜 E : Type*) [NormedRing 𝕜] [NormedAddCommGroup E]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    pullbackL2 η 𝕜 (E := E) id measurable_id =
      (TauCeti.castLpₗᵢ (𝕜 := 𝕜) (E := E) (p := 2) (Measure.map_id (μ := η)) :
        Lp E 2 (η.map id) →L[𝕜] Lp E 2 η) := by
  ext1 g
  rw [pullbackL2_apply, Lp.compMeasurePreserving_castLpₗᵢ_eq 𝕜 (Measure.map_id (μ := η)) id
    (measurable_id.measurePreserving η) (MeasurePreserving.id η) g,
    Lp.compMeasurePreserving_id_apply, LinearIsometryEquiv.coe_coe'']

/-- Pullback along a composite map factors as composition of the two pullbacks after transporting
along `Measure.map_map`. -/
theorem pullbackL2_comp {Z : Type*} [MeasurableSpace Z] (η : Measure Y) (𝕜 E : Type*)
    [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    {m₁ : Y → X} (hm₁ : Measurable m₁) {m₂ : X → Z} (hm₂ : Measurable m₂) :
    pullbackL2 η 𝕜 (E := E) (m₂ ∘ m₁) (hm₂.comp hm₁) =
      pullbackL2 η 𝕜 m₁ hm₁ ∘L pullbackL2 (η.map m₁) 𝕜 m₂ hm₂ ∘L
        (TauCeti.castLpₗᵢ (𝕜 := 𝕜) (E := E) (p := 2) (Measure.map_map (μ := η) hm₂ hm₁).symm :
          Lp E 2 (η.map (m₂ ∘ m₁)) →L[𝕜] Lp E 2 ((η.map m₁).map m₂)) := by
  ext1 g
  simp only [ContinuousLinearMap.comp_apply, pullbackL2_apply]
  rw [Lp.compMeasurePreserving_castLpₗᵢ_eq 𝕜 (Measure.map_map (μ := η) hm₂ hm₁).symm (m₂ ∘ m₁)
    ((hm₂.comp hm₁).measurePreserving η)
    ((hm₂.measurePreserving (η.map m₁)).comp (hm₁.measurePreserving η)) g,
    Lp.compMeasurePreserving_comp_apply _ (hm₂.measurePreserving (η.map m₁))
      (hm₁.measurePreserving η), LinearIsometryEquiv.coe_coe'']

/-- `pullbackL2` preserves integrals for arbitrary measures. -/
@[simp]
theorem integral_pullbackL2 (η : Measure Y) (𝕜 : Type*) {E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [NormedSpace ℝ E]
    (m : Y → X) (hm : Measurable m) (g : Lp E 2 (η.map m)) :
    ∫ y, pullbackL2 η 𝕜 m hm g y ∂η = ∫ x, g x ∂η.map m := by
  rw [integral_congr_ae (coeFn_pullbackL2 η 𝕜 m hm g)]
  exact (integral_map hm.aemeasurable (Lp.aestronglyMeasurable g)).symm

end NormedModule

section InnerProduct

/-- `pullbackL2` preserves `L²` inner products. -/
@[simp]
theorem inner_pullbackL2 (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (m : Y → X) (hm : Measurable m)
    (g₁ g₂ : Lp E 2 (η.map m)) :
    ⟪pullbackL2 η 𝕜 m hm g₁, pullbackL2 η 𝕜 m hm g₂⟫_𝕜 = ⟪g₁, g₂⟫_𝕜 := by
  rw [pullbackL2_def, LinearIsometry.coe_toContinuousLinearMap]
  exact (Lp.compMeasurePreservingₗᵢ 𝕜 m (hm.measurePreserving η)).inner_map_map g₁ g₂

end InnerProduct

end PullbackL2

section CondExpOperator

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The conditional expectation operator `Lp E 2 η →L[𝕜] Lp E 2 (η.map m)` given `m`, defined for
an arbitrary measure `η` as the Hilbert-space adjoint of `pullbackL2`. -/
def condExpOperator (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (m : Y → X) (hm : Measurable m) :
    Lp E 2 η →L[𝕜] Lp E 2 (η.map m) :=
  ContinuousLinearMap.adjoint (pullbackL2 η 𝕜 m hm)

theorem condExpOperator_def (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (m : Y → X) (hm : Measurable m) :
    condExpOperator η 𝕜 (E := E) m hm = ContinuousLinearMap.adjoint (pullbackL2 η 𝕜 m hm) :=
  (rfl)

/-- Conditional expectation along the identity map is the canonical measure-transport equivalence
along `(Measure.map_id).symm`. -/
theorem condExpOperator_id (η : Measure Y) (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    condExpOperator η 𝕜 (E := E) id measurable_id =
      (TauCeti.castLpₗᵢ (𝕜 := 𝕜) (E := E) (p := 2) (Measure.map_id (μ := η)).symm :
        Lp E 2 η →L[𝕜] Lp E 2 (η.map id)) := by
  rw [condExpOperator_def, pullbackL2_id, LinearIsometryEquiv.adjoint_eq_symm,
    TauCeti.castLpₗᵢ_symm]

/-- Conditional expectation along a composite map factors in the same order as the measurable maps
(`m₁` then `m₂`, opposite to the pullbacks), transported along `Measure.map_map`. -/
theorem condExpOperator_comp {Z : Type*} [MeasurableSpace Z] (η : Measure Y) (𝕜 E : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {m₁ : Y → X} (hm₁ : Measurable m₁) {m₂ : X → Z} (hm₂ : Measurable m₂) :
    condExpOperator η 𝕜 (E := E) (m₂ ∘ m₁) (hm₂.comp hm₁) =
      (TauCeti.castLpₗᵢ (𝕜 := 𝕜) (E := E) (p := 2) (Measure.map_map (μ := η) hm₂ hm₁) :
          Lp E 2 ((η.map m₁).map m₂) →L[𝕜] Lp E 2 (η.map (m₂ ∘ m₁))) ∘L
        condExpOperator (η.map m₁) 𝕜 m₂ hm₂ ∘L condExpOperator η 𝕜 m₁ hm₁ := by
  simp_rw [condExpOperator_def]
  rw [pullbackL2_comp, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm, TauCeti.castLpₗᵢ_symm, ContinuousLinearMap.comp_assoc]

/-- Adjoint identity for `condExpOperator` on the right argument of the inner product. -/
theorem inner_condExpOperator_right (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (m : Y → X) (hm : Measurable m) (g : Lp E 2 (η.map m)) (b : Lp E 2 η) :
    ⟪g, condExpOperator η 𝕜 m hm b⟫_𝕜 = ⟪pullbackL2 η 𝕜 m hm g, b⟫_𝕜 := by
  rw [condExpOperator_def]
  exact ContinuousLinearMap.adjoint_inner_right (pullbackL2 η 𝕜 m hm) g b

/-- Adjoint identity for `condExpOperator` on the left argument of the inner product. -/
theorem inner_condExpOperator_left (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (m : Y → X) (hm : Measurable m) (b : Lp E 2 η) (g : Lp E 2 (η.map m)) :
    ⟪condExpOperator η 𝕜 m hm b, g⟫_𝕜 = ⟪b, pullbackL2 η 𝕜 m hm g⟫_𝕜 := by
  rw [condExpOperator_def]
  exact ContinuousLinearMap.adjoint_inner_left (pullbackL2 η 𝕜 m hm) g b

/-- `condExpOperator` is a left inverse of `pullbackL2`. -/
@[simp]
theorem condExpOperator_comp_pullbackL2 (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (m : Y → X) (hm : Measurable m) :
    condExpOperator η 𝕜 (E := E) m hm ∘L pullbackL2 η 𝕜 m hm = ContinuousLinearMap.id 𝕜 _ := by
  rw [condExpOperator_def, pullbackL2_def, LinearIsometry.adjoint_comp_self,
    ContinuousLinearMap.one_def]

/-- Applying `condExpOperator` after `pullbackL2` recovers the original element of
`Lp E 2 (η.map m)`. -/
@[simp]
theorem condExpOperator_pullbackL2 (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (m : Y → X) (hm : Measurable m) (g : Lp E 2 (η.map m)) :
    condExpOperator η 𝕜 m hm (pullbackL2 η 𝕜 m hm g) = g :=
  DFunLike.congr_fun (condExpOperator_comp_pullbackL2 η 𝕜 m hm) g

/-- `condExpOperator` is surjective onto `Lp E 2 (η.map m)`. -/
theorem condExpOperator_surjective (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (m : Y → X) (hm : Measurable m) :
    Function.Surjective (condExpOperator η 𝕜 (E := E) m hm) :=
  Function.LeftInverse.surjective (condExpOperator_pullbackL2 η 𝕜 m hm)

/-- `condExpOperator` is a contraction: its operator norm is at most `1`. -/
theorem norm_condExpOperator_le_one (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (m : Y → X) (hm : Measurable m) :
    ‖condExpOperator η 𝕜 (E := E) m hm‖ ≤ 1 := by
  rw [condExpOperator_def, LinearIsometryEquiv.norm_map, pullbackL2_def]
  exact LinearIsometry.norm_toContinuousLinearMap_le (𝕜 := 𝕜) (𝕜₂ := 𝕜) _

/-- `condExpOperator` does not increase `L²` norms. -/
theorem norm_condExpOperator_apply_le (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (m : Y → X) (hm : Measurable m) (b : Lp E 2 η) :
    ‖condExpOperator η 𝕜 m hm b‖ ≤ ‖b‖ :=
  (ContinuousLinearMap.le_opNorm _ b).trans
    (mul_le_of_le_one_left (norm_nonneg b) (norm_condExpOperator_le_one η 𝕜 m hm))

/-- The range of `pullbackL2` consists of the `L²` functions almost everywhere strongly measurable
with respect to `σ(m)`. -/
theorem range_pullbackL2 (η : Measure Y) (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (m : Y → X) (hm : Measurable m) :
    (pullbackL2 η 𝕜 (E := E) m hm).range =
      lpMeas E 𝕜 (MeasurableSpace.comap m inferInstance) 2 η := by
  ext u
  rw [LinearMap.mem_range, mem_lpMeas_iff_aestronglyMeasurable,
    ← Lp.mem_range_compMeasurePreservingₗᵢ_iff 𝕜 (hm.measurePreserving η), LinearMap.mem_range]
  simp only [pullbackL2_def, ContinuousLinearMap.coe_coe,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.coe_toLinearMap]

/-- Applying `pullbackL2` to `condExpOperator η 𝕜 m hm b` yields Mathlib's `L²` conditional
expectation given `σ(m)`, for an arbitrary measure `η`. -/
theorem pullbackL2_condExpOperator_eq_condExpL2 (η : Measure Y) (𝕜 : Type*) {E : Type*}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (m : Y → X) (hm : Measurable m) (b : Lp E 2 η) :
    pullbackL2 η 𝕜 m hm (condExpOperator η 𝕜 m hm b) =
      (condExpL2 E 𝕜 hm.comap_le b : Lp E 2 η) := by
  have : Fact (MeasurableSpace.comap m inferInstance ≤ _) := ⟨hm.comap_le⟩
  have hproj := ContinuousLinearMap.comp_adjoint_eq_starProjection_range
    (isometry_pullbackL2 η 𝕜 (E := E) m hm)
  have hb := congr($hproj b)
  rw [ContinuousLinearMap.comp_apply, ← condExpOperator_def] at hb
  rw [hb, condExpL2, ← Submodule.starProjection_apply]
  simp only [range_pullbackL2]

/-- For an integrable `L²` function `b` and a σ-finite conditioning measure `η.trim hm.comap_le`,
applying `pullbackL2` to `condExpOperator η 𝕜 m hm b` yields the conditional expectation
`η[b | σ(m)]` almost everywhere. -/
theorem pullbackL2_condExpOperator_ae_eq (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E]
    (m : Y → X) (hm : Measurable m) [SigmaFinite (η.trim hm.comap_le)]
    (b : Lp E 2 η) (hb : Integrable (b : Y → E) η) :
    (pullbackL2 η 𝕜 m hm (condExpOperator η 𝕜 m hm b) : Y → E) =ᵐ[η]
      η[(b : Y → E) | MeasurableSpace.comap m inferInstance] := by
  have h := (Lp.memLp b).condExpL2_ae_eq_condExp' (𝕜 := 𝕜) hm.comap_le hb
  rw [Lp.toLp_coeFn] at h
  rw [pullbackL2_condExpOperator_eq_condExpL2]
  exact h

/-- On a finite measure space, applying `pullbackL2` to `condExpOperator η 𝕜 m hm b` yields the
conditional expectation `η[b | σ(m)]` almost everywhere. -/
theorem pullbackL2_condExpOperator_ae_eq_of_isFiniteMeasure (η : Measure Y) [IsFiniteMeasure η]
    (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] (m : Y → X) (hm : Measurable m) (b : Lp E 2 η) :
    (pullbackL2 η 𝕜 m hm (condExpOperator η 𝕜 m hm b) : Y → E) =ᵐ[η]
      η[(b : Y → E) | MeasurableSpace.comap m inferInstance] :=
  pullbackL2_condExpOperator_ae_eq η 𝕜 m hm b ((Lp.memLp b).integrable one_le_two)

/-- `condExpOperator` preserves integrals of integrable `L²` functions when `η.trim hm.comap_le`
is σ-finite. -/
theorem integral_condExpOperator (η : Measure Y) (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E]
    (m : Y → X) (hm : Measurable m) [SigmaFinite (η.trim hm.comap_le)]
    (b : Lp E 2 η) (hb : Integrable (b : Y → E) η) :
    ∫ x, condExpOperator η 𝕜 m hm b x ∂η.map m = ∫ y, b y ∂η := by
  calc ∫ x, condExpOperator η 𝕜 m hm b x ∂η.map m
      = ∫ y, pullbackL2 η 𝕜 m hm (condExpOperator η 𝕜 m hm b) y ∂η :=
        (integral_pullbackL2 η 𝕜 m hm _).symm
    _ = ∫ y, η[(b : Y → E) | MeasurableSpace.comap m inferInstance] y ∂η :=
        integral_congr_ae (pullbackL2_condExpOperator_ae_eq η 𝕜 m hm b hb)
    _ = ∫ y, b y ∂η := integral_condExp hm.comap_le

/-- `condExpOperator` preserves integrals on a finite measure space. -/
@[simp]
theorem integral_condExpOperator_of_isFiniteMeasure (η : Measure Y) [IsFiniteMeasure η]
    (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [NormedSpace ℝ E] (m : Y → X) (hm : Measurable m) (b : Lp E 2 η) :
    ∫ x, condExpOperator η 𝕜 m hm b x ∂η.map m = ∫ y, b y ∂η :=
  integral_condExpOperator η 𝕜 m hm b ((Lp.memLp b).integrable one_le_two)

/-- `pullbackL2` preserves and reflects membership in `meanZeroL2`. -/
theorem pullbackL2_mem_meanZeroL2_iff (η : Measure Y) [IsFiniteMeasure η] (𝕜 : Type*)
    {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedSpace ℝ E] (m : Y → X) (hm : Measurable m) {g : Lp E 2 (η.map m)} :
    pullbackL2 η 𝕜 m hm g ∈ meanZeroL2 η 𝕜 ↔ g ∈ meanZeroL2 (η.map m) 𝕜 := by
  simp [mem_meanZeroL2_iff]

/-- `condExpOperator` preserves and reflects membership in `meanZeroL2`. -/
theorem condExpOperator_mem_meanZeroL2_iff (η : Measure Y) [IsFiniteMeasure η] (𝕜 : Type*)
    {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedSpace ℝ E] (m : Y → X) (hm : Measurable m) {b : Lp E 2 η} :
    condExpOperator η 𝕜 m hm b ∈ meanZeroL2 (η.map m) 𝕜 ↔ b ∈ meanZeroL2 η 𝕜 := by
  simp [mem_meanZeroL2_iff]

/-- `condExpOperator` maps `L²₀(η)` onto `L²₀(η.map m)`. -/
theorem map_meanZeroL2_condExpOperator (η : Measure Y) [IsFiniteMeasure η] (𝕜 E : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E]
    (m : Y → X) (hm : Measurable m) :
    (meanZeroL2 η 𝕜 (E := E)).map
        (condExpOperator η 𝕜 (E := E) m hm : Lp E 2 η →ₗ[𝕜] Lp E 2 (η.map m)) =
      meanZeroL2 (η.map m) 𝕜 := by
  have hcomap : meanZeroL2 η 𝕜 (E := E) =
      (meanZeroL2 (η.map m) 𝕜).comap
        (condExpOperator η 𝕜 (E := E) m hm : Lp E 2 η →ₗ[𝕜] Lp E 2 (η.map m)) := by
    ext b
    exact (condExpOperator_mem_meanZeroL2_iff η 𝕜 m hm).symm
  rw [hcomap]
  exact Submodule.map_comap_eq_of_surjective (condExpOperator_surjective η 𝕜 m hm) _

end CondExpOperator

end MeasureTheory.Measure
