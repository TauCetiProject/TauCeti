/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import TauCeti.MeasureTheory.Function.L2Space.MeanZero
import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.MeasureTheory.Function.L2Space.Basic
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv

/-!
# Pullback isometry on `L²` and its conditional expectation adjoint

For a measurable map `m : Y → X` and an arbitrary measure `η` on `Y`, composition with `m` defines
an isometric linear map `MeasureTheory.Measure.pullbackL2 η m hm : Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η`.
Its Hilbert-space adjoint
`MeasureTheory.Measure.condExpOperator η m hm : Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m)` is defined for an
arbitrary measure `η` as a surjective contraction that inverts `pullbackL2` on the left; both
operators satisfy identity and composition laws up to the canonical pushforward measure transports.

For arbitrary `η`, `pullbackL2` preserves integrals and `pullbackL2 (condExpOperator b)` agrees
with Mathlib's `L²` conditional expectation `condExpL2`. When the trimmed measure
`η.trim hm.comap_le` is σ-finite and `b` is integrable (in particular, for every `b` when `η` is a
finite measure), `condExpOperator` preserves integrals and satisfies
`pullbackL2 (condExpOperator b) =ᵐ[η] η[b | σ(m)]`. On finite measure spaces, `condExpOperator`
maps `L²₀(η)` onto `L²₀(η.map m)`.

## Main definitions

* `MeasureTheory.Measure.pullbackL2`: pullback along a measurable map `m : Y → X` as an `L²`
  isometry.
* `MeasureTheory.Measure.condExpOperator`: Hilbert-space adjoint of `pullbackL2` for an arbitrary
  measure `η` (the conditional expectation operator given `m`).

## Main results

* `MeasureTheory.Measure.isometry_pullbackL2`, `MeasureTheory.Measure.norm_pullbackL2`,
  `MeasureTheory.Measure.inner_pullbackL2`: `pullbackL2` is an `L²` isometry.
* `MeasureTheory.Measure.pullbackL2_id`, `MeasureTheory.Measure.pullbackL2_comp`,
  `MeasureTheory.Measure.condExpOperator_id`, `MeasureTheory.Measure.condExpOperator_comp`:
  operator-level identity and composition laws incorporating `Measure.map_id` and `Measure.map_map`.
* `MeasureTheory.Measure.condExpOperator_comp_pullbackL2`,
  `MeasureTheory.Measure.condExpOperator_surjective`,
  `MeasureTheory.Measure.norm_condExpOperator_le_one`: `condExpOperator` is a surjective contraction
  and a left inverse of `pullbackL2`.
* `MeasureTheory.Measure.pullbackL2_condExpOperator_eq_condExpL2`,
  `MeasureTheory.Measure.pullbackL2_condExpOperator_ae_eq`,
  `MeasureTheory.Measure.pullbackL2_condExpOperator_ae_eq_of_isFiniteMeasure`: composing
  `condExpOperator` with `m` equals `condExpL2` for arbitrary `η`, and yields `η[b | σ(m)]` almost
  everywhere for integrable `b` when `η.trim hm.comap_le` is σ-finite (in particular for finite
  `η`).
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

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Composition with a measurable map `m : Y → X`, as an isometry `Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η`.
-/
def pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η :=
  (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).toContinuousLinearMap

theorem pullbackL2_def (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    pullbackL2 η m hm =
      (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).toContinuousLinearMap :=
  (rfl)

private theorem pullbackL2_apply (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (g : Lp ℝ 2 (η.map m)) :
    pullbackL2 η m hm g = Lp.compMeasurePreserving m (hm.measurePreserving η) g := by
  rw [pullbackL2_def, LinearIsometry.coe_toContinuousLinearMap, Lp.compMeasurePreservingₗᵢ_apply]

/-- `pullbackL2` agrees almost everywhere with precomposition by `m`. -/
theorem coeFn_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (g : Lp ℝ 2 (η.map m)) : (pullbackL2 η m hm g : Y → ℝ) =ᵐ[η] g ∘ m := by
  rw [pullbackL2_apply]
  exact Lp.coeFn_compMeasurePreserving g (hm.measurePreserving η)

/-- `pullbackL2` is an isometry. -/
theorem isometry_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Isometry (pullbackL2 η m hm) := by
  rw [pullbackL2_def, LinearIsometry.coe_toContinuousLinearMap]
  exact (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).isometry

/-- `pullbackL2` preserves `L²` norms. -/
@[simp]
theorem norm_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (g : Lp ℝ 2 (η.map m)) : ‖pullbackL2 η m hm g‖ = ‖g‖ := by
  rw [pullbackL2_apply]
  exact Lp.norm_compMeasurePreserving g (hm.measurePreserving η)

/-- `pullbackL2` preserves `L²` inner products. -/
@[simp]
theorem inner_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (g₁ g₂ : Lp ℝ 2 (η.map m)) :
    ⟪pullbackL2 η m hm g₁, pullbackL2 η m hm g₂⟫_ℝ = ⟪g₁, g₂⟫_ℝ := by
  rw [pullbackL2_def, LinearIsometry.coe_toContinuousLinearMap]
  exact (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).inner_map_map g₁ g₂

/-- `pullbackL2` maps an indicator function to the indicator of its preimage. -/
theorem pullbackL2_indicatorConstLp (η : Measure Y) (m : Y → X) (hm : Measurable m)
    {s : Set X} (hs : MeasurableSet s) (hμs : (η.map m) s ≠ ∞) (c : ℝ) :
    pullbackL2 η m hm (indicatorConstLp 2 hs hμs c) =
      indicatorConstLp 2 (hm hs)
        (by rwa [(hm.measurePreserving η).measure_preimage hs.nullMeasurableSet]) c := by
  rw [pullbackL2_apply]
  exact Lp.indicatorConstLp_compMeasurePreserving hs hμs c (hm.measurePreserving η)

/-- `pullbackL2` sends constant functions to constant functions. -/
@[simp]
theorem pullbackL2_const (η : Measure Y) [IsFiniteMeasure η] (m : Y → X) (hm : Measurable m)
    (c : ℝ) : pullbackL2 η m hm (Lp.const 2 (η.map m) c) = Lp.const 2 η c := by
  rw [← indicatorConstLp_univ, ← indicatorConstLp_univ]
  exact pullbackL2_indicatorConstLp η m hm .univ (measure_ne_top _ _) c

private theorem eqRec_clm_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ₁ μ₂ : Measure X} (h : μ₁ = μ₂) (S : Lp ℝ 2 μ₂ →L[ℝ] E) (T : Lp ℝ 2 μ₁ →L[ℝ] E)
    (hST : ∀ g : Lp ℝ 2 μ₁, T g = S (h ▸ g)) :
    T = h.symm ▸ S := by
  subst h
  exact ContinuousLinearMap.ext hST

private theorem coeFn_eqRec_lp {μ₁ μ₂ : Measure X} (h : μ₁ = μ₂) (g : Lp ℝ 2 μ₁) :
    ((h ▸ g : Lp ℝ 2 μ₂) : X → ℝ) =ᵐ[μ₂] (g : X → ℝ) := by
  subst h
  rfl

/-- Pullback along the identity map is the identity operator on `L²`, transported along
`Measure.map_id`. -/
theorem pullbackL2_id (η : Measure Y) :
    pullbackL2 η id measurable_id =
      (Measure.map_id (μ := η)).symm ▸ ContinuousLinearMap.id ℝ (Lp ℝ 2 η) := by
  refine eqRec_clm_eq Measure.map_id _ _ fun g ↦ Lp.ext ?_
  exact (coeFn_pullbackL2 η id measurable_id g).trans (coeFn_eqRec_lp Measure.map_id g).symm

/-- Pullback along a composite map factors as composition of the two pullbacks, transported along
`Measure.map_map`. -/
theorem pullbackL2_comp {Z : Type*} [MeasurableSpace Z] (η : Measure Y)
    {m₁ : Y → X} (hm₁ : Measurable m₁) {m₂ : X → Z} (hm₂ : Measurable m₂) :
    pullbackL2 η (m₂ ∘ m₁) (hm₂.comp hm₁) =
      Measure.map_map hm₂ hm₁ ▸ (pullbackL2 η m₁ hm₁ ∘L pullbackL2 (η.map m₁) m₂ hm₂) := by
  refine eqRec_clm_eq (Measure.map_map hm₂ hm₁).symm _ _ fun g ↦ Lp.ext ?_
  simp only [ContinuousLinearMap.comp_apply]
  refine (coeFn_pullbackL2 η (m₂ ∘ m₁) (hm₂.comp hm₁) g).trans ?_
  refine Filter.EventuallyEq.trans ?_ (coeFn_pullbackL2 η m₁ hm₁ _).symm
  have h2 : (pullbackL2 (η.map m₁) m₂ hm₂ ((Measure.map_map hm₂ hm₁).symm ▸ g) : X → ℝ) =ᵐ[η.map m₁]
      (g : Z → ℝ) ∘ m₂ :=
    (coeFn_pullbackL2 (η.map m₁) m₂ hm₂ _).trans
      ((hm₂.measurePreserving (η.map m₁)).quasiMeasurePreserving.ae_eq_comp
        (coeFn_eqRec_lp (Measure.map_map hm₂ hm₁).symm g))
  exact ((hm₁.measurePreserving η).quasiMeasurePreserving.ae_eq_comp h2).symm

/-- The conditional expectation operator `Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m)` given `m`, defined for
an arbitrary measure `η` as the Hilbert-space adjoint of `pullbackL2`. -/
def condExpOperator (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m) :=
  ContinuousLinearMap.adjoint (pullbackL2 η m hm)

theorem condExpOperator_def (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    condExpOperator η m hm = ContinuousLinearMap.adjoint (pullbackL2 η m hm) :=
  (rfl)

private theorem adjoint_eqRec_dom {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {μ₁ μ₂ : Measure X} (h : μ₁ = μ₂) (T : Lp ℝ 2 μ₁ →L[ℝ] E) :
    ContinuousLinearMap.adjoint (h ▸ T) = h ▸ ContinuousLinearMap.adjoint T := by
  subst h
  rfl

/-- Conditional expectation along the identity map is the identity operator on `L²`, transported
along `Measure.map_id`. -/
theorem condExpOperator_id (η : Measure Y) :
    condExpOperator η id measurable_id =
      (Measure.map_id (μ := η)).symm ▸ ContinuousLinearMap.id ℝ (Lp ℝ 2 η) := by
  rw [condExpOperator_def, pullbackL2_id, adjoint_eqRec_dom, ContinuousLinearMap.adjoint_id]

/-- Conditional expectation along a composite map factors in reverse order as the composition of the
two conditional expectation operators, transported along `Measure.map_map`. -/
theorem condExpOperator_comp {Z : Type*} [MeasurableSpace Z] (η : Measure Y)
    {m₁ : Y → X} (hm₁ : Measurable m₁) {m₂ : X → Z} (hm₂ : Measurable m₂) :
    condExpOperator η (m₂ ∘ m₁) (hm₂.comp hm₁) =
      Measure.map_map hm₂ hm₁ ▸
        (condExpOperator (η.map m₁) m₂ hm₂ ∘L condExpOperator η m₁ hm₁) := by
  rw [condExpOperator_def, pullbackL2_comp, adjoint_eqRec_dom,
    ContinuousLinearMap.adjoint_comp, condExpOperator_def, condExpOperator_def]

/-- Adjoint identity for `condExpOperator` on the right argument of the inner product. -/
theorem inner_condExpOperator_right (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (g : Lp ℝ 2 (η.map m)) (b : Lp ℝ 2 η) :
    ⟪g, condExpOperator η m hm b⟫_ℝ = ⟪pullbackL2 η m hm g, b⟫_ℝ := by
  rw [condExpOperator_def]
  exact ContinuousLinearMap.adjoint_inner_right (pullbackL2 η m hm) g b

/-- Adjoint identity for `condExpOperator` on the left argument of the inner product. -/
theorem inner_condExpOperator_left (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (b : Lp ℝ 2 η) (g : Lp ℝ 2 (η.map m)) :
    ⟪condExpOperator η m hm b, g⟫_ℝ = ⟪b, pullbackL2 η m hm g⟫_ℝ := by
  rw [condExpOperator_def]
  exact ContinuousLinearMap.adjoint_inner_left (pullbackL2 η m hm) g b

/-- `condExpOperator` is a left inverse of `pullbackL2`. -/
@[simp]
theorem condExpOperator_comp_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    condExpOperator η m hm ∘L pullbackL2 η m hm = ContinuousLinearMap.id ℝ _ := by
  rw [condExpOperator_def, pullbackL2_def, LinearIsometry.adjoint_comp_self,
    ContinuousLinearMap.one_def]

/-- Applying `condExpOperator` after `pullbackL2` recovers the original element of
`Lp ℝ 2 (η.map m)`. -/
@[simp]
theorem condExpOperator_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (g : Lp ℝ 2 (η.map m)) : condExpOperator η m hm (pullbackL2 η m hm g) = g :=
  DFunLike.congr_fun (condExpOperator_comp_pullbackL2 η m hm) g

/-- `condExpOperator` is surjective onto `Lp ℝ 2 (η.map m)`. -/
theorem condExpOperator_surjective (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Function.Surjective (condExpOperator η m hm) :=
  Function.LeftInverse.surjective (condExpOperator_pullbackL2 η m hm)

/-- `condExpOperator` is a contraction: its operator norm is at most `1`. -/
theorem norm_condExpOperator_le_one (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    ‖condExpOperator η m hm‖ ≤ 1 := by
  rw [condExpOperator_def, LinearIsometryEquiv.norm_map, pullbackL2_def]
  exact LinearIsometry.norm_toContinuousLinearMap_le (𝕜 := ℝ) (𝕜₂ := ℝ) _

/-- `condExpOperator` does not increase `L²` norms. -/
theorem norm_condExpOperator_apply_le (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (b : Lp ℝ 2 η) : ‖condExpOperator η m hm b‖ ≤ ‖b‖ :=
  (ContinuousLinearMap.le_opNorm _ b).trans
    (mul_le_of_le_one_left (norm_nonneg b) (norm_condExpOperator_le_one η m hm))

/-- `pullbackL2` preserves integrals for arbitrary measures. -/
@[simp]
theorem integral_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (g : Lp ℝ 2 (η.map m)) :
    ∫ y, pullbackL2 η m hm g y ∂η = ∫ x, g x ∂η.map m := by
  rw [integral_congr_ae (coeFn_pullbackL2 η m hm g)]
  exact (integral_map hm.aemeasurable (Lp.aestronglyMeasurable g)).symm

/-- Composing `condExpOperator` with `m` yields Mathlib's `L²` conditional expectation given
`σ(m)`, for an arbitrary measure `η`. -/
theorem pullbackL2_condExpOperator_eq_condExpL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (b : Lp ℝ 2 η) :
    pullbackL2 η m hm (condExpOperator η m hm b) =
      (condExpL2 ℝ ℝ hm.comap_le b : Lp ℝ 2 η) := by
  have : Fact (MeasurableSpace.comap m inferInstance ≤ (inferInstance : MeasurableSpace Y)) :=
    ⟨hm.comap_le⟩
  have hrange : (pullbackL2 η m hm).range =
      lpMeas ℝ ℝ (MeasurableSpace.comap m inferInstance) 2 η := by
    ext u
    rw [mem_lpMeas_iff_aestronglyMeasurable,
      ← Lp.mem_range_compMeasurePreservingₗᵢ_iff (𝕜 := ℝ) (hm.measurePreserving η), pullbackL2_def]
    rfl
  let := ContinuousLinearMap.hasOrthogonalProjection_range_of_isUnit_adjoint_comp
    ((ContinuousLinearMap.isometry_iff_adjoint_comp_self _).1 (isometry_pullbackL2 η m hm) ▸
      isUnit_one)
  have hproj : pullbackL2 η m hm (condExpOperator η m hm b) =
      (pullbackL2 η m hm).range.starProjection b := by
    simpa only [condExpOperator_def, ContinuousLinearMap.comp_apply] using
      congr($(ContinuousLinearMap.comp_adjoint_eq_starProjection_range
        (isometry_pullbackL2 η m hm)) b)
  rw [hproj]
  simp_rw [hrange]
  rfl

/-- For an integrable `L²` function `b` and a σ-finite conditioning measure `η.trim hm.comap_le`,
composing `condExpOperator` with `m` yields the conditional expectation `η[b | σ(m)]` almost
everywhere. -/
theorem pullbackL2_condExpOperator_ae_eq (η : Measure Y) (m : Y → X) (hm : Measurable m)
    [SigmaFinite (η.trim hm.comap_le)] (b : Lp ℝ 2 η) (hb : Integrable (b : Y → ℝ) η) :
    (pullbackL2 η m hm (condExpOperator η m hm b) : Y → ℝ) =ᵐ[η]
      η[(b : Y → ℝ) | MeasurableSpace.comap m inferInstance] := by
  have h := (Lp.memLp b).condExpL2_ae_eq_condExp' (𝕜 := ℝ) hm.comap_le hb
  rw [Lp.toLp_coeFn] at h
  rw [pullbackL2_condExpOperator_eq_condExpL2]
  exact h

/-- On a finite measure space, composing `condExpOperator` with `m` yields the conditional
expectation `η[b | σ(m)]` almost everywhere. -/
theorem pullbackL2_condExpOperator_ae_eq_of_isFiniteMeasure (η : Measure Y) [IsFiniteMeasure η]
    (m : Y → X) (hm : Measurable m) (b : Lp ℝ 2 η) :
    (pullbackL2 η m hm (condExpOperator η m hm b) : Y → ℝ) =ᵐ[η]
      η[(b : Y → ℝ) | MeasurableSpace.comap m inferInstance] :=
  pullbackL2_condExpOperator_ae_eq η m hm b ((Lp.memLp b).integrable one_le_two)

/-- `condExpOperator` preserves integrals of integrable `L²` functions when `η.trim hm.comap_le`
is σ-finite. -/
theorem integral_condExpOperator (η : Measure Y) (m : Y → X) (hm : Measurable m)
    [SigmaFinite (η.trim hm.comap_le)] (b : Lp ℝ 2 η) (hb : Integrable (b : Y → ℝ) η) :
    ∫ x, condExpOperator η m hm b x ∂η.map m = ∫ y, b y ∂η := by
  calc ∫ x, condExpOperator η m hm b x ∂η.map m
      = ∫ y, pullbackL2 η m hm (condExpOperator η m hm b) y ∂η :=
        (integral_pullbackL2 η m hm _).symm
    _ = ∫ y, η[(b : Y → ℝ) | MeasurableSpace.comap m inferInstance] y ∂η :=
        integral_congr_ae (pullbackL2_condExpOperator_ae_eq η m hm b hb)
    _ = ∫ y, b y ∂η := integral_condExp hm.comap_le

/-- `condExpOperator` preserves integrals on a finite measure space. -/
@[simp]
theorem integral_condExpOperator_of_isFiniteMeasure (η : Measure Y) [IsFiniteMeasure η]
    (m : Y → X) (hm : Measurable m) (b : Lp ℝ 2 η) :
    ∫ x, condExpOperator η m hm b x ∂η.map m = ∫ y, b y ∂η :=
  integral_condExpOperator η m hm b ((Lp.memLp b).integrable one_le_two)

/-- `pullbackL2` preserves and reflects membership in `meanZeroL2`. -/
theorem pullbackL2_mem_meanZeroL2_iff (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) {g : Lp ℝ 2 (η.map m)} :
    pullbackL2 η m hm g ∈ meanZeroL2 η ↔ g ∈ meanZeroL2 (η.map m) := by
  simp [mem_meanZeroL2_iff]

/-- `condExpOperator` preserves and reflects membership in `meanZeroL2`. -/
theorem condExpOperator_mem_meanZeroL2_iff (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) {b : Lp ℝ 2 η} :
    condExpOperator η m hm b ∈ meanZeroL2 (η.map m) ↔ b ∈ meanZeroL2 η := by
  simp [mem_meanZeroL2_iff]

/-- `condExpOperator` maps `L²₀(η)` onto `L²₀(η.map m)`. -/
theorem map_meanZeroL2_condExpOperator (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) :
    (meanZeroL2 η).map (condExpOperator η m hm : Lp ℝ 2 η →ₗ[ℝ] Lp ℝ 2 (η.map m)) =
      meanZeroL2 (η.map m) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨b, hb, rfl⟩
    exact (condExpOperator_mem_meanZeroL2_iff η m hm).mpr hb
  · intro g hg
    exact ⟨pullbackL2 η m hm g, (pullbackL2_mem_meanZeroL2_iff η m hm).mpr hg,
      condExpOperator_pullbackL2 η m hm g⟩

end MeasureTheory.Measure
