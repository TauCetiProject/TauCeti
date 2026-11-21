/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.L2Space.MeanZero
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Pullback isometry on `L²` and its conditional expectation adjoint

For a measurable map `m : Y → X` and a measure `η` on `Y`, composition with `m` defines an
isometric linear map `MeasureTheory.Measure.pullbackL2 η m hm : Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η`.
Its Hilbert-space adjoint
`MeasureTheory.Measure.condExpOperator η m hm : Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m)` is a surjective
contraction that inverts `pullbackL2` on the left, preserves integrals and maps `L²₀(η)` onto
`L²₀(η.map m)` when `η` is finite, and satisfies `pullbackL2 (condExpOperator b) =ᵐ[η] η[b | σ(m)]`.

## Main definitions

* `MeasureTheory.Measure.pullbackL2`: pullback along a measurable map `m : Y → X` as an `L²`
  isometry.
* `MeasureTheory.Measure.condExpOperator`: Hilbert-space adjoint of `pullbackL2` (the conditional
  expectation operator given `m`).

## Main results

* `MeasureTheory.Measure.isometry_pullbackL2`, `MeasureTheory.Measure.norm_pullbackL2`,
  `MeasureTheory.Measure.inner_pullbackL2`: `pullbackL2` is an `L²` isometry.
* `MeasureTheory.Measure.condExpOperator_comp_pullbackL2`,
  `MeasureTheory.Measure.condExpOperator_surjective`,
  `MeasureTheory.Measure.norm_condExpOperator_le_one`: `condExpOperator` is a surjective contraction
  and a left inverse of `pullbackL2`.
* `MeasureTheory.Measure.integral_condExpOperator`, `MeasureTheory.Measure.integral_pullbackL2`,
  `MeasureTheory.Measure.map_meanZeroL2_condExpOperator`: both operators preserve integrals on
  finite measure spaces, and `condExpOperator` maps `L²₀(η)` onto `L²₀(η.map m)`.
* `MeasureTheory.Measure.pullbackL2_condExpOperator_ae_eq`: composing `condExpOperator` with `m`
  yields the conditional expectation given `σ(m)` almost everywhere.
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

/-- `pullbackL2` agrees almost everywhere with precomposition by `m`. -/
theorem coeFn_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (g : Lp ℝ 2 (η.map m)) : (pullbackL2 η m hm g : Y → ℝ) =ᵐ[η] g ∘ m :=
  Lp.coeFn_compMeasurePreserving g (hm.measurePreserving η)

/-- `pullbackL2` is an isometry. -/
theorem isometry_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Isometry (pullbackL2 η m hm) :=
  (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).isometry

/-- `pullbackL2` preserves `L²` norms. -/
@[simp]
theorem norm_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (g : Lp ℝ 2 (η.map m)) : ‖pullbackL2 η m hm g‖ = ‖g‖ :=
  Lp.norm_compMeasurePreserving g (hm.measurePreserving η)

/-- `pullbackL2` preserves `L²` inner products. -/
@[simp]
theorem inner_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (g₁ g₂ : Lp ℝ 2 (η.map m)) :
    ⟪pullbackL2 η m hm g₁, pullbackL2 η m hm g₂⟫_ℝ = ⟪g₁, g₂⟫_ℝ :=
  (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).inner_map_map g₁ g₂

/-- `pullbackL2` maps an indicator function to the indicator of its preimage. -/
theorem pullbackL2_indicatorConstLp (η : Measure Y) (m : Y → X) (hm : Measurable m)
    {s : Set X} (hs : MeasurableSet s) (hμs : (η.map m) s ≠ ∞) (c : ℝ) :
    pullbackL2 η m hm (indicatorConstLp 2 hs hμs c) =
      indicatorConstLp 2 (hm hs)
        (by rwa [(hm.measurePreserving η).measure_preimage hs.nullMeasurableSet]) c :=
  Lp.indicatorConstLp_compMeasurePreserving hs hμs c (hm.measurePreserving η)

/-- `pullbackL2` sends constant functions to constant functions. -/
@[simp]
theorem pullbackL2_const (η : Measure Y) [IsFiniteMeasure η] (m : Y → X) (hm : Measurable m)
    (c : ℝ) : pullbackL2 η m hm (Lp.const 2 (η.map m) c) = Lp.const 2 η c := by
  rw [← indicatorConstLp_univ, ← indicatorConstLp_univ]
  exact pullbackL2_indicatorConstLp η m hm .univ (measure_ne_top _ _) c

/-- The conditional expectation operator `Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m)` given `m`, defined as
the Hilbert-space adjoint of `pullbackL2`. -/
def condExpOperator (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m) :=
  ContinuousLinearMap.adjoint (pullbackL2 η m hm)

theorem condExpOperator_def (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    condExpOperator η m hm = ContinuousLinearMap.adjoint (pullbackL2 η m hm) :=
  (rfl)

/-- Adjoint identity for `condExpOperator` on the right argument of the inner product. -/
theorem inner_condExpOperator_right (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (g : Lp ℝ 2 (η.map m)) (b : Lp ℝ 2 η) :
    ⟪g, condExpOperator η m hm b⟫_ℝ = ⟪pullbackL2 η m hm g, b⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_right (pullbackL2 η m hm) g b

/-- Adjoint identity for `condExpOperator` on the left argument of the inner product. -/
theorem inner_condExpOperator_left (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (b : Lp ℝ 2 η) (g : Lp ℝ 2 (η.map m)) :
    ⟪condExpOperator η m hm b, g⟫_ℝ = ⟪b, pullbackL2 η m hm g⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left (pullbackL2 η m hm) g b

/-- `condExpOperator` is a left inverse of `pullbackL2`. -/
@[simp]
theorem condExpOperator_comp_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    condExpOperator η m hm ∘L pullbackL2 η m hm = ContinuousLinearMap.id ℝ _ :=
  (ContinuousLinearMap.isometry_iff_adjoint_comp_self (pullbackL2 η m hm)).mp
    (isometry_pullbackL2 η m hm)

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
  rw [condExpOperator_def, LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g ↦ by
    rw [norm_pullbackL2, one_mul]

/-- `condExpOperator` does not increase `L²` norms. -/
theorem norm_condExpOperator_apply_le (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (b : Lp ℝ 2 η) : ‖condExpOperator η m hm b‖ ≤ ‖b‖ :=
  (ContinuousLinearMap.le_opNorm _ b).trans
    (mul_le_of_le_one_left (norm_nonneg b) (norm_condExpOperator_le_one η m hm))

/-- `condExpOperator` preserves integrals on a finite measure space. -/
@[simp]
theorem integral_condExpOperator (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) (b : Lp ℝ 2 η) :
    ∫ x, condExpOperator η m hm b x ∂η.map m = ∫ y, b y ∂η := by
  calc ∫ x, condExpOperator η m hm b x ∂η.map m
      = ⟪Lp.const 2 (η.map m) (1 : ℝ), condExpOperator η m hm b⟫_ℝ := (L2.inner_const_one _).symm
    _ = ⟪pullbackL2 η m hm (Lp.const 2 (η.map m) (1 : ℝ)), b⟫_ℝ :=
        inner_condExpOperator_right η m hm _ b
    _ = ⟪Lp.const 2 η (1 : ℝ), b⟫_ℝ := by rw [pullbackL2_const]
    _ = ∫ y, b y ∂η := L2.inner_const_one b

/-- `pullbackL2` preserves integrals on a finite measure space. -/
@[simp]
theorem integral_pullbackL2 (η : Measure Y) [IsFiniteMeasure η] (m : Y → X) (hm : Measurable m)
    (g : Lp ℝ 2 (η.map m)) :
    ∫ y, pullbackL2 η m hm g y ∂η = ∫ x, g x ∂η.map m := by
  rw [← integral_condExpOperator η m hm, condExpOperator_pullbackL2]

/-- `condExpOperator` preserves and reflects membership in `meanZeroL2`. -/
theorem condExpOperator_mem_meanZeroL2_iff (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) {b : Lp ℝ 2 η} :
    condExpOperator η m hm b ∈ meanZeroL2 (η.map m) ↔ b ∈ meanZeroL2 η := by
  simp

/-- `condExpOperator` maps `L²₀(η)` onto `L²₀(η.map m)`. -/
theorem map_meanZeroL2_condExpOperator (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) :
    (meanZeroL2 η).map (condExpOperator η m hm : Lp ℝ 2 η →ₗ[ℝ] Lp ℝ 2 (η.map m)) =
      meanZeroL2 (η.map m) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨b, hb, rfl⟩
    exact (condExpOperator_mem_meanZeroL2_iff η m hm).mpr hb
  · intro g hg
    refine ⟨pullbackL2 η m hm g, ?_, condExpOperator_pullbackL2 η m hm g⟩
    simpa only [SetLike.mem_coe, mem_meanZeroL2_iff, integral_pullbackL2] using hg

/-- Composing `condExpOperator` with `m` yields the conditional expectation given `σ(m)` almost
everywhere. -/
theorem pullbackL2_condExpOperator_ae_eq (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) (b : Lp ℝ 2 η) :
    (pullbackL2 η m hm (condExpOperator η m hm b) : Y → ℝ) =ᵐ[η]
      η[(b : Y → ℝ) | MeasurableSpace.comap m inferInstance] := by
  set g := condExpOperator η m hm b
  set f := pullbackL2 η m hm g
  have hmeas : AEStronglyMeasurable[MeasurableSpace.comap m inferInstance] (f : Y → ℝ) η := by
    obtain ⟨g', hg', hgg'⟩ := Lp.aestronglyMeasurable g
    refine ⟨g' ∘ m, hg'.comp_measurable (measurable_iff_comap_le.mpr le_rfl), ?_⟩
    exact (coeFn_pullbackL2 η m hm g).trans
      ((hm.measurePreserving η).quasiMeasurePreserving.ae_eq_comp hgg')
  refine ae_eq_condExp_of_forall_setIntegral_eq hm.comap_le ((Lp.memLp b).integrable one_le_two)
    (fun _ _ _ ↦ ((Lp.memLp f).integrable one_le_two).integrableOn) ?_ hmeas
  rintro _ ⟨t, ht, rfl⟩ _
  have hμt : (η.map m) t ≠ ∞ := measure_ne_top _ _
  have hηt : η (m ⁻¹' t) ≠ ∞ := measure_ne_top _ _
  let u : Lp ℝ 2 (η.map m) := indicatorConstLp 2 ht hμt (1 : ℝ)
  have hu : pullbackL2 η m hm u = indicatorConstLp 2 (hm ht) hηt (1 : ℝ) :=
    pullbackL2_indicatorConstLp η m hm ht hμt (1 : ℝ)
  calc ∫ y in m ⁻¹' t, f y ∂η
      = ⟪indicatorConstLp 2 (hm ht) hηt (1 : ℝ), f⟫_ℝ :=
        (L2.inner_indicatorConstLp_one (hm ht) hηt f).symm
    _ = ⟪pullbackL2 η m hm u, pullbackL2 η m hm g⟫_ℝ := by rw [hu]
    _ = ⟪u, condExpOperator η m hm b⟫_ℝ := inner_pullbackL2 η m hm u g
    _ = ⟪pullbackL2 η m hm u, b⟫_ℝ := inner_condExpOperator_right η m hm u b
    _ = ⟪indicatorConstLp 2 (hm ht) hηt (1 : ℝ), b⟫_ℝ := by rw [hu]
    _ = ∫ y in m ⁻¹' t, b y ∂η := L2.inner_indicatorConstLp_one (hm ht) hηt b

end MeasureTheory.Measure
