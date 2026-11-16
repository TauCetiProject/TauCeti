/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import TauCeti.Statistics.Semiparametric.TangentSpace
import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreservingEquiv

/-!
# Conditional expectation and score operators on `L²`

Given a measurable observation map `m : Y → X` on a measure space `(Y, η)`, precomposition
`pullbackL2 η m hm : Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η` is a linear isometry whose range consists of
the `L²(η)` classes measurable with respect to `MeasurableSpace.comap m inferInstance`. Its
Hilbert-space adjoint `condExpOperator η m hm : Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m)` is the score
operator associated with observing `m` (van der Vaart, *Asymptotic Statistics*, 1998, §25.5,
p. 375): pulling it back along `m` recovers the `L²` conditional expectation `condExpL2`, and hence
the pointwise conditional expectation `η[· | MeasurableSpace.comap m inferInstance]` whenever the
trimmed measure is σ-finite and the integrand is integrable (automatically on any finite measure
space).

This file also specializes the general closed-range and Gram projection formula
(`ContinuousLinearMap.isClosed_range_of_isUnit_adjoint_comp` and
`ContinuousLinearMap.starProjection_range_eq`) to score operators `A : H →L[ℝ] Lp ℝ 2 P` whose
information operator `A† A` is invertible (van der Vaart, §25.2, p. 362).

## Main definitions

* `TauCeti.pullbackL2`: precomposition with a measurable map `m : Y → X` as a continuous linear
  map `Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η`.
* `TauCeti.condExpOperator`: the Hilbert-space adjoint of `pullbackL2`.

## Main results

* `TauCeti.isometry_pullbackL2`, `TauCeti.range_pullbackL2_eq_lpMeas`: `pullbackL2` is an isometry
  with range `lpMeas ℝ ℝ (MeasurableSpace.comap m inferInstance) 2 η`.
* `TauCeti.condExpOperator_comp_pullbackL2`, `TauCeti.condExpOperator_surjective`,
  `TauCeti.norm_condExpOperator_le`: `condExpOperator` is a surjective contraction and left inverse
  of `pullbackL2`.
* `TauCeti.pullbackL2_comp_condExpOperator`, `TauCeti.pullbackL2_condExpOperator_eq_condExpL2`,
  `TauCeti.pullbackL2_condExpOperator_ae_eq`: composing `condExpOperator` with `pullbackL2` gives
  the orthogonal projection onto `σ(m)`-measurable functions, i.e. conditional expectation given
  `m`.
* `TauCeti.integral_condExpOperator`, `TauCeti.condExpOperator_mem_meanZeroL2_iff`,
  `TauCeti.map_meanZeroL2_condExpOperator`: on a finite measure space, `condExpOperator` preserves
  integrals and maps `meanZeroL2 η` onto `meanZeroL2 (η.map m)`.
* `TauCeti.tangentSpace_range_toSubmodule_eq`, `TauCeti.starProjection_tangentSpace_range`: when
  `A† A` is invertible, `tangentSpace P (Set.range A)` equals `A.range` and its orthogonal
  projection is `A (A† A)⁻¹ A†`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

section CondExpOperator

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Precomposition with a measurable map `m : Y → X`, as a continuous linear isometry
`Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η`. -/
def pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η :=
  (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).toContinuousLinearMap

/-- Definitional restatement of `pullbackL2` in terms of `Lp.compMeasurePreservingₗᵢ`. -/
theorem pullbackL2_def (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    pullbackL2 η m hm =
      (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).toContinuousLinearMap :=
  (rfl)

/-- Applying `pullbackL2` is `MeasureTheory.Lp.compMeasurePreserving`. -/
theorem pullbackL2_apply (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (f : Lp ℝ 2 (η.map m)) :
    pullbackL2 η m hm f = Lp.compMeasurePreserving m (hm.measurePreserving η) f :=
  (rfl)

/-- `pullbackL2` acts almost everywhere by precomposition with `m`. -/
theorem coeFn_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (f : Lp ℝ 2 (η.map m)) :
    (pullbackL2 η m hm f : Y → ℝ) =ᵐ[η] (f : X → ℝ) ∘ m :=
  Lp.coeFn_compMeasurePreserving f (hm.measurePreserving η)

/-- `pullbackL2` is an isometry. -/
theorem isometry_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Isometry (pullbackL2 η m hm) :=
  (Lp.compMeasurePreservingₗᵢ ℝ m (hm.measurePreserving η)).isometry

/-- The range of `pullbackL2` is a closed subspace of `Lp ℝ 2 η` and therefore admits an orthogonal
projection. -/
instance (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    (pullbackL2 η m hm).range.HasOrthogonalProjection :=
  have : CompleteSpace (pullbackL2 η m hm).range :=
    (isometry_pullbackL2 η m hm).isClosedEmbedding.isClosed_range.isComplete.completeSpace_coe
  .ofCompleteSpace _

/-- `pullbackL2` sends constant `L²` classes to constant `L²` classes. -/
@[simp]
theorem pullbackL2_const (η : Measure Y) [IsFiniteMeasure η] (m : Y → X) (hm : Measurable m)
    (c : ℝ) : pullbackL2 η m hm (Lp.const 2 (η.map m) c) = Lp.const 2 η c := by
  refine Lp.ext ((coeFn_pullbackL2 η m hm _).trans ?_)
  exact ((hm.measurePreserving η).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_const 2 (η.map m) c)).trans (Lp.coeFn_const 2 η c).symm

/-- The range of `pullbackL2 η m hm` consists precisely of the `Lp ℝ 2 η` classes that are
almost everywhere strongly measurable for `MeasurableSpace.comap m inferInstance`. -/
theorem range_pullbackL2_eq_lpMeas (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    (pullbackL2 η m hm).range = lpMeas ℝ ℝ (MeasurableSpace.comap m inferInstance) 2 η := by
  ext u
  exact (Lp.mem_range_compMeasurePreservingₗᵢ_iff ℝ (hm.measurePreserving η) u).trans
    mem_lpMeas_iff_aestronglyMeasurable.symm

/-- The conditional expectation operator `Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m)` given `m`, defined as
the Hilbert-space adjoint of `pullbackL2`. -/
def condExpOperator (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Lp ℝ 2 η →L[ℝ] Lp ℝ 2 (η.map m) :=
  ContinuousLinearMap.adjoint (pullbackL2 η m hm)

/-- `condExpOperator` is the adjoint of `pullbackL2`. -/
theorem condExpOperator_def (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    condExpOperator η m hm = ContinuousLinearMap.adjoint (pullbackL2 η m hm) :=
  (rfl)

/-- Adjunction defining `condExpOperator` in the right inner-product slot. -/
theorem inner_condExpOperator_right (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (f : Lp ℝ 2 (η.map m)) (b : Lp ℝ 2 η) :
    inner ℝ f (condExpOperator η m hm b) = inner ℝ (pullbackL2 η m hm f) b :=
  ContinuousLinearMap.adjoint_inner_right (pullbackL2 η m hm) f b

/-- Adjunction defining `condExpOperator` in the left inner-product slot. -/
theorem inner_condExpOperator_left (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (b : Lp ℝ 2 η) (f : Lp ℝ 2 (η.map m)) :
    inner ℝ (condExpOperator η m hm b) f = inner ℝ b (pullbackL2 η m hm f) :=
  ContinuousLinearMap.adjoint_inner_left (pullbackL2 η m hm) f b

/-- `condExpOperator` is a left inverse of `pullbackL2`. -/
@[simp]
theorem condExpOperator_comp_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    condExpOperator η m hm ∘L pullbackL2 η m hm =
      ContinuousLinearMap.id ℝ (Lp ℝ 2 (η.map m)) :=
  (ContinuousLinearMap.isometry_iff_adjoint_comp_self (pullbackL2 η m hm)).1
    (isometry_pullbackL2 η m hm)

/-- Pointwise left-inverse identity `condExpOperator (pullbackL2 f) = f`. -/
@[simp]
theorem condExpOperator_pullbackL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (f : Lp ℝ 2 (η.map m)) : condExpOperator η m hm (pullbackL2 η m hm f) = f :=
  congrArg (fun T ↦ T f) (condExpOperator_comp_pullbackL2 η m hm)

/-- `condExpOperator` is surjective. -/
theorem condExpOperator_surjective (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    Function.Surjective (condExpOperator η m hm) :=
  fun f ↦ ⟨pullbackL2 η m hm f, condExpOperator_pullbackL2 η m hm f⟩

/-- `condExpOperator` is a contraction. -/
theorem norm_condExpOperator_le (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    ‖condExpOperator η m hm‖ ≤ 1 := by
  rw [condExpOperator, LinearIsometryEquiv.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ ?_
  rw [one_mul, (isometry_pullbackL2 η m hm).norm_map_of_map_zero (map_zero _)]

/-- Pulling back `condExpOperator` gives the orthogonal projection onto the range of
`pullbackL2`. -/
theorem pullbackL2_comp_condExpOperator (η : Measure Y) (m : Y → X) (hm : Measurable m) :
    pullbackL2 η m hm ∘L condExpOperator η m hm = (pullbackL2 η m hm).range.starProjection :=
  ContinuousLinearMap.comp_adjoint_eq_starProjection_range (isometry_pullbackL2 η m hm)

/-- Pulling back `condExpOperator` along `m` recovers Mathlib's `L²` conditional expectation
`condExpL2` for `MeasurableSpace.comap m inferInstance`, for any measure `η`. -/
theorem pullbackL2_condExpOperator_eq_condExpL2 (η : Measure Y) (m : Y → X) (hm : Measurable m)
    (b : Lp ℝ 2 η) :
    pullbackL2 η m hm (condExpOperator η m hm b) =
      (condExpL2 ℝ ℝ hm.comap_le b : Lp ℝ 2 η) := by
  have : Fact (MeasurableSpace.comap m inferInstance ≤ (inferInstance : MeasurableSpace Y)) :=
    ⟨hm.comap_le⟩
  have hcoe :
      ((condExpL2 ℝ ℝ hm.comap_le b :
          lpMeas ℝ ℝ (MeasurableSpace.comap m inferInstance) 2 η) : Lp ℝ 2 η) =
        (lpMeas ℝ ℝ (MeasurableSpace.comap m inferInstance) 2 η).starProjection b :=
    Submodule.coe_orthogonalProjectionOnto_apply _ b
  have hrange := range_pullbackL2_eq_lpMeas η m hm
  have hcomp := congrArg (fun T ↦ T b) (pullbackL2_comp_condExpOperator η m hm)
  rw [ContinuousLinearMap.comp_apply] at hcomp
  rw [hcomp, hcoe]
  refine (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
  · rw [← hrange]
    exact Submodule.starProjection_apply_mem _ _
  · rw [← hrange]
    exact Submodule.sub_starProjection_mem_orthogonal _

/-- `condExpOperator` is the conditional expectation given `m`, read on the sample space of `m`.
On a finite measure space, both `[SigmaFinite (η.trim hm.comap_le)]` and `hb` hold automatically
(the latter via `(Lp.memLp b).integrable one_le_two`). -/
theorem pullbackL2_condExpOperator_ae_eq (η : Measure Y) (m : Y → X) (hm : Measurable m)
    [SigmaFinite (η.trim hm.comap_le)] (b : Lp ℝ 2 η) (hb : Integrable (b : Y → ℝ) η) :
    (pullbackL2 η m hm (condExpOperator η m hm b) : Y → ℝ) =ᵐ[η]
      η[(b : Y → ℝ) | MeasurableSpace.comap m inferInstance] := by
  have h := (Lp.memLp b).condExpL2_ae_eq_condExp' (𝕜 := ℝ) hm.comap_le hb
  rw [Lp.toLp_coeFn] at h
  rw [pullbackL2_condExpOperator_eq_condExpL2]
  exact h

/-- On a finite measure space, `condExpOperator` preserves integrals. -/
theorem integral_condExpOperator (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) (b : Lp ℝ 2 η) :
    ∫ x, condExpOperator η m hm b x ∂(η.map m) = ∫ y, b y ∂η := by
  rw [← setIntegral_univ, ← L2.inner_indicatorConstLp_one (𝕜 := ℝ) .univ (measure_ne_top _ _),
    indicatorConstLp_univ, inner_condExpOperator_right, pullbackL2_const, ← indicatorConstLp_univ,
    L2.inner_indicatorConstLp_one, setIntegral_univ]

/-- On a finite measure space, `condExpOperator η m hm b` has mean zero if and only if `b` has
mean zero. -/
theorem condExpOperator_mem_meanZeroL2_iff (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) {b : Lp ℝ 2 η} :
    condExpOperator η m hm b ∈ meanZeroL2 (η.map m) ↔ b ∈ meanZeroL2 η := by
  rw [mem_meanZeroL2_iff, mem_meanZeroL2_iff, integral_condExpOperator]

/-- On a finite measure space, `condExpOperator` maps `meanZeroL2 η` onto `meanZeroL2 (η.map m)`. -/
theorem map_meanZeroL2_condExpOperator (η : Measure Y) [IsFiniteMeasure η] (m : Y → X)
    (hm : Measurable m) :
    (meanZeroL2 η).map (condExpOperator η m hm : Lp ℝ 2 η →ₗ[ℝ] Lp ℝ 2 (η.map m)) =
      meanZeroL2 (η.map m) := by
  ext f
  simp only [Submodule.mem_map, ContinuousLinearMap.coe_coe]
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨b, hb, rfl⟩
    exact (condExpOperator_mem_meanZeroL2_iff η m hm).2 hb
  · refine ⟨pullbackL2 η m hm f, ?_, condExpOperator_pullbackL2 η m hm f⟩
    rw [← condExpOperator_mem_meanZeroL2_iff η m hm, condExpOperator_pullbackL2]
    exact hf

end CondExpOperator

section ScoreOperator

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- If a score operator `A : H →L[ℝ] Lp ℝ 2 P` has invertible information operator `A† A`, then
its range is closed and coincides with the tangent space `tangentSpace P (Set.range A)`. -/
theorem tangentSpace_range_toSubmodule_eq (P : Measure X) (A : H →L[ℝ] Lp ℝ 2 P)
    (hA : IsUnit (ContinuousLinearMap.adjoint A ∘L A)) :
    (tangentSpace P (Set.range A)).toSubmodule = A.range := by
  have hclosed : IsClosed (A.range : Set (Lp ℝ 2 P)) :=
    ContinuousLinearMap.isClosed_range_of_isUnit_adjoint_comp hA
  have hset : (A.range : Set (Lp ℝ 2 P)) = Set.range A :=
    LinearMap.coe_range (A : H →ₗ[ℝ] Lp ℝ 2 P)
  rw [← hset]
  exact tangentSpace_toSubmodule_eq_self P hclosed

/-- The orthogonal projection onto `tangentSpace P (Set.range A)` for a score operator `A` with
invertible information operator `A† A` is `A (A† A)⁻¹ A†`. -/
theorem starProjection_tangentSpace_range (P : Measure X) (A : H →L[ℝ] Lp ℝ 2 P)
    (hA : IsUnit (ContinuousLinearMap.adjoint A ∘L A)) :
    (tangentSpace P (Set.range A)).toSubmodule.starProjection =
      A ∘L Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A := by
  have : A.range.HasOrthogonalProjection :=
    ContinuousLinearMap.hasOrthogonalProjection_range_of_isUnit_adjoint_comp hA
  have hsub := tangentSpace_range_toSubmodule_eq P A hA
  have aux : ∀ {K : Submodule ℝ (Lp ℝ 2 P)} [K.HasOrthogonalProjection],
      K = A.range →
      K.starProjection =
        A ∘L Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L
          ContinuousLinearMap.adjoint A := by
    rintro _ _ rfl
    exact ContinuousLinearMap.starProjection_range_eq hA
  exact aux hsub

end ScoreOperator

end TauCeti
