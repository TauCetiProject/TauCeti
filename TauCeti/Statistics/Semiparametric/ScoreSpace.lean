/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.Probability.Moments.Variance

/-!
# Hilbert geometry of score spaces

This file develops the Hilbert-space geometry of score functions in `Lp ℝ 2 P` underlying
semiparametric efficiency theory:

* **Mean-zero `L²` and constants:** `TauCeti.meanZeroL2 P` is the closed subspace `L²₀(P)` of
  square-integrable real functions with integral zero, defined as the orthogonal complement of the
  constants. It complements the constant functions, orthogonal projection onto `L²₀(P)` subtracts
  the average (the mean when `P` is a probability measure) with squared norm equal to the variance,
  and both bounded measurable and (on a normal Borel space with a weakly regular measure) bounded
  continuous mean-zero functions are dense in `L²₀(P)`.
* **Tangent spaces:** `TauCeti.tangentSpace P T` is the closed linear span of a tangent set
  `T ⊆ Lp ℝ 2 P` as a `ClosedSubmodule`. It satisfies the universal property of the smallest closed
  submodule containing `T`, sends unions to joins in `ClosedSubmodule`, and reduces to an algebraic
  orthogonal sum with additive orthogonal projections when the two tangent spaces are orthogonal.
* **Efficient scores and information matrices:** `TauCeti.efficientScore P N ℓ` is the residual of
  a score `ℓ` after orthogonal projection onto the nuisance tangent space `tangentSpace P N`.
  `TauCeti.informationMatrix P ℓ` and `TauCeti.efficientInformationMatrix P N ℓ` are the Gram
  matrices of the scores and of the efficient scores. Enlarging the nuisance set decreases the
  efficient information matrix in the Loewner order, yielding the information-loss inequality
  `I - I_eff ≥ 0`, the adaptation criterion `I_eff = I` iff every score is orthogonal to `N`, and
  positive definiteness iff the efficient scores are linearly independent.
* **Conditional expectation and score operators:** `TauCeti.pullbackL2 η m hm` is composition with
  a measurable map `m : Y → X` as an isometry `Lp ℝ 2 (η.map m) →L[ℝ] Lp ℝ 2 η`, and
  `TauCeti.condExpOperator η m hm` is its Hilbert-space adjoint. The adjoint is a surjective
  contraction that inverts the pullback on the left, maps `L²₀(η)` onto `L²₀(η.map m)`, and
  satisfies `pullbackL2 (condExpOperator b) =ᵐ η[b | σ(m)]`. For a continuous linear score
  operator `A : H →L[ℝ] Lp ℝ 2 P` with invertible Gram operator `A† A`, the orthogonal projection
  onto `tangentSpace P (Set.range A)` is `A (A† A)⁻¹ A†`.

## Main definitions

* `TauCeti.meanZeroL2`: the closed subspace `L²₀(P)` of mean-zero elements of `Lp ℝ 2 P`.
* `TauCeti.tangentSpace`: the closed linear span of a set of scores in `Lp ℝ 2 P`.
* `TauCeti.efficientScore`: the residual of a score after projection onto a nuisance tangent space.
* `TauCeti.informationMatrix`, `TauCeti.efficientInformationMatrix`: the Gram matrices of a family
  of scores and of their efficient scores.
* `TauCeti.pullbackL2`, `TauCeti.condExpOperator`: pullback along a measurable map on `L²` and its
  adjoint conditional expectation operator.

## Main results

* `TauCeti.starProjection_meanZeroL2`, `TauCeti.norm_starProjection_meanZeroL2_sq`: the orthogonal
  projection onto `L²₀(P)` subtracts the mean, and its squared norm is the variance.
* `TauCeti.meanZeroL2_subset_closure_bounded`,
  `TauCeti.meanZeroL2_subset_closure_boundedContinuous`: density of bounded and bounded continuous
  mean-zero elements in `L²₀(P)`.
* `TauCeti.tangentSpace_union`, `TauCeti.tangentSpace_union_toSubmodule_of_isOrtho`,
  `TauCeti.starProjection_tangentSpace_union_of_isOrtho`: tangent space of a union, orthogonal sum
  decomposition, and additivity of projections.
* `TauCeti.posSemidef_efficientInformationMatrix_sub_of_subset`,
  `TauCeti.posSemidef_informationMatrix_sub_efficient`,
  `TauCeti.efficientInformationMatrix_eq_informationMatrix_iff`,
  `TauCeti.posDef_efficientInformationMatrix_iff`: information-loss inequalities, adaptation
  criterion, and nonsingularity criterion.
* `TauCeti.pullbackL2_condExpOperator_ae_eq`, `TauCeti.condExpOperator_comp_pullbackL2`,
  `TauCeti.map_meanZeroL2_condExpOperator`: characterization and mapping properties of the
  conditional expectation operator.
* `TauCeti.starProjection_closure_range_eq`: projection formula `A (A† A)⁻¹ A†` onto the closed
  range of a score operator with invertible `A† A`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §25.2, §25.4,
  §25.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction

namespace TauCeti

/-! ### Mean-zero `L²` and constants -/

section MeanZeroL2

variable {X : Type*} [MeasurableSpace X]

/-- The closed subspace `L²₀(P)` of mean-zero elements of `Lp ℝ 2 P`, defined as the orthogonal
complement of the constant functions. -/
def meanZeroL2 (P : Measure X) [IsFiniteMeasure P] : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)})ᗮ

theorem meanZeroL2_def (P : Measure X) [IsFiniteMeasure P] :
    meanZeroL2 P = (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)})ᗮ :=
  (rfl)

/-- An element of `Lp ℝ 2 P` lies in `meanZeroL2 P` if and only if its integral vanishes. -/
@[simp]
theorem mem_meanZeroL2_iff {P : Measure X} [IsFiniteMeasure P] {f : Lp ℝ 2 P} :
    f ∈ meanZeroL2 P ↔ ∫ x, f x ∂P = 0 := by
  rw [meanZeroL2_def, Submodule.mem_orthogonal_singleton_iff_inner_right,
    ← indicatorConstLp_univ, L2.inner_indicatorConstLp_one, setIntegral_univ]

/-- The mean-zero subspace `L²₀(P)` is closed in `Lp ℝ 2 P`. -/
theorem isClosed_meanZeroL2 (P : Measure X) [IsFiniteMeasure P] :
    IsClosed (meanZeroL2 P : Set (Lp ℝ 2 P)) :=
  Submodule.isClosed_orthogonal _

/-- The mean-zero subspace `L²₀(P)` is complete, and hence admits orthogonal projections. -/
instance completeSpace_meanZeroL2 (P : Measure X) [IsFiniteMeasure P] :
    CompleteSpace (meanZeroL2 P) :=
  (isClosed_meanZeroL2 P).isComplete.completeSpace_coe

/-- `Lp ℝ 2 P` decomposes as the direct sum of the constant functions and `L²₀(P)`. -/
theorem isCompl_span_const_meanZeroL2 (P : Measure X) [IsFiniteMeasure P] :
    IsCompl (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)}) (meanZeroL2 P) := by
  rw [meanZeroL2_def]
  exact Submodule.isCompl_orthogonal _

/-- For a Dirac measure, every mean-zero element of `L²` vanishes. -/
@[simp]
theorem meanZeroL2_dirac (x : X) : meanZeroL2 (Measure.dirac x) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [mem_meanZeroL2_iff] at hf
  obtain ⟨g, hg, hfg⟩ := Lp.aestronglyMeasurable f
  have hgx : g x = 0 := by
    rw [← integral_dirac' g x hg, ← integral_congr_ae hfg]
    exact hf
  have hg0 : g =ᵐ[Measure.dirac x] (0 : X → ℝ) :=
    (ae_dirac_iff (hg.measurable (measurableSet_singleton 0))).mpr hgx
  exact Lp.ext (hfg.trans (hg0.trans (Lp.coeFn_zero ℝ 2 (Measure.dirac x)).symm))

/-- On a finite measure space, the orthogonal projection onto `L²₀(P)` subtracts the `P`-average. -/
theorem starProjection_meanZeroL2_eq_sub_const_average {P : Measure X} [IsFiniteMeasure P]
    (f : Lp ℝ 2 P) :
    (meanZeroL2 P).starProjection f = f - Lp.const 2 P (⨍ x, f x ∂P) := by
  have hinner : ⟪Lp.const 2 P (1 : ℝ), f⟫_ℝ = ∫ x, f x ∂P := by
    rw [← indicatorConstLp_univ, L2.inner_indicatorConstLp_one, setIntegral_univ]
  have hnorm : ‖Lp.const 2 P (1 : ℝ)‖ ^ 2 = P.real Set.univ := by
    rw [Lp.norm_const' 2 P (1 : ℝ) (by norm_num) (by norm_num)]
    simp [← Real.rpow_natCast, ← Real.rpow_mul measureReal_nonneg]
  have hsmul (c : ℝ) : c • Lp.const 2 P (1 : ℝ) = Lp.const 2 P c := by
    simpa [mul_one] using ((Lp.constₗ 2 P ℝ).map_smul c (1 : ℝ)).symm
  dsimp only [meanZeroL2]
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton ℝ f, hinner, hnorm, average_eq, smul_eq_mul,
    ← div_eq_inv_mul, hsmul]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

/-- On a probability space, subtracting the mean yields an element of `L²₀(P)`. -/
theorem sub_const_integral_mem_meanZeroL2 {P : Measure X} [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    f - Lp.const 2 P (∫ x, f x ∂P) ∈ meanZeroL2 P := by
  rw [← average_eq_integral, ← starProjection_meanZeroL2_eq_sub_const_average]
  exact Submodule.starProjection_apply_mem _ _

/-- On a probability space, the orthogonal projection onto `L²₀(P)` subtracts the mean. -/
theorem starProjection_meanZeroL2 {P : Measure X} [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    (meanZeroL2 P).starProjection f = f - Lp.const 2 P (∫ x, f x ∂P) := by
  rw [starProjection_meanZeroL2_eq_sub_const_average, average_eq_integral]

/-- On a probability space, the squared `L²` norm of the projection onto `L²₀(P)` is the
variance. -/
theorem norm_starProjection_meanZeroL2_sq {P : Measure X} [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    ‖(meanZeroL2 P).starProjection f‖ ^ 2 = variance (f : X → ℝ) P := by
  rw [starProjection_meanZeroL2, variance_eq_norm_sub_const_sq]

private theorem meanZeroL2_subset_closure_starProjection_image (P : Measure X) [IsFiniteMeasure P]
    {S : Set (Lp ℝ 2 P)} (hS : Dense S) :
    (meanZeroL2 P : Set (Lp ℝ 2 P)) ⊆ closure ((meanZeroL2 P).starProjection '' S) := by
  intro u hu
  rw [← Submodule.starProjection_eq_self_iff.mpr hu]
  exact image_closure_subset_closure_image (meanZeroL2 P).starProjection.continuous
    ⟨u, hS u, rfl⟩

/-- Bounded mean-zero elements are dense in `L²₀(P)`. -/
theorem meanZeroL2_subset_closure_bounded (P : Measure X) [IsFiniteMeasure P] :
    (meanZeroL2 P : Set (Lp ℝ 2 P)) ⊆
      closure {u | u ∈ meanZeroL2 P ∧ ∃ C, ∀ᵐ x ∂P, |u x| ≤ C} := by
  refine (meanZeroL2_subset_closure_starProjection_image P
    (Lp.simpleFunc.dense (by norm_num))).trans (closure_mono ?_)
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨Submodule.starProjection_apply_mem _ _, ?_⟩
  let s : SimpleFunc X ℝ := Lp.simpleFunc.toSimpleFunc ⟨v, hv⟩
  have hvs : (v : X → ℝ) =ᵐ[P] s := (Lp.simpleFunc.toSimpleFunc_eq_toFun ⟨v, hv⟩).symm
  have hC (x : X) : |s x| ≤ (s.range.sup fun y ↦ ‖y‖₊ : ℝ≥0) := by
    rw [← Real.norm_eq_abs, ← coe_nnNorm]
    exact_mod_cast Finset.le_sup (f := fun y ↦ ‖y‖₊) (s.mem_range_self x)
  refine ⟨(s.range.sup fun y ↦ ‖y‖₊ : ℝ≥0) + |⨍ x, v x ∂P|, ?_⟩
  rw [starProjection_meanZeroL2_eq_sub_const_average]
  filter_upwards [Lp.coeFn_sub v (Lp.const 2 P (⨍ x, v x ∂P)),
    Lp.coeFn_const 2 P (⨍ x, v x ∂P), hvs] with x hsub hc hxs
  rw [hsub, Pi.sub_apply, hc, Function.const_apply, hxs]
  exact (abs_sub (s x) _).trans (add_le_add (hC x) le_rfl)

/-- On a normal space with its Borel σ-algebra and a weakly regular finite measure `P`, bounded
continuous mean-zero functions are dense in `L²₀(P)`. -/
theorem meanZeroL2_subset_closure_boundedContinuous (P : Measure X) [IsFiniteMeasure P]
    [TopologicalSpace X] [NormalSpace X] [BorelSpace X] [P.WeaklyRegular] :
    (meanZeroL2 P : Set (Lp ℝ 2 P)) ⊆
      closure {u | u ∈ meanZeroL2 P ∧ ∃ g : X →ᵇ ℝ, (u : X → ℝ) =ᵐ[P] g} := by
  refine (meanZeroL2_subset_closure_starProjection_image P
    (BoundedContinuousFunction.toLp_denseRange ℝ ℝ (p := 2) (μ := P) (by norm_num))).trans
      (closure_mono ?_)
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  refine ⟨Submodule.starProjection_apply_mem _ _, ?_⟩
  set c := ⨍ x, (BoundedContinuousFunction.toLp 2 P ℝ g : X → ℝ) x ∂P
  refine ⟨g - BoundedContinuousFunction.const X c, ?_⟩
  rw [starProjection_meanZeroL2_eq_sub_const_average]
  filter_upwards [Lp.coeFn_sub (BoundedContinuousFunction.toLp 2 P ℝ g) (Lp.const 2 P c),
    Lp.coeFn_const 2 P c, BoundedContinuousFunction.coeFn_toLp 2 P ℝ g] with x hsub hc hg
  rw [hsub, Pi.sub_apply, hc, Function.const_apply, hg]
  rfl

end MeanZeroL2

/-! ### Tangent spaces -/

section TangentSpace

variable {X : Type*} [MeasurableSpace X]

/-- The tangent space of a tangent set `T ⊆ Lp ℝ 2 P`: the closed linear span of `T`. -/
def tangentSpace (P : Measure X) (T : Set (Lp ℝ 2 P)) : ClosedSubmodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ T).closure

theorem tangentSpace_def {P : Measure X} (T : Set (Lp ℝ 2 P)) :
    tangentSpace P T = (Submodule.span ℝ T).closure :=
  (rfl)

theorem tangentSpace_toSubmodule {P : Measure X} (T : Set (Lp ℝ 2 P)) :
    (tangentSpace P T).toSubmodule = (Submodule.span ℝ T).topologicalClosure :=
  (rfl)

/-- Universal property of `tangentSpace`: `tangentSpace P T` is the smallest closed submodule
containing `T`. -/
theorem tangentSpace_le_iff {P : Measure X} {T : Set (Lp ℝ 2 P)}
    {K : ClosedSubmodule ℝ (Lp ℝ 2 P)} :
    tangentSpace P T ≤ K ↔ T ⊆ K := by
  rw [tangentSpace_def, Submodule.closure_le, Submodule.span_le, ClosedSubmodule.coe_toSubmodule]

/-- Every tangent set is contained in its tangent space. -/
theorem subset_tangentSpace {P : Measure X} (T : Set (Lp ℝ 2 P)) :
    T ⊆ (tangentSpace P T : Set (Lp ℝ 2 P)) :=
  tangentSpace_le_iff.mp le_rfl

/-- Every element of a tangent set belongs to its tangent space. -/
theorem mem_tangentSpace_of_mem {P : Measure X} {T : Set (Lp ℝ 2 P)} {g : Lp ℝ 2 P} (hg : g ∈ T) :
    g ∈ tangentSpace P T :=
  subset_tangentSpace T hg

/-- The tangent space is monotone in the generating set. -/
theorem tangentSpace_mono {P : Measure X} {T T' : Set (Lp ℝ 2 P)} (h : T ⊆ T') :
    tangentSpace P T ≤ tangentSpace P T' :=
  tangentSpace_le_iff.mpr (h.trans (subset_tangentSpace T'))

/-- The tangent space of the empty set is the zero subspace. -/
@[simp]
theorem tangentSpace_empty (P : Measure X) : tangentSpace P ∅ = ⊥ :=
  le_bot_iff.mp (tangentSpace_le_iff.mpr (Set.empty_subset _))

/-- The tangent space of a closed submodule is itself. -/
@[simp]
theorem tangentSpace_coe {P : Measure X} (K : ClosedSubmodule ℝ (Lp ℝ 2 P)) :
    tangentSpace P (K : Set (Lp ℝ 2 P)) = K :=
  le_antisymm (tangentSpace_le_iff.mpr Set.Subset.rfl) (subset_tangentSpace _)

/-- The underlying submodule of the tangent space of a closed submodule is that submodule. -/
theorem tangentSpace_toSubmodule_eq_self {P : Measure X} {K : Submodule ℝ (Lp ℝ 2 P)}
    (hK : IsClosed (K : Set (Lp ℝ 2 P))) :
    (tangentSpace P (K : Set (Lp ℝ 2 P))).toSubmodule = K :=
  congrArg ClosedSubmodule.toSubmodule (tangentSpace_coe ⟨K, hK⟩)

/-- The tangent space of a singleton is its linear span. -/
theorem tangentSpace_singleton_toSubmodule {P : Measure X} (g : Lp ℝ 2 P) :
    (tangentSpace P {g}).toSubmodule = Submodule.span ℝ {g} := by
  rw [tangentSpace_toSubmodule]
  exact (Submodule.span ℝ {g}).isClosed_of_finiteDimensional.submodule_topologicalClosure_eq

/-- If every score in `T` has mean zero, then `tangentSpace P T` is contained in `L²₀(P)`. -/
theorem tangentSpace_le_meanZeroL2 {P : Measure X} [IsFiniteMeasure P] {T : Set (Lp ℝ 2 P)}
    (hT : T ⊆ meanZeroL2 P) : (tangentSpace P T).toSubmodule ≤ meanZeroL2 P :=
  (tangentSpace_le_iff (K := ⟨meanZeroL2 P, isClosed_meanZeroL2 P⟩)).mpr hT

/-- A vector is orthogonal to `tangentSpace P T` if and only if it is orthogonal to every element
of `T`. -/
theorem mem_orthogonal_tangentSpace_iff {P : Measure X} {T : Set (Lp ℝ 2 P)} {f : Lp ℝ 2 P} :
    f ∈ (tangentSpace P T).toSubmoduleᗮ ↔ ∀ g ∈ T, ⟪g, f⟫_ℝ = 0 := by
  rw [tangentSpace_toSubmodule, Submodule.orthogonal_closure,
    ← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le, Submodule.isOrtho_comm,
    Submodule.isOrtho_span]
  simp

/-- Two tangent spaces are orthogonal if and only if every element of the first tangent set is
orthogonal to every element of the second. -/
theorem isOrtho_tangentSpace_iff {P : Measure X} {T T' : Set (Lp ℝ 2 P)} :
    (tangentSpace P T).toSubmodule.IsOrtho (tangentSpace P T').toSubmodule ↔
      ∀ g ∈ T, ∀ g' ∈ T', ⟪g, g'⟫_ℝ = 0 := by
  rw [Submodule.isOrtho_iff_le, tangentSpace_toSubmodule T', Submodule.orthogonal_closure,
    ← Submodule.isOrtho_iff_le, Submodule.isOrtho_comm, Submodule.isOrtho_iff_le,
    tangentSpace_toSubmodule T, Submodule.orthogonal_closure, ← Submodule.isOrtho_iff_le,
    Submodule.isOrtho_comm, Submodule.isOrtho_span]

/-- The tangent space of a union is the join of the two tangent spaces in `ClosedSubmodule` (the
closure of their sum). -/
@[simp]
theorem tangentSpace_union {P : Measure X} (T T' : Set (Lp ℝ 2 P)) :
    tangentSpace P (T ∪ T') = tangentSpace P T ⊔ tangentSpace P T' := by
  refine le_antisymm ?_ (sup_le (tangentSpace_mono Set.subset_union_left)
    (tangentSpace_mono Set.subset_union_right))
  rw [tangentSpace_le_iff]
  exact Set.union_subset
    ((subset_tangentSpace T).trans (SetLike.coe_subset_coe.mpr le_sup_left))
    ((subset_tangentSpace T').trans (SetLike.coe_subset_coe.mpr le_sup_right))

/-- When two tangent spaces are orthogonal, the tangent space of their union is their algebraic
sum. -/
theorem tangentSpace_union_toSubmodule_of_isOrtho {P : Measure X} {T T' : Set (Lp ℝ 2 P)}
    (h : (tangentSpace P T).toSubmodule.IsOrtho (tangentSpace P T').toSubmodule) :
    (tangentSpace P (T ∪ T')).toSubmodule =
      (tangentSpace P T).toSubmodule ⊔ (tangentSpace P T').toSubmodule := by
  rw [tangentSpace_union, ClosedSubmodule.toSubmodule_sup]
  exact h.isClosed_sup.submodule_topologicalClosure_eq

/-- When two tangent spaces are orthogonal, the orthogonal projection onto the tangent space of
their union is the sum of their orthogonal projections. -/
theorem starProjection_tangentSpace_union_of_isOrtho {P : Measure X} {T T' : Set (Lp ℝ 2 P)}
    (h : (tangentSpace P T).toSubmodule.IsOrtho (tangentSpace P T').toSubmodule) :
    (tangentSpace P (T ∪ T')).toSubmodule.starProjection =
      (tangentSpace P T).toSubmodule.starProjection +
        (tangentSpace P T').toSubmodule.starProjection := by
  have := h.hasOrthogonalProjection_sup
  rw [← h.starProjection_sup]
  simp_rw [tangentSpace_union_toSubmodule_of_isOrtho h]

end TangentSpace

/-! ### Efficient scores and information matrices -/

section EfficientScore

variable {X : Type*} [MeasurableSpace X]

/-- The efficient score: the residual of `ℓ` after orthogonal projection onto the nuisance tangent
space generated by `N`. -/
def efficientScore (P : Measure X) (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) : Lp ℝ 2 P :=
  ℓ - (tangentSpace P N).toSubmodule.starProjection ℓ

theorem efficientScore_def {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = ℓ - (tangentSpace P N).toSubmodule.starProjection ℓ :=
  (rfl)

/-- The efficient score is the orthogonal projection of `ℓ` onto the orthogonal complement of the
nuisance tangent space. -/
theorem efficientScore_eq_starProjection_orthogonal {P : Measure X} (N : Set (Lp ℝ 2 P))
    (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = (tangentSpace P N).toSubmoduleᗮ.starProjection ℓ :=
  (Submodule.starProjection_orthogonal_val ℓ).symm

/-- The efficient score is orthogonal to the nuisance tangent space. -/
theorem efficientScore_mem_orthogonal {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ ∈ (tangentSpace P N).toSubmoduleᗮ :=
  Submodule.sub_starProjection_mem_orthogonal ℓ

/-- The efficient score is orthogonal to every element of the nuisance tangent space. -/
theorem inner_efficientScore_eq_zero_of_mem_tangentSpace {P : Measure X} (N : Set (Lp ℝ 2 P))
    (ℓ : Lp ℝ 2 P) {g : Lp ℝ 2 P} (hg : g ∈ tangentSpace P N) :
    ⟪g, efficientScore P N ℓ⟫_ℝ = 0 :=
  Submodule.inner_right_of_mem_orthogonal hg (efficientScore_mem_orthogonal N ℓ)

/-- The efficient score is orthogonal to every nuisance score in `N`. -/
theorem inner_efficientScore_eq_zero_of_mem {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P)
    {g : Lp ℝ 2 P} (hg : g ∈ N) : ⟪g, efficientScore P N ℓ⟫_ℝ = 0 :=
  inner_efficientScore_eq_zero_of_mem_tangentSpace N ℓ (mem_tangentSpace_of_mem hg)

/-- The efficient score equals `ℓ` if and only if `ℓ` is orthogonal to every nuisance score. -/
theorem efficientScore_eq_self_iff {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = ℓ ↔ ∀ g ∈ N, ⟪g, ℓ⟫_ℝ = 0 := by
  rw [efficientScore_def, sub_eq_self, Submodule.starProjection_apply_eq_zero_iff,
    mem_orthogonal_tangentSpace_iff]

/-- The efficient score vanishes if and only if `ℓ` lies in the nuisance tangent space. -/
theorem efficientScore_eq_zero_iff {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N ℓ = 0 ↔ ℓ ∈ tangentSpace P N := by
  rw [efficientScore_def, sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff,
    ClosedSubmodule.mem_toSubmodule_iff]

/-- Taking the efficient score is idempotent. -/
@[simp]
theorem efficientScore_idempotent {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ : Lp ℝ 2 P) :
    efficientScore P N (efficientScore P N ℓ) = efficientScore P N ℓ :=
  (efficientScore_eq_self_iff N _).mpr fun _ hg ↦ inner_efficientScore_eq_zero_of_mem N ℓ hg

/-- The efficient score of `0` is `0`. -/
@[simp]
theorem efficientScore_zero {P : Measure X} (N : Set (Lp ℝ 2 P)) : efficientScore P N 0 = 0 := by
  simp [efficientScore_def]

/-- `efficientScore P N` is additive in the score. -/
theorem efficientScore_add {P : Measure X} (N : Set (Lp ℝ 2 P)) (ℓ₁ ℓ₂ : Lp ℝ 2 P) :
    efficientScore P N (ℓ₁ + ℓ₂) = efficientScore P N ℓ₁ + efficientScore P N ℓ₂ := by
  simp only [efficientScore_eq_starProjection_orthogonal, map_add]

/-- `efficientScore P N` is homogeneous in the score. -/
theorem efficientScore_smul {P : Measure X} (N : Set (Lp ℝ 2 P)) (c : ℝ) (ℓ : Lp ℝ 2 P) :
    efficientScore P N (c • ℓ) = c • efficientScore P N ℓ := by
  simp only [efficientScore_eq_starProjection_orthogonal, map_smul]

/-- With no nuisance scores, the efficient score is the score itself. -/
@[simp]
theorem efficientScore_empty {P : Measure X} (ℓ : Lp ℝ 2 P) : efficientScore P ∅ ℓ = ℓ :=
  (efficientScore_eq_self_iff ∅ ℓ).mpr fun _ h ↦ h.elim

/-- For a single nuisance score `n`, the efficient score is `ℓ - (⟪n, ℓ⟫ / ‖n‖²) n`. -/
theorem efficientScore_singleton {P : Measure X} (n ℓ : Lp ℝ 2 P) :
    efficientScore P {n} ℓ = ℓ - (⟪n, ℓ⟫_ℝ / ‖n‖ ^ 2) • n := by
  rw [efficientScore_def]
  simp_rw [tangentSpace_singleton_toSubmodule n]
  simp [Submodule.starProjection_singleton ℝ ℓ]

/-- If `ℓ` and every nuisance score in `N` have mean zero, then so does the efficient score. -/
theorem efficientScore_mem_meanZeroL2 {P : Measure X} [IsFiniteMeasure P] {N : Set (Lp ℝ 2 P)}
    {ℓ : Lp ℝ 2 P} (hN : N ⊆ meanZeroL2 P) (hℓ : ℓ ∈ meanZeroL2 P) :
    efficientScore P N ℓ ∈ meanZeroL2 P :=
  Submodule.sub_mem _ hℓ
    (tangentSpace_le_meanZeroL2 hN (Submodule.starProjection_apply_mem _ ℓ))

/-- The information matrix `Iᵢⱼ = ⟪ℓᵢ, ℓⱼ⟫` of a family of scores in `Lp ℝ 2 P`. -/
def informationMatrix (P : Measure X) {ι : Type*} (ℓ : ι → Lp ℝ 2 P) : Matrix ι ι ℝ :=
  Matrix.gram ℝ ℓ

theorem informationMatrix_eq_gram {P : Measure X} {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    informationMatrix P ℓ = Matrix.gram ℝ ℓ :=
  (rfl)

@[simp]
theorem informationMatrix_apply {P : Measure X} {ι : Type*} (ℓ : ι → Lp ℝ 2 P) (i j : ι) :
    informationMatrix P ℓ i j = ⟪ℓ i, ℓ j⟫_ℝ :=
  (rfl)

/-- Every information matrix is positive semidefinite. -/
theorem posSemidef_informationMatrix {P : Measure X} {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ).PosSemidef :=
  Matrix.posSemidef_gram ℝ ℓ

/-- The information matrix is positive definite if and only if the scores are linearly
independent. -/
theorem posDef_informationMatrix_iff {P : Measure X} {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ).PosDef ↔ LinearIndependent ℝ ℓ :=
  Matrix.posDef_gram_iff_linearIndependent

/-- The efficient information matrix of a family of scores relative to a nuisance set `N`: the
Gram matrix of the efficient scores `efficientScore P N (ℓ i)`. -/
def efficientInformationMatrix (P : Measure X) {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) : Matrix ι ι ℝ :=
  informationMatrix P (fun i ↦ efficientScore P N (ℓ i))

theorem efficientInformationMatrix_def {P : Measure X} {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ = informationMatrix P (fun i ↦ efficientScore P N (ℓ i)) :=
  (rfl)

@[simp]
theorem efficientInformationMatrix_apply {P : Measure X} {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) (i j : ι) :
    efficientInformationMatrix P N ℓ i j = ⟪efficientScore P N (ℓ i), efficientScore P N (ℓ j)⟫_ℝ :=
  (rfl)

/-- With no nuisance scores, the efficient information matrix equals the information matrix. -/
@[simp]
theorem efficientInformationMatrix_empty {P : Measure X} {ι : Type*} (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P ∅ ℓ = informationMatrix P ℓ := by
  simp [efficientInformationMatrix_def]

/-- Every efficient information matrix is positive semidefinite. -/
theorem posSemidef_efficientInformationMatrix {P : Measure X} {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) : (efficientInformationMatrix P N ℓ).PosSemidef :=
  posSemidef_informationMatrix _

/-- The efficient information matrix is positive definite if and only if the efficient scores are
linearly independent in `Lp ℝ 2 P`. -/
theorem posDef_efficientInformationMatrix_iff {P : Measure X} {ι : Type*} (N : Set (Lp ℝ 2 P))
    (ℓ : ι → Lp ℝ 2 P) :
    (efficientInformationMatrix P N ℓ).PosDef ↔
      LinearIndependent ℝ (fun i ↦ efficientScore P N (ℓ i)) :=
  Matrix.posDef_gram_iff_linearIndependent

/-- Enlarging the nuisance set from `N` to `N'` lowers the efficient information matrix by the Gram
matrix of the projection difference `(Π_{N'} - Π_N) ℓ`. -/
theorem efficientInformationMatrix_sub_of_subset {P : Measure X} {ι : Type*}
    {N N' : Set (Lp ℝ 2 P)} (h : N ⊆ N') (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ =
      Matrix.gram ℝ (fun i ↦ (tangentSpace P N').toSubmodule.starProjection (ℓ i) -
        (tangentSpace P N).toSubmodule.starProjection (ℓ i)) := by
  ext i j
  set K := (tangentSpace P N).toSubmodule
  set K' := (tangentSpace P N').toSubmodule
  have hle : K ≤ K' := tangentSpace_mono h
  have hdiff (k : ι) : K'.starProjection (ℓ k) - K.starProjection (ℓ k) ∈ K' :=
    K'.sub_mem (K'.starProjection_apply_mem _) (hle (K.starProjection_apply_mem _))
  have hsplit (k : ι) : efficientScore P N (ℓ k) =
      efficientScore P N' (ℓ k) + (K'.starProjection (ℓ k) - K.starProjection (ℓ k)) := by
    simp only [efficientScore_def, K, K']
    abel
  have h₁ : ⟪efficientScore P N' (ℓ i),
      K'.starProjection (ℓ j) - K.starProjection (ℓ j)⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (hdiff j) (efficientScore_mem_orthogonal N' (ℓ i))
  have h₂ : ⟪K'.starProjection (ℓ i) - K.starProjection (ℓ i),
      efficientScore P N' (ℓ j)⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (hdiff i) (efficientScore_mem_orthogonal N' (ℓ j))
  simp only [Matrix.sub_apply, efficientInformationMatrix_apply, Matrix.gram_apply]
  conv_lhs => rw [hsplit i, hsplit j]
  rw [inner_add_left, inner_add_right, inner_add_right, h₁, h₂]
  ring

/-- Enlarging the nuisance scores can only lower the efficient information matrix in the Loewner
order. -/
theorem posSemidef_efficientInformationMatrix_sub_of_subset {P : Measure X} {ι : Type*}
    {N N' : Set (Lp ℝ 2 P)} (h : N ⊆ N') (ℓ : ι → Lp ℝ 2 P) :
    (efficientInformationMatrix P N ℓ - efficientInformationMatrix P N' ℓ).PosSemidef := by
  rw [efficientInformationMatrix_sub_of_subset h]
  exact Matrix.posSemidef_gram ℝ _

/-- Information loss: `I - I_eff` is the Gram matrix of the projections of the scores onto the
nuisance tangent space. -/
theorem informationMatrix_sub_efficientInformationMatrix {P : Measure X} {ι : Type*}
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    informationMatrix P ℓ - efficientInformationMatrix P N ℓ =
      Matrix.gram ℝ (fun i ↦ (tangentSpace P N).toSubmodule.starProjection (ℓ i)) := by
  have h := efficientInformationMatrix_sub_of_subset (Set.empty_subset N) ℓ
  simpa only [efficientInformationMatrix_empty, tangentSpace_empty,
    ClosedSubmodule.toSubmodule_bot, Submodule.starProjection_bot, zero_apply, sub_zero] using h

/-- Information loss is positive semidefinite: `I - I_eff ≥ 0`. -/
theorem posSemidef_informationMatrix_sub_efficient {P : Measure X} {ι : Type*}
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    (informationMatrix P ℓ - efficientInformationMatrix P N ℓ).PosSemidef := by
  rw [informationMatrix_sub_efficientInformationMatrix]
  exact Matrix.posSemidef_gram ℝ _

/-- Adaptation criterion: the efficient information matrix equals the full information matrix if
and only if every score coordinate is orthogonal to the nuisance set `N`. -/
theorem efficientInformationMatrix_eq_informationMatrix_iff {P : Measure X} {ι : Type*}
    (N : Set (Lp ℝ 2 P)) (ℓ : ι → Lp ℝ 2 P) :
    efficientInformationMatrix P N ℓ = informationMatrix P ℓ ↔
      ∀ i, ∀ g ∈ N, ⟪g, ℓ i⟫_ℝ = 0 := by
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · have hzero : (informationMatrix P ℓ - efficientInformationMatrix P N ℓ) i i = 0 := by
      rw [h, sub_self, Matrix.zero_apply]
    rw [informationMatrix_sub_efficientInformationMatrix, Matrix.gram_apply,
      inner_self_eq_zero, Submodule.starProjection_apply_eq_zero_iff,
      mem_orthogonal_tangentSpace_iff] at hzero
    exact hzero
  · ext i j
    simp only [efficientInformationMatrix_apply, informationMatrix_apply,
      (efficientScore_eq_self_iff N (ℓ i)).mpr (h i),
      (efficientScore_eq_self_iff N (ℓ j)).mpr (h j)]

end EfficientScore

/-! ### Conditional expectation operator and score operators -/

section ScoreOperators

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
theorem surjective_condExpOperator (η : Measure Y) (m : Y → X) (hm : Measurable m) :
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
      = ⟪Lp.const 2 (η.map m) (1 : ℝ), condExpOperator η m hm b⟫_ℝ := by
        rw [← indicatorConstLp_univ, L2.inner_indicatorConstLp_one, setIntegral_univ]
    _ = ⟪pullbackL2 η m hm (Lp.const 2 (η.map m) (1 : ℝ)), b⟫_ℝ :=
        inner_condExpOperator_right η m hm _ b
    _ = ⟪Lp.const 2 η (1 : ℝ), b⟫_ℝ := by rw [pullbackL2_const]
    _ = ∫ y, b y ∂η := by
        rw [← indicatorConstLp_univ, L2.inner_indicatorConstLp_one, setIntegral_univ]

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

/-- The tangent space of the range of a score operator `A` with invertible Gram operator `A† A`
equals the range of `A`. -/
theorem tangentSpace_range_eq_range {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {P : Measure X} (A : H →L[ℝ] Lp ℝ 2 P)
    (hA : IsUnit (ContinuousLinearMap.adjoint A ∘L A)) :
    (tangentSpace P (Set.range A)).toSubmodule = A.range := by
  have hclosed : IsClosed (A.range : Set (Lp ℝ 2 P)) := by
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
      ContinuousLinearMap.isClosed_range_of_isUnit_adjoint_comp hA
  simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using
    tangentSpace_toSubmodule_eq_self hclosed

/-- The orthogonal projection onto the closed range of a score operator `A` with continuously
invertible information operator `A† A` is `A (A† A)⁻¹ A†`. -/
theorem starProjection_closure_range_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {P : Measure X} (A : H →L[ℝ] Lp ℝ 2 P)
    (hA : IsUnit (ContinuousLinearMap.adjoint A ∘L A)) :
    (tangentSpace P (Set.range A)).toSubmodule.starProjection =
      A ∘L Ring.inverse (ContinuousLinearMap.adjoint A ∘L A) ∘L ContinuousLinearMap.adjoint A := by
  have := ContinuousLinearMap.hasOrthogonalProjection_range_of_isUnit_adjoint_comp hA
  rw [← ContinuousLinearMap.starProjection_range_eq hA]
  simp_rw [tangentSpace_range_eq_range A hA]

end ScoreOperators

end TauCeti
