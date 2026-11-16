/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Mean-zero `L²` functions and orthogonal projection off constants

For a finite measure `P` on a measurable space `X`, the closed subspace `L²₀(P)` (`meanZeroL2 P`)
of square-integrable functions with integral zero is the orthogonal complement of the constant
functions in `Lp ℝ 2 P`.

This file establishes the Hilbert-space geometry of `L²₀(P)` following van der Vaart
(*Asymptotic Statistics*, 1998, §25.2, pp. 360–362):

* `TauCeti.meanZeroL2`: the orthogonal complement of `{1}` in `Lp ℝ 2 P`.
* `TauCeti.mem_meanZeroL2_iff`: `f ∈ meanZeroL2 P ↔ ∫ x, f x ∂P = 0`.
* `TauCeti.isCompl_span_const_meanZeroL2`: `Lp ℝ 2 P` decomposes as `span {1} ⊕ L²₀(P)`.
* `TauCeti.starProjection_meanZeroL2_eq_sub_average` and
  `TauCeti.starProjection_meanZeroL2_apply`: orthogonal projection onto `L²₀(P)` subtracts the
  average `⨍ x, f x ∂P` (and the integral `∫ x, f x ∂P` when `P` is a probability measure).
* `TauCeti.norm_sub_const_integral_sq` and `TauCeti.norm_starProjection_meanZeroL2_sq`: the squared
  `L²` norm of the centered function is the variance `ProbabilityTheory.variance f P`.
* `TauCeti.closure_bounded_meanZeroL2` and `TauCeti.closure_boundedContinuous_meanZeroL2`: bounded
  mean-zero functions, and on a normal Borel space with weakly regular `P` bounded continuous
  mean-zero functions, are dense in `L²₀(P)`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] (P : Measure X)

/-- The closed subspace `L²₀(P)` of mean-zero elements of `Lp ℝ 2 P`, defined as the orthogonal
complement of the constant functions. -/
def meanZeroL2 [IsFiniteMeasure P] : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)})ᗮ

/-- Definitional restatement of `meanZeroL2 P` as the orthogonal complement of `{1}`. -/
theorem meanZeroL2_def [IsFiniteMeasure P] :
    meanZeroL2 P = (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)})ᗮ :=
  (rfl)

/-- `meanZeroL2 P` is a closed subspace of `Lp ℝ 2 P`. -/
theorem isClosed_meanZeroL2 [IsFiniteMeasure P] :
    IsClosed (meanZeroL2 P : Set (Lp ℝ 2 P)) :=
  Submodule.isClosed_orthogonal _

/-- As a closed subspace of the Hilbert space `Lp ℝ 2 P`, `meanZeroL2 P` is complete and therefore
admits an orthogonal projection. -/
instance [IsFiniteMeasure P] : CompleteSpace (meanZeroL2 P) :=
  (isClosed_meanZeroL2 P).isComplete.completeSpace_coe

/-- An element of `Lp ℝ 2 P` lies in `meanZeroL2 P` if and only if its integral vanishes. -/
@[simp]
theorem mem_meanZeroL2_iff [IsFiniteMeasure P] {f : Lp ℝ 2 P} :
    f ∈ meanZeroL2 P ↔ ∫ x, f x ∂P = 0 := by
  rw [meanZeroL2, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hinner : inner ℝ (Lp.const 2 P (1 : ℝ)) f = ∫ x, f x ∂P := by
    rw [← indicatorConstLp_univ, L2.inner_indicatorConstLp_one, setIntegral_univ]
  rw [hinner]

/-- `Lp ℝ 2 P` decomposes as the orthogonal direct sum of the constants and `meanZeroL2 P`. -/
theorem isCompl_span_const_meanZeroL2 [IsFiniteMeasure P] :
    IsCompl (Submodule.span ℝ {Lp.const 2 P (1 : ℝ)}) (meanZeroL2 P) :=
  Submodule.isCompl_orthogonal _

/-- The orthogonal projection onto `meanZeroL2 P` subtracts the average `⨍ x, f x ∂P`. -/
theorem starProjection_meanZeroL2_eq_sub_average [IsFiniteMeasure P] (f : Lp ℝ 2 P) :
    (meanZeroL2 P).starProjection f = f - Lp.const 2 P (⨍ x, f x ∂P) := by
  by_cases hP : P = 0
  · subst hP
    apply Lp.ext
    rw [ae_zero]
    exact Filter.eventually_bot
  have : NeZero P := ⟨hP⟩
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · rw [mem_meanZeroL2_iff]
    have hf : Integrable (f : X → ℝ) P := (Lp.memLp f).integrable one_le_two
    have hsub : (fun x ↦ (f - Lp.const 2 P (⨍ y, f y ∂P)) x) =ᵐ[P]
        fun x ↦ f x - ⨍ y, f y ∂P := by
      filter_upwards [Lp.coeFn_sub f (Lp.const 2 P (⨍ y, f y ∂P)),
        Lp.coeFn_const 2 P (⨍ y, f y ∂P)] with x h₁ h₂
      rw [h₁, Pi.sub_apply, h₂]
      rfl
    rw [integral_congr_ae hsub, integral_sub hf (integrable_const _), integral_const, smul_eq_mul,
      average_eq, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ measureReal_univ_pos.ne', one_mul,
      sub_self]
  · rw [sub_sub_cancel]
    have hmem : Lp.const 2 P (⨍ x, f x ∂P) ∈ Submodule.span ℝ {Lp.const 2 P (1 : ℝ)} := by
      have hsmul : (⨍ x, f x ∂P) • Lp.const 2 P (1 : ℝ) = Lp.const 2 P (⨍ x, f x ∂P) := by
        rw [← Lp.constL_apply 2 P ℝ, ← map_smul, smul_eq_mul, mul_one, Lp.constL_apply]
      rw [← hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    exact Submodule.le_orthogonal_orthogonal _ hmem

/-- On a probability space, the orthogonal projection onto `meanZeroL2 P` subtracts the mean
`∫ x, f x ∂P`. -/
theorem starProjection_meanZeroL2_apply [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    (meanZeroL2 P).starProjection f = f - Lp.const 2 P (∫ x, f x ∂P) := by
  rw [starProjection_meanZeroL2_eq_sub_average, average_eq_integral]

/-- For a finite measure `P`, the squared `L²` distance from `f` to the constant `∫ x, f x ∂P`
equals `ProbabilityTheory.variance f P`. -/
theorem norm_sub_const_integral_sq [IsFiniteMeasure P] (f : Lp ℝ 2 P) :
    ‖f - Lp.const 2 P (∫ x, f x ∂P)‖ ^ 2 = variance (f : X → ℝ) P := by
  rw [variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable,
    ← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub f (Lp.const 2 P (∫ x, f x ∂P)),
    Lp.coeFn_const 2 P (∫ x, f x ∂P)] with x h₁ h₂
  simp only [h₁, Pi.sub_apply, h₂, Function.const_apply, RCLike.inner_apply,
    conj_trivial, ← sq]

/-- On a probability space, the squared `L²` norm of the projection of `f` onto `meanZeroL2 P` is
the variance of `f`. -/
theorem norm_starProjection_meanZeroL2_sq [IsProbabilityMeasure P] (f : Lp ℝ 2 P) :
    ‖(meanZeroL2 P).starProjection f‖ ^ 2 = variance (f : X → ℝ) P := by
  rw [starProjection_meanZeroL2_apply, norm_sub_const_integral_sq]

private theorem closure_eq_meanZeroL2_of_dense [IsFiniteMeasure P]
    {S T : Set (Lp ℝ 2 P)} (hS : Dense S) (hT : T ⊆ meanZeroL2 P)
    (hproj : ∀ u ∈ S, (meanZeroL2 P).starProjection u ∈ T) :
    closure T = meanZeroL2 P := by
  refine subset_antisymm ((isClosed_meanZeroL2 P).closure_subset_iff.2 hT) fun v hv ↦ ?_
  have hv' : v ∈ (meanZeroL2 P).starProjection '' closure S := by
    rw [hS.closure_eq]
    exact ⟨v, Set.mem_univ v, Submodule.starProjection_eq_self_iff.2 hv⟩
  exact closure_mono (Set.image_subset_iff.2 hproj)
    (image_closure_subset_closure_image (meanZeroL2 P).starProjection.continuous hv')

/-- Bounded mean-zero elements are dense in `meanZeroL2 P`. -/
theorem closure_bounded_meanZeroL2 [IsFiniteMeasure P] :
    closure {u : Lp ℝ 2 P | u ∈ meanZeroL2 P ∧ ∃ C, ∀ᵐ x ∂P, |u x| ≤ C} = meanZeroL2 P := by
  refine closure_eq_meanZeroL2_of_dense P (Lp.simpleFunc.dense (by simp))
    (fun _ h ↦ h.1) fun u hu ↦ ⟨Submodule.starProjection_apply_mem _ _, ?_⟩
  let s : SimpleFunc X ℝ := Lp.simpleFunc.toSimpleFunc ⟨u, hu⟩
  refine ⟨(∑ y ∈ s.range, |y|) + |⨍ x, u x ∂P|, ?_⟩
  rw [starProjection_meanZeroL2_eq_sub_average]
  filter_upwards [Lp.coeFn_sub u (Lp.const 2 P (⨍ x, u x ∂P)),
    Lp.coeFn_const 2 P (⨍ x, u x ∂P),
    Lp.simpleFunc.toSimpleFunc_eq_toFun (⟨u, hu⟩ : Lp.simpleFunc ℝ 2 P)] with x h₁ h₂ h₃
  rw [h₁, Pi.sub_apply, h₂, Function.const_apply, ← h₃]
  refine (abs_sub _ _).trans ?_
  gcongr
  exact Finset.single_le_sum (fun _ _ ↦ abs_nonneg _) (s.mem_range_self x)

/-- On a normal space with its Borel σ-algebra and a weakly regular finite measure `P`, bounded
continuous mean-zero functions are dense in `meanZeroL2 P`. -/
theorem closure_boundedContinuous_meanZeroL2 [TopologicalSpace X] [NormalSpace X]
    [BorelSpace X] [IsFiniteMeasure P] [P.WeaklyRegular] :
    closure {u : Lp ℝ 2 P | u ∈ meanZeroL2 P ∧ ∃ g : X →ᵇ ℝ, (u : X → ℝ) =ᵐ[P] g} =
      meanZeroL2 P := by
  refine closure_eq_meanZeroL2_of_dense P
    (BoundedContinuousFunction.toLp_denseRange ℝ P ℝ (by simp))
    (fun _ h ↦ h.1) ?_
  rintro _ ⟨g, rfl⟩
  set u := BoundedContinuousFunction.toLp 2 P ℝ g
  set c := ⨍ x, u x ∂P
  refine ⟨Submodule.starProjection_apply_mem _ _, g - BoundedContinuousFunction.const X c, ?_⟩
  rw [starProjection_meanZeroL2_eq_sub_average]
  filter_upwards [Lp.coeFn_sub u (Lp.const 2 P c),
    BoundedContinuousFunction.coeFn_toLp 2 P ℝ g,
    Lp.coeFn_const 2 P c] with x h₁ h₂ h₃
  rw [h₁, Pi.sub_apply, h₂, h₃]
  rfl

end TauCeti
