/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.TestFunction.Topology
public import TauCeti.RepresentationTheory.Continuous.Integrated.Lie.Basic
import TauCeti.RepresentationTheory.Continuous.StronglyContinuous

/-!
# Continuity of the integrated operator on fixed-support spaces

Let `π` be a strongly continuous representation of a Lie group `G` on a complex Banach space `V`
and `μ` a measure on `G` that is finite on compact sets. For a compact set `C`, the integrated
operator `a ↦ π(a)` is bounded on the test functions supported in `C` by the sup norm, the
fixed-support seminorm of the empty word: `‖π(a)‖ ≤ c · sup |a|`, with `c` the product of a bound
of `‖π y‖` on `C` (Banach–Steinhaus) and `μ(C)`. Hence `a ↦ π(a)` is a continuous linear map from
the fixed-support space of `C` to the bounded operators on `V`.

## Main definitions

* `ContRepresentation.lieIntegratedOperatorCLM`: `a ↦ π(a)` as a continuous linear map on the
  fixed-support space of a compact set.

## Main results

* `ContRepresentation.exists_norm_lieIntegratedOperator_le`: `‖π(a)‖ ≤ c · sup |a|` for test
  functions supported in a compact set.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §2.
-/

public section

noncomputable section

open MeasureTheory Set TauCeti TauCeti.LieTestFunction
open scoped ContDiff Manifold NNReal

namespace ContRepresentation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [MeasurableSpace G] [OpensMeasurableSpace G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  (π : ContRepresentation ℂ G V) (hπ : ∀ v, Continuous fun g ↦ π g v) (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ]

/-- **The integrated operator is bounded by the sup norm on a compact support**: for a compact set
`C` there is `c` with `‖π(a)‖ ≤ c · sup |a|` for every test function `a` supported in `C`. -/
theorem exists_norm_lieIntegratedOperator_le {C : Set G} (hC : IsCompact C) :
    ∃ c : ℝ≥0, ∀ a : LieTestFunction I G, tsupport a ⊆ C →
      ‖lieIntegratedOperator π hπ μ a‖ ≤ c * fixedSupportSeminorm [] a := by
  obtain ⟨M, hM⟩ := exists_norm_le_of_isCompact hπ hC
  refine ⟨(max M 0 * μ.real C).toNNReal, fun a ha ↦ ?_⟩
  have hM' (y : G) (hy : y ∈ C) : ‖(π y : V →L[ℂ] V)‖ ≤ max M 0 :=
    (hM y hy).trans (le_max_left _ _)
  have hK : IsCompact (tsupport a) := a.hasCompactSupport.isCompact
  -- `∫ ‖a‖ ≤ μ(C) · sup |a|`, integrating over the support of `a`.
  have hint : ∫ y, ‖a y‖ ∂μ ≤ μ.real C * fixedSupportSeminorm [] a := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport a) fun y hy ↦ by
      simp [image_eq_zero_of_notMem_tsupport hy]]
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, mul_comm]
    refine (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun y _ ↦ ?_).trans
      (mul_le_mul_of_nonneg_left (measureReal_mono ha hC.measure_lt_top.ne)
        (apply_nonneg _ _))
    simpa using norm_leftDerivWord_le [] a y
  calc ‖lieIntegratedOperator π hπ μ a‖ ≤ max M 0 * ∫ y, ‖a y‖ ∂μ :=
        norm_lieIntegratedOperator_le π hπ μ a ha hM'
    _ ≤ max M 0 * (μ.real C * fixedSupportSeminorm [] a) :=
        mul_le_mul_of_nonneg_left hint (le_max_right _ _)
    _ = _ := by
      rw [Real.coe_toNNReal _ (mul_nonneg (le_max_right _ _) measureReal_nonneg), mul_assoc]

/-- The integrated operator `a ↦ π(a)` as a **continuous linear map on the fixed-support space**
of a compact set `C`. -/
def lieIntegratedOperatorCLM {C : Set G} (hC : IsCompact C) :
    FixedSupport I G C →L[ℂ] V →L[ℂ] V :=
  ⟨(lieIntegratedOperator π hπ μ).comp (FixedSupport.inclusion I G C),
    WithSeminorms.continuous_normedSpace_rng _ (FixedSupport.withSeminorms I G C) _ <| by
      obtain ⟨c, hc⟩ := exists_norm_lieIntegratedOperator_le (I := I) π hπ μ hC
      refine ⟨{[]}, c, fun a ↦ ?_⟩
      simpa [FixedSupport.seminormFamily_apply, NNReal.smul_def] using
        hc _ (FixedSupport.tsupport_inclusion_subset a)⟩

/-- The continuous linear map `lieIntegratedOperatorCLM` evaluates to the integrated operator. -/
@[simp]
theorem lieIntegratedOperatorCLM_apply {C : Set G} (hC : IsCompact C) (a : FixedSupport I G C) :
    lieIntegratedOperatorCLM π hπ μ hC a =
      lieIntegratedOperator π hπ μ (FixedSupport.inclusion I G C a) :=
  (rfl)

end ContRepresentation
