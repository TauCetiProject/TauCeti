/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.Intertwiner
public import TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1

/-!
# Bochner `L¹` intertwiners, uniqueness, and commutants

This file extends `TauCeti.Analysis.CStarAlgebra.Action.Covariant.Intertwiner` and
`TauCeti.Analysis.CStarAlgebra.Action.Covariant.L1` to the Bochner `L¹` integrated form
`CovariantRepresentation.integratedOperatorBochnerL1`:

* `CovariantRepresentation.comp_integratedOperatorBochnerL1` and
  `CovariantRepresentation.comp_integratedOperatorBochnerL1_iff`: intertwining of covariant pairs
  expressed through `integratedOperatorBochnerL1`.
* `CovariantRepresentation.ext_integratedOperatorBochnerL1`: uniqueness of a nondegenerate
  covariant pair determined by `integratedOperatorBochnerL1`.
* `CovariantRepresentation.centralizer_range_integratedOperatorBochnerL1`: equality of the
  commutant of `integratedOperatorBochnerL1` and the joint commutant of the covariant pair.

## References

* Dana P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs,
  vol. 134, American Mathematical Society (2007), Chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace TauCeti.CStarAction.CovariantRepresentation

variable {G A H K : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {α : CStarAction G A}

/-- A bounded operator intertwining two covariant pairs intertwines their
`integratedOperatorBochnerL1` forms. -/
theorem comp_integratedOperatorBochnerL1 [R1Space G] (μ : Measure G) [μ.InnerRegularCompactLTTop]
    {P : CovariantRepresentation α H} {Q : CovariantRepresentation α K} {T : H →L[ℂ] K}
    (hπ : ∀ a, T ∘L P.coefficient a = Q.coefficient a ∘L T)
    (hU : ∀ g, T ∘L P.group g = Q.group g ∘L T) (u : Lp A 1 μ) :
    T ∘L P.integratedOperatorBochnerL1 μ u = Q.integratedOperatorBochnerL1 μ u ∘L T := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, integratedOperatorBochnerL1_apply]
  rw [← T.integral_comp_comm (P.integrable_integrand_of_integrable (L1.integrable_coeFn u) v)]
  refine integral_congr_ae (.of_forall fun g => ?_)
  dsimp only
  rw [← ContinuousLinearMap.comp_apply T, hπ, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.comp_apply T, hU, ContinuousLinearMap.comp_apply]

section Nondegenerate

variable [IsTopologicalGroup G] [LocallyCompactSpace G] (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ] [μ.InnerRegularCompactLTTop] [μ.IsMulLeftInvariant]
  [μ.IsOpenPosMeasure]

/-- For a nondegenerate source pair, intertwining `integratedOperatorBochnerL1` is equivalent to
intertwining both the coefficient and group representations. -/
theorem comp_integratedOperatorBochnerL1_iff
    {P : CovariantRepresentation α H} {Q : CovariantRepresentation α K}
    (hP : P.coefficient.IsNondegenerate) {T : H →L[ℂ] K} :
    (∀ u, T ∘L P.integratedOperatorBochnerL1 μ u = Q.integratedOperatorBochnerL1 μ u ∘L T) ↔
      (∀ a, T ∘L P.coefficient a = Q.coefficient a ∘L T) ∧
        ∀ g, T ∘L P.group g = Q.group g ∘L T :=
  ⟨fun h => (comp_integratedOperator_iff μ hP).1 fun f => by
    simpa only [integratedOperatorBochnerL1_toLp] using
      h (CompactlySupportedContinuousMap.toLp 1 μ ℂ f),
    fun h => comp_integratedOperatorBochnerL1 μ h.1 h.2⟩

/-- A nondegenerate covariant pair is uniquely determined by `integratedOperatorBochnerL1`. -/
theorem ext_integratedOperatorBochnerL1 {P Q : CovariantRepresentation α H}
    (hP : P.coefficient.IsNondegenerate)
    (h : P.integratedOperatorBochnerL1 μ = Q.integratedOperatorBochnerL1 μ) : P = Q :=
  ext_integratedOperator μ hP fun f => by
    simpa only [integratedOperatorBochnerL1_toLp] using
      congrArg (fun L => L (CompactlySupportedContinuousMap.toLp 1 μ ℂ f)) h

/-- For a nondegenerate pair, the commutant of `integratedOperatorBochnerL1` equals the joint
commutant of `P.coefficient` and `P.group`. -/
theorem centralizer_range_integratedOperatorBochnerL1 {P : CovariantRepresentation α H}
    (hP : P.coefficient.IsNondegenerate) :
    Set.centralizer (Set.range (P.integratedOperatorBochnerL1 μ)) =
      Set.centralizer (Set.range P.coefficient ∪ Set.range P.group) := by
  ext T
  have h := comp_integratedOperatorBochnerL1_iff μ hP (Q := P) (T := T)
  simp only [← ContinuousLinearMap.mul_def] at h
  simp only [Set.mem_centralizer_iff, Set.mem_union, or_imp, forall_and, Set.forall_mem_range]
  simpa only [eq_comm (a := T * _)] using h

end Nondegenerate

end TauCeti.CStarAction.CovariantRepresentation
