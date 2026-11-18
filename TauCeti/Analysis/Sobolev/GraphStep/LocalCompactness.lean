/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.Analysis.Sobolev.W1p.LocalCompactness
public import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional

/-!
# Vector-valued local Rellich compactness

For a finite-dimensional target, restriction of a weakly differentiable `Lᵖ` field to an open
set compactly contained in its domain is compact for every `1 ≤ p ≤ ∞`. No boundary condition or
boundedness of the ambient domain is required. The graph-space version retains an arbitrary
preceding space and field-selection map, so it also applies to higher weak-derivative steps.

`TauCeti.WeakDerivStep.restrictBaseL` restricts the selected field, and
`TauCeti.WeakDerivStep.isCompactOperator_restrictBaseL` proves its compactness. The proof
projects to scalar coordinates using `toW1pL`, applies
`TauCeti.W1p.isCompactOperator_valueL_restrictL`, and reconstructs the field in a finite basis
through `TauCeti.isCompactOperator_of_forall_isCompactOperator_compLpL_comp`.
Finite dimensionality of the target is essential: constant fields valued in an infinite
orthonormal sequence already obstruct local norm compactness.

In particular this supplies compact restriction of `W^{1,2}(ℝ,F)` paths to bounded intervals
(`TauCeti.WeakDerivStep.isCompactOperator_smul_restrictBaseL`), the compact error term in the
Fredholm estimates for first-order trajectory operators.

## Reference

H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Theorem 9.16 (Rellich--Kondrachov); the vector-valued extension is coordinatewise.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

variable {E F X : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega V : Opens E}
  {p : ENNReal} [Fact (1 ≤ p)]

/-- Restriction to a compactly contained open subset is compact for a finite-dimensional target
and `1 ≤ p ≤ ∞`. The preceding space need not be complete. -/
theorem isCompactOperator_restrictBaseL [FiniteDimensional ℝ F]
    (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (hVc : IsCompact (closure (V : Set E))) (hVO : closure (V : Set E) ⊆ Omega) :
    IsCompactOperator (restrictBaseL base (SetLike.coe_subset_coe.mp
      (subset_closure.trans hVO))) := by
  let hV : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVO)
  refine isCompactOperator_of_forall_isCompactOperator_compLpL_comp ℝ fun ℓ ↦ ?_
  have heq : (ℓ.compLpL p (mu.restrict V)).comp (restrictBaseL base hV) =
      ((W1p.valueL (mu := mu) (Omega := V) (p := p)).comp (W1p.restrictL hV)).comp
        (toW1pL base ℓ) := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, W1p.valueL_apply]
    refine ((ℓ.coeFn_compLpL (restrictBaseL base hV u)).trans
      ((restrictBaseL_apply_ae base hV u).fun_comp ℓ)).trans ?_
    refine Filter.EventuallyEq.trans ?_ (W1p.value_restrictL_ae hV _).symm
    rw [value_toW1pL]
    exact (ℓ.coeFn_compLpL (base (prev base u))).symm.filter_mono
      (ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hV)))
  rw [← ContinuousLinearMap.coe_comp, heq]
  exact (W1p.isCompactOperator_valueL_restrictL hVc hVO).comp_clm (toW1pL base ℓ)

/-- Restriction of `W^{1,2}(ℝ, F)` paths to a bounded interval, scaled by a constant, is
compact. -/
theorem isCompactOperator_smul_restrictBaseL [FiniteDimensional ℝ F] (K R : ℝ) :
    IsCompactOperator (K • restrictBaseL
      (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))
      (V := ⟨Ioo (-R) R, isOpen_Ioo⟩) le_top) := by
  rw [FunLike.coe_smul]
  exact (isCompactOperator_restrictBaseL _
    (Metric.isBounded_Ioo (-R) R).isCompact_closure (by simp)).smul K

end TauCeti.WeakDerivStep
