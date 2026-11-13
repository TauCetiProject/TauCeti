/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional

/-!
# Vector-valued compactness from scalar compactness

If the value map `W^{1,p}(Ω) → Lᵖ(Ω)` is compact, then for a finite-dimensional target `F` the
field selected by a weak-derivative graph space is compact as a map into `Lᵖ(Ω; F)`. Each scalar
projection of the field factors through `TauCeti.WeakDerivStep.toW1pL` and the scalar value map,
so the coordinatewise criterion `TauCeti.isCompactOperator_of_forall_isCompactOperator_compLpL_comp`
applies. Nothing about `Ω` is used beyond the scalar compactness hypothesis, so this serves every
domain on which a first-order Rellich theorem is available.

## Main declarations

* `TauCeti.WeakDerivStep.isCompactOperator_comp_prevL`: compactness of the selected field from
  compactness of the scalar value map.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace

variable {E F X : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- If the scalar value map `W^{1,p}(Ω) → Lᵖ(Ω)` is compact, then for finite-dimensional `F` the
field selected by `base` is compact as a map from the weak-derivative graph space into
`Lᵖ(Ω; F)`. -/
theorem isCompactOperator_comp_prevL (base : X →L[ℝ] Lp F p (mu.restrict Omega))
    (h : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := p))) :
    IsCompactOperator (base.comp (prevL base)) := by
  refine isCompactOperator_of_forall_isCompactOperator_compLpL_comp ℝ fun ℓ ↦ ?_
  have heq : (ℓ.compLpL p (mu.restrict Omega)).comp (base.comp (prevL base)) =
      (W1p.valueL (mu := mu) (Omega := Omega) (p := p)).comp (toW1pL base ℓ) := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, W1p.valueL_apply, value_toW1pL, prevL_apply]
  rw [← ContinuousLinearMap.coe_comp, heq]
  exact h.comp_clm (toW1pL base ℓ)

end TauCeti.WeakDerivStep
