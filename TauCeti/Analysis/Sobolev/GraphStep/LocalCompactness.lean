/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.Analysis.Sobolev.W1p.LocalCompactness

/-!
# Vector-valued local Rellich compactness

For a finite-dimensional target, restriction of a weakly differentiable `Lᵖ` field to an open
set compactly contained in its domain is compact when `1 ≤ p < ∞`. No boundary condition or
boundedness of the ambient domain is required. The graph-space version retains an arbitrary
preceding space and field-selection map, so it also applies to higher weak-derivative steps.

`TauCeti.WeakDerivStep.restrictBaseL` restricts the selected field, and
`TauCeti.WeakDerivStep.isCompactOperator_restrictBaseL` proves its compactness. The proof
projects to scalar coordinates using `toW1pL`, applies
`TauCeti.W1p.isCompactOperator_valueL_restrictL`, and reconstructs the field in a finite basis.
Finite dimensionality of the target is essential: constant fields valued in an infinite
orthonormal sequence already obstruct local norm compactness.

In particular this supplies compact restriction of `W^{1,2}(ℝ,F)` paths to bounded intervals,
the compact error term in the Fredholm estimates for first-order trajectory operators.

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
and `1 ≤ p < ∞`. The preceding space need not be complete. -/
theorem isCompactOperator_restrictBaseL [FiniteDimensional ℝ F]
    (base : X →L[ℝ] Lp F p (mu.restrict Omega)) (hp : p ≠ ∞)
    (hVc : IsCompact (closure (V : Set E))) (hVO : closure (V : Set E) ⊆ Omega) :
    IsCompactOperator (restrictBaseL base (SetLike.coe_subset_coe.mp
      (subset_closure.trans hVO))) := by
  classical
  let hV : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVO)
  let b := Module.finBasis ℝ F
  let ℓ := fun i ↦ (b.coord i).toContinuousLinearMap
  let C := fun i ↦ ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL
    p (mu.restrict V)).comp
      (((W1p.valueL (mu := mu) (Omega := V) (p := p)).comp
        (W1p.restrictL hV)).comp (toW1pL base (ℓ i)))
  have hC (i) : IsCompactOperator (C i) :=
    ((W1p.isCompactOperator_valueL_restrictL hp hVc hVO).comp_clm
      (toW1pL base (ℓ i))).clm_comp
        ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL p (mu.restrict V))
  have heq : restrictBaseL base hV = ∑ i, C i := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    have hproj : ∀ i, W1p.value (W1p.restrictL hV (toW1pL base (ℓ i) u)) =ᵐ[mu.restrict V]
        fun x ↦ ℓ i (base (prev base u) x) := fun i ↦ by
      refine (W1p.value_restrictL_ae hV _).trans ?_
      rw [value_toW1pL]
      exact (ℓ i).coeFn_compLpL (base (prev base u)) |>.filter_mono
        (ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hV)))
    have hcoord : ∀ i, C i u =ᵐ[mu.restrict V]
        fun x ↦ (ℓ i (base (prev base u) x)) • b i := fun i ↦ by
      simp only [C, ContinuousLinearMap.comp_apply, W1p.valueL_apply]
      refine (((ContinuousLinearMap.toSpanSingleton ℝ (b i)).coeFn_compLpL
        (W1p.value (W1p.restrictL hV (toW1pL base (ℓ i) u))))).trans ?_
      filter_upwards [hproj i] with x hx
      simp only [ContinuousLinearMap.toSpanSingleton_apply, hx]
    filter_upwards [restrictBaseL_apply_ae base hV u,
      Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ C i u),
      ae_all_iff.mpr hcoord] with x hres hsum hcoords
    simp only [sum_apply, hres, hsum]
    simpa only [hcoords, ℓ, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply] using
      (b.sum_repr (base (prev base u) x)).symm
  rw [heq]
  -- Compact operators form a submodule, so finite coordinate reconstruction preserves compactness.
  exact (compactOperator (RingHom.id ℝ) _ _).sum_mem fun i _ ↦ hC i

end TauCeti.WeakDerivStep
