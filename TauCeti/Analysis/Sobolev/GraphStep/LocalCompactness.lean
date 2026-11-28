/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Multiplication
public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
public import TauCeti.Analysis.Sobolev.W1p.LocalCompactness
public import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import TauCeti.MeasureTheory.Function.Lp.ExtendByZero

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

Multiplying by a smooth function with compact support in the domain before taking the field is
compact as well (`TauCeti.WeakDerivStep.isCompactOperator_prevL_comp_smulLeftCLM`): the product
vanishes off a compactly contained open set, so it is the extension by zero of a compact
restriction. This localizes compactness on unbounded domains such as the whole space.

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
open scoped ENNReal ContDiff

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

/-- **Compactness of localization by a cutoff.** For finite-dimensional `F`, `1 ≤ p ≤ ∞` and a
smooth `ψ` with compact support inside `Ω`, the map sending `u ∈ W^{1,p}(Ω, F)` to the field
`ψ u ∈ Lᵖ(Ω, F)` is compact. No boundedness of `Ω` is needed. -/
theorem isCompactOperator_prevL_comp_smulLeftCLM [FiniteDimensional ℝ F] {ψ : E → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ Omega) (h₀ : ∃ C, ∀ x ∈ Omega, ‖ψ x‖ ≤ C)
    (h₁ : ∃ C, ∀ x ∈ Omega, ‖fderiv ℝ ψ x‖ ≤ C) (hc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Omega) :
    IsCompactOperator ((prevL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))).comp
      (smulLeftCLM ψ hψ h₀ h₁ fun _ _ ↦ rfl)) := by
  obtain ⟨U, hUo, hψU, hUΩ, hUc⟩ :=
    exists_open_between_and_isCompact_closure hc.isCompact Omega.isOpen hψΩ
  let V : Opens E := ⟨U, hUo⟩
  have hV : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hUΩ)
  let ext := (TauCeti.extendByZeroLpₗᵢ (F := F) (p := p) ℝ mu hUo.measurableSet.nullMeasurableSet
    (SetLike.coe_subset_coe.mpr hV)).toContinuousLinearMap
  -- The field `ψ u` vanishes off `V`, so it is the extension by zero of its restriction to `V`.
  have heq : (prevL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))).comp
      (smulLeftCLM ψ hψ h₀ h₁ fun _ _ ↦ rfl) =
      ext.comp ((restrictBaseL _ hV).comp (smulLeftCLM ψ hψ h₀ h₁ fun _ _ ↦ rfl)) := by
    refine ContinuousLinearMap.ext fun u ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, prevL_apply, ext,
      LinearIsometry.coe_toContinuousLinearMap]
    have hprev := prev_smulLeftCLM_ae (T := ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))
      hψ h₀ h₁ (fun _ _ ↦ rfl) u
    refine (TauCeti.extendByZeroLpₗᵢ_eq_of_ae_eq ℝ _ _
      (h := fun x ↦ ψ x • prev _ u x) (fun x hx ↦ hψU (subset_tsupport ψ (left_ne_zero_of_smul hx)))
      ?_ hprev).symm
    filter_upwards [restrictBaseL_apply_ae _ hV (smulLeftCLM ψ hψ h₀ h₁ (fun _ _ ↦ rfl) u),
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hV) hprev] with x hx₁ hx₂
    rw [hx₁, ContinuousLinearMap.id_apply, hx₂]
  have hR : IsCompactOperator (restrictBaseL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))
      hV) := isCompactOperator_restrictBaseL (V := V) _ hUc hUΩ
  rw [heq, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
  exact (hR.comp_clm _).clm_comp ext

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
