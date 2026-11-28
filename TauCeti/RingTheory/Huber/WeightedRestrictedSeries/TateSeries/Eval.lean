/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedEval.Hom
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.TateSeries.Basic

/-!
# Evaluation and functoriality for `tateSeries`

This module connects the uncompleted restricted power-series ring `TauCeti.Huber.tateSeries N A`
with Wedhorn's evaluation (`TauCeti.Huber.weightedEval` and `TauCeti.Huber.weightedEvalHom`) at
power-bounded tuples.

## Main results

* `TauCeti.Huber.weightedEval_tateSeries_jacobian`: evaluation of the formal Jacobian determinant
  `tateSeries.jacobian F` commutes with `weightedEval` at power-bounded tuples.
* `TauCeti.Huber.map_weightedEval_tateSeries`: compatibility of `weightedEval` on `tateSeries`
  with continuous ring homomorphisms.
-/

public section

namespace TauCeti.Huber

/-- **Evaluating the formal Jacobian determinant `tateSeries.jacobian F`** at a power-bounded tuple
`x` along a ring homomorphism `φ` continuous at `0` computes the determinant of the evaluated
Jacobian matrix `(weightedEval φ x (∂ⱼFᵢ))`. -/
theorem weightedEval_tateSeries_jacobian
    {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C] [T3Space C]
    {φ : A →+* C} (hφ : ContinuousAt φ 0)
    {N : ℕ} {x : Fin N → C} (hx : ∀ i, IsPowerBounded (x i))
    (F : Fin N → tateSeries N A) :
    weightedEval φ x (tateSeries.jacobian F : MvPowerSeries (Fin N) A) =
      (Matrix.of fun i j ↦
        weightedEval φ x (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) A))).det := by
  rw [← coe_weightedEvalHom isWeightFamily_one_weight hφ
      ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ x).mpr hx),
    tateSeries.jacobian_def, RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp

/-- **Compatibility of `weightedEval` on `tateSeries` with continuous ring homomorphisms:** if
`φ : C →+* C'` is continuous into a Hausdorff nonarchimedean ring `C'` and `x : Fin N → C` consists
of power-bounded elements, then evaluating `g : tateSeries N C` at `x` and applying `φ` agrees with
evaluating `tateSeries.mapRingHom hφ g` at `φ ∘ x`. -/
theorem map_weightedEval_tateSeries
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C]
    {C' : Type*} [CommRing C'] [TopologicalSpace C'] [NonarchimedeanRing C'] [T2Space C']
    {φ : C →+* C'} (hφ : Continuous φ)
    {N : ℕ} {x : Fin N → C} (hx : ∀ l, IsPowerBounded (x l)) (g : tateSeries N C) :
    φ (weightedEval (RingHom.id C) x (g : MvPowerSeries (Fin N) C)) =
      weightedEval (RingHom.id C') (fun l ↦ φ (x l))
        (tateSeries.mapRingHom hφ g : MvPowerSeries (Fin N) C') := by
  have hid : ContinuousAt (RingHom.id C) 0 := continuous_id.continuousAt
  have hsum := (hasSum_weightedEval_of_forall_isPowerBounded hid hx
    (mem_weightedRestrictedSubring.mp g.property)).map φ hφ
  have hsum' : HasSum (weightedEvalTerm (RingHom.id C') (fun l ↦ φ (x l))
      (tateSeries.mapRingHom hφ g : MvPowerSeries (Fin N) C'))
      (φ (weightedEval (RingHom.id C) x (g : MvPowerSeries (Fin N) C))) := by
    convert hsum using 1
    ext ν
    simp [weightedEvalTerm_def, map_prod]
  symm
  rw [weightedEval_def]
  exact hsum'.tsum_eq

end TauCeti.Huber

end
