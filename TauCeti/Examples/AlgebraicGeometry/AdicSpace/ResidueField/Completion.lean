/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ResidueField.Completion
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.MinimalPlus
public import TauCeti.RingTheory.Huber.Padic.Field
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.PadicInt

/-!
# Completed residue pairs on the p-adic disc

The rank-one Gauss point and its rank-two specialization just above radius one give
completed residue pairs with different coordinate inequalities. Both closed residue points
map back to the original points through the canonical morphism of Huber pairs. The canonical
residue map kills the coordinate at the classical origin and is injective at the Gauss point.
The analytic point of the p-adic integers also has a completed residue pair.
-/

public section

open TauCeti TauCeti.Huber TauCeti.ValuationSpectrum

namespace TauCeti.Examples.ResidueFieldCompletion

variable (p : ℕ) [Fact p.Prime]

/-- The completed residue field at the rank-two point above the boundary is a Tate ring. -/
example :
    IsTateRing (residueFieldValuation (gaussPointAboveOne ℚ_[p])).Completion :=
  (isAnalyticPoint_of_isTateRing _).isTateRing_residueFieldCompletion
    ((mem_spa_iff _ _).mp gaussPointAboveOne_mem_spa_closedDiscMinimalPlus).1

/-- The canonical morphism from the minimal p-adic disc pair sends the closed point of the
rank-two completed residue spectrum back to the rank-two point. -/
example :
    let S : Pair (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p]))
      isWeightFamily_one_weight) := ⟨closedDiscMinimalPlus ℚ_[p],
      isRingOfIntegralElements_closedDiscMinimalPlus⟩
    let x : spa S.plus := ⟨gaussPointAboveOne ℚ_[p],
      gaussPointAboveOne_mem_spa_closedDiscMinimalPlus⟩
    letI := (isAnalyticPoint_of_isTateRing x.val).isTateRing_residueFieldCompletion
      ((mem_spa_iff _ _).mp x.property).1
    (residueFieldCompletionHom S x).spaComap (residueFieldCompletionPoint x.val) = x := by
  intro S x
  let := (isAnalyticPoint_of_isTateRing x.val).isTateRing_residueFieldCompletion
    ((mem_spa_iff _ _).mp x.property).1
  simp

/-- The canonical completed residue map at the rank-two point keeps the strict inequality
`v(T) > 1`; the power-bounded coordinate need not belong to this pair's plus ring. -/
example :
    1 < Valued.v (residueFieldCompletionMap (gaussPointAboveOne ℚ_[p])
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p])) isWeightFamily_one_weight 0)) := by
  rw [valued_residueFieldCompletionMap, ← map_one (gaussPointAboveOne ℚ_[p]).valuation,
    lt_iff_not_ge, valuation_le_iff]
  intro h
  exact gaussPointAboveOne_notMem_closedPolydisc
    ((mem_closedPolydisc_iff_weightedX_vle_one
      gaussPointAboveOne_mem_spa_closedDiscMinimalPlus).mpr h)

/-- The rank-one Gauss point gives a second canonical residue morphism from the same minimal
p-adic disc pair, whose distinguished closed point lies over the Gauss point. -/
example :
    let S : Pair (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p]))
      isWeightFamily_one_weight) := ⟨closedDiscMinimalPlus ℚ_[p],
      isRingOfIntegralElements_closedDiscMinimalPlus⟩
    let x : spa S.plus := ⟨(gaussPoint (K := ℚ_[p]) one_pos le_rfl).val,
      closedPolydisc_subset_spa_closedDiscMinimalPlus (gaussPoint one_pos le_rfl).property⟩
    letI := (isAnalyticPoint_of_isTateRing x.val).isTateRing_residueFieldCompletion
      ((mem_spa_iff _ _).mp x.property).1
    (residueFieldCompletionHom S x).spaComap (residueFieldCompletionPoint x.val) = x := by
  intro S x
  let := (isAnalyticPoint_of_isTateRing x.val).isTateRing_residueFieldCompletion
    ((mem_spa_iff _ _).mp x.property).1
  simp

/-- At the rank-one Gauss point the coordinate remains sub-unit in the completed residue
field, separating its valuation from the rank-two example. -/
example :
    Valued.v (residueFieldCompletionMap (gaussPoint (K := ℚ_[p]) one_pos le_rfl).val
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p])) isWeightFamily_one_weight 0)) ≤ 1 := by
  rw [valued_residueFieldCompletionMap,
    ← map_one (gaussPoint (K := ℚ_[p]) one_pos le_rfl).val.valuation, valuation_le_iff]
  exact (mem_closedPolydisc_iff_weightedX_vle_one
    (closedPolydisc_subset_spa_closedDiscMinimalPlus (gaussPoint one_pos le_rfl).property)).mp
      (gaussPoint one_pos le_rfl).property

/-- The canonical completed residue map at the p-adic Gauss point is injective because its
support is zero. -/
example : Function.Injective
    (residueFieldCompletionMap (gaussPoint (K := ℚ_[p]) one_pos le_rfl).val) := by
  rw [RingHom.injective_iff_ker_eq_bot, ker_residueFieldCompletionMap, supp_gaussPoint]

/-- At the p-adic classical origin the analytic residue map kills the coordinate. The base
point is obtained by restricting the Gauss point to constants. -/
example :
    let g := gaussPoint (K := ℚ_[p]) one_pos le_rfl
    let b : spa (powerBoundedSubring ℚ_[p]) :=
      ⟨comap (weightedC _ isWeightFamily_one_weight) g.val, comap_weightedC_mem_spa g⟩
    let x := classicalPoint b (fun _ : Fin 1 ↦ (0 : ℚ_[p]))
      (fun _ ↦ isPowerBounded_zero)
    x.val.IsAnalyticPoint ∧ residueFieldCompletionMap x.val
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set ℚ_[p])) isWeightFamily_one_weight 0) = 0 := by
  intro g b x
  refine ⟨isAnalyticPoint_of_isTateRing x.val, ?_⟩
  rw [← RingHom.mem_ker, ker_residueFieldCompletionMap, mem_supp_iff, classicalPoint_vle]
  simp

/-- The canonical residue morphism over the p-adic integers sends its closed point to the
analytic point of the non-Tate source. -/
example :
    let S := Pair.powerBounded ℤ_[p]
    let hAdic := _root_.PadicInt.isAdic_maximalIdeal (p := p)
    let x : spa S.plus :=
      ⟨ofValuation (_root_.IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation,
        TauCeti.IsDiscreteValuationRing.ofValuation_intValuation_mem_spa hAdic S.plus⟩
    letI := (TauCeti.IsDiscreteValuationRing.isAnalyticPoint_ofValuation_intValuation
      hAdic).isTateRing_residueFieldCompletion ((mem_spa_iff _ _).mp x.property).1
    ¬ IsTateRing ℤ_[p] ∧
      (residueFieldCompletionHom S x).spaComap (residueFieldCompletionPoint x.val) = x := by
  intro S hAdic x
  let := (TauCeti.IsDiscreteValuationRing.isAnalyticPoint_ofValuation_intValuation
    hAdic).isTateRing_residueFieldCompletion ((mem_spa_iff _ _).mp x.property).1
  exact ⟨Huber.PadicInt.not_isTateRing, by simp⟩

end TauCeti.Examples.ResidueFieldCompletion
