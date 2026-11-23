/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ResidueField.Valued
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Analytic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.ValuedField
import TauCeti.RingTheory.Huber.ValuedField

/-!
# The completed residue pair at an analytic point

At a continuous analytic valuation `v` of a Huber ring, the completed residue field
`(residueFieldValuation v).Completion` is a Tate field. The valuation ring of the completed
valuation is the closure of the original valuation ring, with the full valuation retained.
It gives a complete Huber pair, and if `v ∈ Spa(A,A⁺)` the canonical map from `A` is a morphism
of pairs. The closed point of the completed residue spectrum maps to `v`.

This is the valued field pair to which one can extend the valuation when constructing
a geometric point over `v`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §2.5.
* P. Scholze, [*Étale cohomology of diamonds*](https://arxiv.org/abs/1709.07343), §7.
-/

public section

namespace TauCeti.ValuationSpectrum

open Huber

variable {A : Type*} [CommRing A]

/-- The completed residue field of an analytic point is Tate. -/
theorem IsAnalyticPoint.isTateRing_residueFieldCompletion
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] {v : Spv A}
    (ha : v.IsAnalyticPoint) (hv : v.IsContinuous) :
    IsTateRing (residueFieldValuation v).Completion := by
  obtain ⟨a, hnil, ha'⟩ :=
    (isAnalyticPoint_iff_exists_isTopologicallyNilpotent_notMem_supp v).mp ha
  apply IsTateRing.of_valued _ (hnil.map (continuous_residueFieldCompletionMap hv))
  intro heq
  apply ha'
  rw [← ker_residueFieldCompletionMap]
  exact RingHom.mem_ker.mpr heq

section

variable (v : Spv A) [IsHuberRing (residueFieldValuation v).Completion]

/-- The completed residue field with the valuation subring of its completed valuation. -/
noncomputable def residueFieldCompletionPair : Pair (residueFieldValuation v).Completion :=
  ⟨Valued.v.valuationSubring.toSubring,
    isRingOfIntegralElements_valuationSubring (residueFieldValuation v).Completion⟩

/-- The plus ring in the completed residue pair is the valuation subring of the completed
valuation. -/
@[simp]
theorem residueFieldCompletionPair_plus :
    (residueFieldCompletionPair v).plus =
      (Valued.v (R := (residueFieldValuation v).Completion)).valuationSubring.toSubring := (rfl)

/-- The plus ring in the completed residue pair is the closure of the original valuation ring
in the completed residue field. -/
theorem residueFieldCompletionPair_plus_eq_completionPlus :
    (residueFieldCompletionPair v).plus =
      completionPlus
        (Valued.v (R := WithVal (residueFieldValuation v))).valuationSubring.toSubring :=
  (residueFieldCompletionPair_plus v).trans (completionPlus_valuationSubring _).symm

/-- The closed point of the completed residue spectrum, represented by the completed valuation. -/
noncomputable def residueFieldCompletionPoint : spa (residueFieldCompletionPair v).plus :=
  valuedSpaPoint (residueFieldValuation v).Completion

/-- The underlying valuation of the completed residue point is the completed valuation. -/
@[simp]
theorem coe_residueFieldCompletionPoint :
    (residueFieldCompletionPoint v : Spv (residueFieldValuation v).Completion) =
      ofValuation Valued.v :=
  coe_valuedSpaPoint (residueFieldValuation v).Completion

/-- Every point of the completed residue spectrum specializes to its distinguished point. -/
theorem specializes_residueFieldCompletionPoint
    (y : spa (residueFieldCompletionPair v).plus) :
    y ⤳ residueFieldCompletionPoint v :=
  specializes_valuedSpaPoint _ y

/-- The distinguished point of the completed residue spectrum is closed. -/
theorem isClosed_singleton_residueFieldCompletionPoint :
    IsClosed ({residueFieldCompletionPoint v} : Set (spa (residueFieldCompletionPair v).plus)) :=
  isClosed_singleton_valuedSpaPoint _

end

section

variable [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (S : Pair A) (x : spa S.plus) [IsHuberRing (residueFieldValuation x.val).Completion]

/-- The canonical morphism from `(A,A⁺)` to the completed residue pair at a point of its adic
spectrum. At an analytic point the target is a Tate field by
`IsAnalyticPoint.isTateRing_residueFieldCompletion`. -/
noncomputable def residueFieldCompletionHom : S.Hom (residueFieldCompletionPair x.val) where
  toRingHom := residueFieldCompletionMap x.val
  continuous_toRingHom := continuous_residueFieldCompletionMap ((mem_spa_iff _ _).mp x.property).1
  map_mem_plus a ha := by
    rw [residueFieldCompletionPair_plus, ValuationSubring.mem_toSubring,
      Valuation.mem_valuationSubring_iff, valued_residueFieldCompletionMap]
    exact valuation_le_one_of_mem_spa x.property ha

/-- The residue morphism of pairs uses the canonical map to the completed residue field. -/
@[simp]
theorem residueFieldCompletionHom_toRingHom :
    (residueFieldCompletionHom S x).toRingHom = residueFieldCompletionMap x.val := (rfl)

/-- The closed point of the completed residue spectrum lies over the original point. -/
@[simp]
theorem residueFieldCompletionHom_spaComap_point :
    (residueFieldCompletionHom S x).spaComap (residueFieldCompletionPoint x.val) = x := by
  apply Subtype.ext
  rw [Pair.Hom.spaComap_val, residueFieldCompletionHom_toRingHom,
    coe_residueFieldCompletionPoint, comap_ofValuation,
    valued_comap_residueFieldCompletionMap, ofValuation_valuation]

/-- Every point of the completed residue spectrum maps to a generization of the original
point. -/
theorem residueFieldCompletionHom_spaComap_specializes
    (y : spa (residueFieldCompletionPair x.val).plus) :
    (residueFieldCompletionHom S x).spaComap y ⤳ x := by
  simpa only [residueFieldCompletionHom_spaComap_point] using
    (specializes_residueFieldCompletionPoint x.val y).map
      (residueFieldCompletionHom S x).continuous_spaComap

end

end TauCeti.ValuationSpectrum
