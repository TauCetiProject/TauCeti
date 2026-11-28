/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.SimpleCoordinates
import TauCeti.LinearAlgebra.RootSystem.Weyl.TypeA.RankTwo
import Mathlib.Algebra.DualNumber

/-!
# Simple-root coordinate checks in ranks one and two

These checks use supplied Chevalley data, so they apply to every isogeny type and
admissible representation. In A₂ the two simple coordinates distinguish the two simple
root groups and vanish on the root group of their sum. Over the rational dual numbers,
a nonzero infinitesimal simple parameter is retained and becomes zero under reduction.
-/

public noncomputable section

open Multiplicative TauCeti TauCeti.DynkinType

namespace TauCeti.ChevalleySimpleCoordinatesExamples

local instance : NeZero (DynkinType.A 1).rank := ⟨by simp⟩
local instance : NeZero (DynkinType.A 2).rank := ⟨by simp⟩

/-- In A₁ the coordinate of the positive root is its original parameter over any value ring. -/
theorem a1_coordinate {ht : (DynkinType.A 1).Valid} (D : ChevalleyDatum (.A 1) ht)
    (R : Type*) [CommRing R] (a : R) :
    D.simpleRootCoordinate R 0
      ⟨D.rootSubgroupPoints ((DynkinType.A 1).simpleIndex ht 0) R (ofAdd a),
        D.rootSubgroupPoints_mem_positivePoints R (simpleIndex_mem_posRoots 0) _⟩ = ofAdd a := by
  simp

variable {ht : (DynkinType.A 2).Valid}

/-- Both A₂ coordinates on each of the three positive root groups, over an arbitrary ring. -/
private theorem a2_coordinates (D : ChevalleyDatum (.A 2) ht) (R : Type*) [CommRing R] (a : R) :
    (D.simpleRootCoordinate R 0
        ⟨D.rootSubgroupPoints ((DynkinType.A 2).simpleIndex ht 0) R (ofAdd a),
          D.rootSubgroupPoints_mem_positivePoints R (simpleIndex_mem_posRoots 0) _⟩,
      D.simpleRootCoordinate R 1
        ⟨D.rootSubgroupPoints ((DynkinType.A 2).simpleIndex ht 0) R (ofAdd a),
          D.rootSubgroupPoints_mem_positivePoints R (simpleIndex_mem_posRoots 0) _⟩) =
      (ofAdd a, 1) ∧
    (D.simpleRootCoordinate R 0
        ⟨D.rootSubgroupPoints ((DynkinType.A 2).simpleIndex ht 1) R (ofAdd a),
          D.rootSubgroupPoints_mem_positivePoints R (simpleIndex_mem_posRoots 1) _⟩,
      D.simpleRootCoordinate R 1
        ⟨D.rootSubgroupPoints ((DynkinType.A 2).simpleIndex ht 1) R (ofAdd a),
          D.rootSubgroupPoints_mem_positivePoints R (simpleIndex_mem_posRoots 1) _⟩) =
      (1, ofAdd a) ∧
    (D.simpleRootCoordinate R 0
        ⟨D.rootSubgroupPoints typeA2HighestRootIndex R (ofAdd a),
          D.rootSubgroupPoints_mem_positivePoints R
            typeA2HighestRootIndex_mem_posRoots_rational _⟩,
      D.simpleRootCoordinate R 1
        ⟨D.rootSubgroupPoints typeA2HighestRootIndex R (ofAdd a),
          D.rootSubgroupPoints_mem_positivePoints R
            typeA2HighestRootIndex_mem_posRoots_rational _⟩) = (1, 1) := by
  have h01 : (DynkinType.A 2).simpleIndex ht 0 ≠ (DynkinType.A 2).simpleIndex ht 1 := by
    intro h
    have heq : (DynkinType.A 2).simpleSupportEquiv ht 0 =
        (DynkinType.A 2).simpleSupportEquiv ht 1 :=
      Subtype.ext (by simpa only [coe_simpleSupportEquiv] using h)
    exact (by decide : (0 : Fin 2) ≠ 1)
      (((DynkinType.A 2).simpleSupportEquiv ht).injective heq)
  refine ⟨Prod.ext (D.simpleRootCoordinate_simpleIndex R 0 _) ?_,
    Prod.ext ?_ (D.simpleRootCoordinate_simpleIndex R 1 _), Prod.ext ?_ ?_⟩
  all_goals apply (D.simpleRootCoordinate_eq_one_iff R _ _).mpr
  · exact D.rootSubgroupPoints_mem_puncturedPositivePoints R
      ⟨simpleIndex_mem_posRoots 0, h01⟩ _
  · exact D.rootSubgroupPoints_mem_puncturedPositivePoints R
      ⟨simpleIndex_mem_posRoots 1, h01.symm⟩ _
  · exact D.rootSubgroupPoints_mem_puncturedPositivePoints R
      ⟨typeA2HighestRootIndex_mem_posRoots_rational, typeA2HighestRootIndex_ne_simpleIndex 0⟩ _
  · exact D.rootSubgroupPoints_mem_puncturedPositivePoints R
      ⟨typeA2HighestRootIndex_mem_posRoots_rational, typeA2HighestRootIndex_ne_simpleIndex 1⟩ _

/-- A simple parameter over the rational dual numbers is detected before reduction and
vanishes afterwards; the infinitesimal is a nonzero square-zero element. -/
example (D : ChevalleyDatum (.A 2) ht) :
    let g : D.positivePoints (DualNumber ℚ) :=
      ⟨D.rootSubgroupPoints ((DynkinType.A 2).simpleIndex ht 0) (DualNumber ℚ)
        (ofAdd DualNumber.eps),
        D.rootSubgroupPoints_mem_positivePoints _ (simpleIndex_mem_posRoots 0) _⟩
    D.simpleRootCoordinate (DualNumber ℚ) 0 g = ofAdd DualNumber.eps ∧
      D.simpleRootCoordinate ℚ 0
        (D.mapPositivePoints (TrivSqZeroExt.fstHom ℚ ℚ ℚ).toRingHom g) = 1 ∧
      (DualNumber.eps : DualNumber ℚ) ≠ 0 ∧ (DualNumber.eps : DualNumber ℚ) ^ 2 = 0 := by
  dsimp only
  have hc := congrArg Prod.fst (a2_coordinates D (DualNumber ℚ) DualNumber.eps).1
  dsimp only at hc
  refine ⟨hc, ?_, ?_, ?_⟩
  · rw [D.simpleRootCoordinate_map, hc]
    exact congrArg ofAdd (DualNumber.fst_eps (R := ℚ))
  · intro h
    have he : (1 : ℚ) = 0 := by simpa using congrArg TrivSqZeroExt.snd h
    exact one_ne_zero he
  · simp [pow_two, DualNumber.eps_mul_eps]

end TauCeti.ChevalleySimpleCoordinatesExamples
