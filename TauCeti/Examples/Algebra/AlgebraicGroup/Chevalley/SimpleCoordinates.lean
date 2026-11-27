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

private theorem topRoot_eq_sum :
    ((DynkinType.A 2).rationalRootSystem ht).root typeA2HighestRootIndex =
      ((DynkinType.A 2).rationalRootSystem ht).root ((DynkinType.A 2).simpleIndex ht 0) +
      ((DynkinType.A 2).rationalRootSystem ht).root ((DynkinType.A 2).simpleIndex ht 1) := by
  have hs (i : Fin (DynkinType.A 2).rank) :
      (DynkinType.A 2).simpleIndex ht i = typeASimpleIndex 2 i := by
    apply Fin.ext
    exact (val_simpleIndex _ _ _).trans (typeASimpleIndex_val _).symm
  simpa only [one_nsmul] using
    ((DynkinType.A 2).root_rationalRootSystem_eq_nsmul_add_iff ht
      ((DynkinType.A 2).simpleIndex ht 0) ((DynkinType.A 2).simpleIndex ht 1)
      typeA2HighestRootIndex 1).mpr
        (by
          rw [one_nsmul, hs 0, hs 1]
          -- Normalize both dispatcher carriers before applying the family root relation.
          dsimp only [DynkinType.rank, DynkinType.numRoots]
          rw [simplyConnectedRootDatum_A]
          exact root_typeA2HighestRootIndex)

private theorem topRoot_positive : typeA2HighestRootIndex ∈
    posRoots ((DynkinType.A 2).rationalRootSystem ht) ((DynkinType.A 2).rationalBase ht) :=
  add_mem_posRoots _ _ (simpleIndex_mem_posRoots 0) (simpleIndex_mem_posRoots 1) topRoot_eq_sum

private theorem topRoot_ne_simple (i : Fin 2) :
    typeA2HighestRootIndex ≠ (DynkinType.A 2).simpleIndex ht i := by
  intro h
  have hh := ((DynkinType.A 2).rationalBase ht).height_add topRoot_eq_sum
  rw [h] at hh
  rw [((DynkinType.A 2).rationalBase ht).height_one_of_mem_support
    (simpleIndex_mem_support (t := .A 2) (ht := ht) i),
    ((DynkinType.A 2).rationalBase ht).height_one_of_mem_support
      (simpleIndex_mem_support (t := .A 2) (ht := ht) 0),
    ((DynkinType.A 2).rationalBase ht).height_one_of_mem_support
      (simpleIndex_mem_support (t := .A 2) (ht := ht) 1)] at hh
  omega

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
          D.rootSubgroupPoints_mem_positivePoints R topRoot_positive _⟩,
      D.simpleRootCoordinate R 1
        ⟨D.rootSubgroupPoints typeA2HighestRootIndex R (ofAdd a),
          D.rootSubgroupPoints_mem_positivePoints R topRoot_positive _⟩) = (1, 1) := by
  have h01 : (DynkinType.A 2).simpleIndex ht 0 ≠ (DynkinType.A 2).simpleIndex ht 1 := by
    intro h
    have := congrArg Fin.val h
    simp only [val_simpleIndex] at this
    contradiction
  refine ⟨Prod.ext (D.simpleRootCoordinate_simpleIndex R 0 _) ?_,
    Prod.ext ?_ (D.simpleRootCoordinate_simpleIndex R 1 _), Prod.ext ?_ ?_⟩
  all_goals apply (D.simpleRootCoordinate_eq_one_iff R _ _).mpr
  · exact D.rootSubgroupPoints_mem_puncturedPositivePoints R
      ⟨simpleIndex_mem_posRoots 0, h01⟩ _
  · exact D.rootSubgroupPoints_mem_puncturedPositivePoints R
      ⟨simpleIndex_mem_posRoots 1, h01.symm⟩ _
  · exact D.rootSubgroupPoints_mem_puncturedPositivePoints R
      ⟨topRoot_positive, topRoot_ne_simple 0⟩ _
  · exact D.rootSubgroupPoints_mem_puncturedPositivePoints R
      ⟨topRoot_positive, topRoot_ne_simple 1⟩ _

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
