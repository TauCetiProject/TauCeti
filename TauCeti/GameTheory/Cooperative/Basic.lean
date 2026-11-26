/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Function.Submodular
public import TauCeti.Order.Lattice.Submodular.SMul
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Linarith

/-!
# Classes of cooperative games

A real-valued set function assigns a worth to each finite coalition of players. It is a game
when the empty coalition has worth zero. Convexity means that its negative is submodular,
and superadditivity means that disjoint coalitions lose no worth by joining.

The increasing-marginals characterization `TauCeti.isSubmodular_neg_iff_forall_insert`
explains how convexity controls the gain from adding a player to a coalition.
`ConvexOn.isSubmodular_neg_finsetSum` gives convexity of measure games, where the worth
is a convex function of the sum of nonnegative player weights.

## References

* L. S. Shapley, *Notes on n-person games VII: cores of convex games*,
  RAND memorandum RM-4571-PR (1965), §1.
-/

public section

open Finset

namespace TauCeti

variable {ι : Type*} [DecidableEq ι]

/-- A coalition worth function is superadditive if the worth of the union of two disjoint
coalitions is at least the sum of their individual worths. -/
def IsSuperadditive (v : Finset ι → ℝ) : Prop :=
  ∀ S T : Finset ι, Disjoint S T → v S + v T ≤ v (S ∪ T)

/-- Superadditivity is the union inequality on disjoint coalitions. -/
theorem isSuperadditive_def (v : Finset ι → ℝ) :
    IsSuperadditive v ↔ ∀ S T : Finset ι, Disjoint S T → v S + v T ≤ v (S ∪ T) :=
  Iff.rfl

variable {v : Finset ι → ℝ}

/-- A convex coalition worth function whose empty coalition has nonpositive worth is
superadditive. In particular this holds for a convex game. -/
theorem IsSubmodular.isSuperadditive (hv : IsSubmodular (-v)) (h₀ : v ∅ ≤ 0) :
    IsSuperadditive v := by
  rw [isSuperadditive_def]
  intro S T hST
  have h := hv.apply S T
  simp only [disjoint_iff_inter_eq_empty.mp hST, Pi.neg_apply] at h
  linarith only [h, h₀]

/-- The worth of the empty coalition is nonpositive for a superadditive set function. -/
theorem IsSuperadditive.empty_le_zero (hv : IsSuperadditive v) : v ∅ ≤ 0 := by
  have h := (isSuperadditive_def v).mp hv ∅ ∅ (by simp)
  rw [empty_union] at h
  linarith only [h]

/-- A superadditive set function with nonnegative singleton worths is monotone. -/
theorem IsSuperadditive.monotone_of_nonneg_singleton (hv : IsSuperadditive v)
    (h₀ : ∀ i, 0 ≤ v {i}) : Monotone v := by
  apply monotone_iff_forall_le_insert.mpr
  intro S i hi
  have h := (isSuperadditive_def v).mp hv {i} S (disjoint_singleton_left.mpr hi)
  rw [singleton_union] at h
  exact (le_add_of_nonneg_left (h₀ i)).trans h

end TauCeti
