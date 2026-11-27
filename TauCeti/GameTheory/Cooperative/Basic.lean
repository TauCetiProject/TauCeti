/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Lattice.Submodular
import Mathlib.Data.Finset.Interval

/-!
# Classes of cooperative games

A real-valued set function assigns a worth to each finite coalition of players. It is a game
when the empty coalition has worth zero. Convexity means that its negative is submodular,
and superadditivity means that disjoint coalitions lose no worth by joining.

A convex worth function is superadditive if the empty coalition has nonpositive worth
(`TauCeti.IsSubmodular.isSuperadditive`). Superadditivity forces that bound on the empty
coalition (`TauCeti.IsSuperadditive.empty_le_zero`) and implies monotonicity when every
singleton has nonnegative worth (`TauCeti.IsSuperadditive.monotone_of_nonneg_singleton`).

The increasing-marginals characterization `TauCeti.isSubmodular_neg_iff_forall_insert`
explains how convexity controls the gain from adding a player to a coalition.

## References

* L. S. Shapley, *Notes on n-person games VII: cores of convex games*,
  RAND memorandum RM-4571-PR (1965), §1.
-/

public section

open Finset

namespace TauCeti

variable {ι K : Type*} [DecidableEq ι]

/-- A coalition worth function is superadditive if the worth of the union of two disjoint
coalitions is at least the sum of their individual worths. -/
def IsSuperadditive [Add K] [LE K] (v : Finset ι → K) : Prop :=
  ∀ S T : Finset ι, Disjoint S T → v S + v T ≤ v (S ∪ T)

/-- Superadditivity is the union inequality on disjoint coalitions. -/
theorem isSuperadditive_def [Add K] [LE K] (v : Finset ι → K) :
    IsSuperadditive v ↔ ∀ S T : Finset ι, Disjoint S T → v S + v T ≤ v (S ∪ T) :=
  Iff.rfl

variable {v : Finset ι → K}

/-- A convex coalition worth function whose empty coalition has nonpositive worth is
superadditive. In particular this holds for a convex game. -/
theorem IsSubmodular.isSuperadditive [AddCommGroup K] [Preorder K] [IsOrderedAddMonoid K]
    (hv : IsSubmodular (-v)) (h₀ : v ∅ ≤ 0) : IsSuperadditive v := by
  rw [isSuperadditive_def]
  intro S T hST
  have h : v S + v T ≤ v (S ∪ T) + v ∅ := by
    simpa only [disjoint_iff_inter_eq_empty.mp hST, Pi.neg_apply, ← neg_add, neg_le_neg_iff]
      using hv.apply S T
  exact h.trans (add_le_of_nonpos_right h₀)

/-- The worth of the empty coalition is nonpositive for a superadditive set function. -/
theorem IsSuperadditive.empty_le_zero [AddZeroClass K] [LE K] [AddLeftReflectLE K]
    (hv : IsSuperadditive v) : v ∅ ≤ 0 := by
  have h := (isSuperadditive_def v).mp hv ∅ ∅ (by simp)
  rw [empty_union] at h
  exact nonpos_of_add_le_right h

/-- A superadditive set function with nonnegative singleton worths is monotone. -/
theorem IsSuperadditive.monotone_of_nonneg_singleton [AddZeroClass K] [Preorder K]
    [AddRightMono K] (hv : IsSuperadditive v) (h₀ : ∀ i, 0 ≤ v {i}) : Monotone v := by
  apply monotone_iff_forall_le_insert.mpr
  intro S i hi
  have h := (isSuperadditive_def v).mp hv {i} S (disjoint_singleton_left.mpr hi)
  rw [singleton_union] at h
  exact (le_add_of_nonneg_left (h₀ i)).trans h

end TauCeti
