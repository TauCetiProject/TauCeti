/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Basic.Real.Basic
public import TauCeti.Order.Lattice.Submodular
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Linarith
import TauCeti.Analysis.Convex.Function.Basic

/-!
# Classes of cooperative games

A real-valued set function assigns a worth to each finite coalition of players. It is a game
when the empty coalition has worth zero. Convexity means that its negative is submodular,
and superadditivity means that disjoint coalitions lose no worth by joining.

The increasing-marginals characterization explains how convexity controls the gain from
adding a player to a coalition. It also gives convexity of measure games, where the worth
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

/-- A set function is convex precisely when the marginal contribution of a player increases
with the coalition that player joins. -/
theorem isSubmodular_neg_iff_forall_insert (v : Finset ι → ℝ) :
    IsSubmodular (-v) ↔
      ∀ S T : Finset ι, S ⊆ T → ∀ i, i ∉ T → v (insert i S) - v S ≤ v (insert i T) - v T := by
  constructor
  · intro hv S T hST i hi
    have hunion : insert i S ∪ T = insert i T := by
      rw [insert_union, union_eq_right.mpr hST]
    have hinter : insert i S ∩ T = S := by
      rw [insert_inter_of_notMem hi, inter_eq_left.mpr hST]
    have h := hv.apply (insert i S) T
    simp only [hunion, hinter, Pi.neg_apply] at h
    linarith only [h]
  · intro hv
    rw [isSubmodular_def]
    intro S T
    simp only [Pi.neg_apply]
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hST : S ⊆ T
      · simp [union_eq_right.mpr hST, inter_eq_left.mpr hST, add_comm]
      -- Removing a player outside T leaves the intersection unchanged.
      obtain ⟨i, hiS, hiT⟩ := not_subset.mp hST
      have hgain := hv (S.erase i) (S.erase i ∪ T) subset_union_left i
        (notMem_union.mpr ⟨notMem_erase _ _, hiT⟩)
      have herase := ih (S.erase i) (erase_ssubset hiS)
      rw [← insert_union, insert_erase hiS] at hgain
      rw [erase_inter, erase_eq_of_notMem (fun hi ↦ hiT (mem_inter.mp hi).2)] at herase
      linarith only [herase, hgain]

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

/-- A nonnegative multiple of a convex coalition worth function is convex. -/
theorem isSubmodular_neg_smul (hv : IsSubmodular (-v)) {c : ℝ} (hc : 0 ≤ c) :
    IsSubmodular (-(c • v)) := by
  rw [isSubmodular_def]
  intro S T
  simpa only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, mul_neg, mul_add] using
    mul_le_mul_of_nonneg_left (hv.apply S T) hc

/-- Adding an additive worth function to a convex worth function preserves convexity. -/
theorem isSubmodular_neg_add_finsetSum (hv : IsSubmodular (-v)) (a : ι → ℝ) :
    IsSubmodular (fun S ↦ -(v S + ∑ i ∈ S, a i)) := by
  simpa only [Pi.neg_apply, sum_neg_distrib, neg_add] using
    hv.add (isSubmodular_finsetSum fun i ↦ -a i)

/-- Applying a real convex function to the total weight of a coalition gives a convex set
function when every player's weight is nonnegative. -/
theorem isSubmodular_neg_convexOn_finsetSum {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Ici 0) f)
    {m : ι → ℝ} (hm : ∀ i, 0 ≤ m i) :
    IsSubmodular (-(fun S : Finset ι ↦ f (∑ i ∈ S, m i))) := by
  apply (isSubmodular_neg_iff_forall_insert _).mpr
  intro S T hST i hi
  simp only [sum_insert (notMem_mono hST hi), sum_insert hi, add_comm (m i)]
  exact hf.sub_le_sub_of_le
    (sum_nonneg fun j _ ↦ hm j)
    (add_nonneg (sum_nonneg fun j _ ↦ hm j) (hm i))
    (hm i)
    (sum_le_sum_of_subset_of_nonneg hST fun j _ _ ↦ hm j)

end TauCeti
