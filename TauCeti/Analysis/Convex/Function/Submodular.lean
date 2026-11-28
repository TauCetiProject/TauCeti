/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import TauCeti.Order.Lattice.Submodular
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import TauCeti.Analysis.Convex.Function.Basic

/-!
# Supermodularity of convex functions of total weight

Applying a convex function to the sum of nonnegative weights over a finite set gives a
supermodular set function. In cooperative game theory this is a measure game when `f 0 = 0`,
since the empty coalition has total weight zero.
-/

public section

open Finset TauCeti

variable {ι : Type*} [DecidableEq ι]

/-- Applying a function convex on the nonnegative half-line to sums of nonnegative weights
gives a supermodular set function. -/
theorem ConvexOn.isSubmodular_neg_finsetSum {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {f : 𝕜 → 𝕜} (hf : ConvexOn 𝕜 (Set.Ici 0) f)
    {m : ι → 𝕜} (hm : ∀ i, 0 ≤ m i) :
    IsSubmodular (-(fun S : Finset ι ↦ f (∑ i ∈ S, m i))) := by
  apply (isSubmodular_neg_iff_forall_insert _).mpr
  intro S T hST i hi
  simp only [sum_insert (notMem_mono hST hi), sum_insert hi, add_comm (m i)]
  exact hf.sub_le_sub_of_le
    (sum_nonneg fun j _ ↦ hm j)
    (add_nonneg (sum_nonneg fun j _ ↦ hm j) (hm i))
    (hm i)
    (sum_le_sum_of_subset_of_nonneg hST fun j _ _ ↦ hm j)
