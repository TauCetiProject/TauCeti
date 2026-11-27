/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule.FiniteOrder
import TauCeti.LinearAlgebra.Dimension.Intersection

/-!
# Codimension bounds for cyclic norm conditions

The codimension imposed by requiring several cyclic norm sums to vanish is at most the
sum of the dimensions of their fixed spaces. For this bound the operators need not commute,
and their periods need not be invertible in the coefficient field.

The dimension estimate is used in `New.Data.le_finrank_ramifiedSourceForms` in
`grh/src/New/UpperBound/Size/ShortColumns.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Finset Module

namespace LinearMap

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- Cyclic norm conditions for a family of operators of possibly different periods cut out
at most the sum of the dimensions of their fixed spaces. -/
theorem finrank_le_finrank_iInf_ker_sum_pow_add (f : ι → Module.End K V) {n : ι → ℕ}
    (hn : ∀ i, f i ^ n i = 1) :
    finrank K V ≤ finrank K (↥(⨅ i, ker (∑ j ∈ Finset.range (n i), f i ^ j)) : Type _) +
      ∑ i, finrank K (f i).fixedSubmodule := by
  by_cases hV : Module.Finite K V
  · have hker : (⨅ i, ker ((f i).fixedNorm (hn i))) =
        ⨅ i, ker (∑ j ∈ Finset.range (n i), f i ^ j) := by
      refine iInf_congr fun i ↦ ?_
      rw [← subtype_comp_fixedNorm _ (hn i), ker_comp_of_ker_eq_bot _ (Submodule.ker_subtype _)]
    rw [← hker]
    exact (finrank_le_finrank_iInf_ker_add_sum_finrank_range
      (fun i ↦ (f i).fixedNorm (hn i))).trans (Nat.add_le_add_left
        (sum_le_sum fun i _ ↦ ((f i).fixedNorm (hn i)).range.finrank_le) _)
  · rw [Module.finrank_of_not_finite hV]
    exact Nat.zero_le _

/-- If each fixed-space dimension is at most `dim V / n`, the common kernel of the cyclic
norms has dimension at least `(1 - Fintype.card ι / n) * dim V` for positive `n`. The
cross-multiplied form holds also at `n = 0`. -/
theorem mul_finrank_iInf_ker_sum_pow_ge (f : ι → Module.End K V) {n : ℕ}
    (hn : ∀ i, f i ^ n = 1) (hfix : ∀ i, n * finrank K (f i).fixedSubmodule ≤ finrank K V) :
    (n - Fintype.card ι) * finrank K V ≤
      n * finrank K (↥(⨅ i, ker (∑ j ∈ Finset.range n, f i ^ j)) : Type _) := by
  have h := Nat.mul_le_mul_left n (finrank_le_finrank_iInf_ker_sum_pow_add f hn)
  rw [Nat.mul_add, Finset.mul_sum] at h
  have hsum : (∑ i, n * finrank K (f i).fixedSubmodule) ≤ Fintype.card ι * finrank K V := by
    simpa using (Finset.sum_le_sum fun i (_ : i ∈ univ) ↦ hfix i)
  rw [Nat.sub_mul]
  exact Nat.sub_le_of_le_add (h.trans (Nat.add_le_add_left hsum _))

end LinearMap
