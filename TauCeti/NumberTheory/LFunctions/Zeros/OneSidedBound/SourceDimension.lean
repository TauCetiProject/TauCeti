/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule.FiniteOrder
import TauCeti.LinearAlgebra.FixedSubmodule.Codimension

/-!
# Source dimension for the index bound of a theta lift

Local colength bounds charge the full source dimension, whereas the translates used in
spanning are counted with the ramified source dimension. At a level larger than twice
the number of cyclic norm conditions, the ramified source retains at least half the
full source dimension.

This is the dimension comparison in `New.Data.finrank_sourceForm_le_two_mul` in
`grh/src/New/Reduction/ShortAndEnough.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Module

namespace TauCeti.OneSidedBound

/-- The full source dimension is at most twice the dimension of the ramified source,
cut out by the cyclic norms. The fixed-space bounds suffice even when the translations do
not commute, or when the period is zero in the coefficient field. -/
theorem finrank_le_two_mul_finrank_ramifiedSourceForms {K V ι : Type*}
    [Field K] [AddCommGroup V] [Module K V] [Fintype ι] (z : ι → Module.End K V) {N : ℕ}
    (hN : 2 * Fintype.card ι < N) (hz : ∀ w, z w ^ (N - 1) = 1)
    (hfix : ∀ w, (N - 1) * finrank K (z w).fixedSubmodule ≤ finrank K V) :
    finrank K V ≤
      2 * finrank K (↥(⨅ w, LinearMap.ker (∑ i ∈ Finset.range (N - 1), z w ^ i)) : Type _) := by
  have hpos : 1 ≤ N := by omega
  obtain rfl | hNp := hpos.eq_or_lt
  · have htop : (⨅ w, LinearMap.ker (∑ i ∈ Finset.range (1 - 1), z w ^ i)) = ⊤ := by
      simp
    rw [htop, finrank_top]
    omega
  have hn : 0 < N - 1 := by omega
  have hdim := LinearMap.mul_finrank_iInf_ker_sum_pow_ge z hz hfix
  have hhalf : N - 1 ≤ 2 * (N - 1 - Fintype.card ι) := by omega
  apply Nat.le_of_mul_le_mul_left _ hn
  calc
    (N - 1) * finrank K V ≤ 2 * (N - 1 - Fintype.card ι) * finrank K V :=
      Nat.mul_le_mul_right _ hhalf
    _ = 2 * ((N - 1 - Fintype.card ι) * finrank K V) := Nat.mul_assoc ..
    _ ≤ _ := by simpa only [Nat.mul_left_comm 2] using Nat.mul_le_mul_left 2 hdim

end TauCeti.OneSidedBound
