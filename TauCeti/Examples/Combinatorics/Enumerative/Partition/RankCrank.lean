/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Enumerative.Partition.RankCrank

/-!
# Regression examples: the rank and the crank of a partition

These examples evaluate `Nat.Partition.rank` and `Nat.Partition.crank` on small partitions:

* `(3, 2, 1, 1)` has two parts equal to `1` and one part larger than `2`, so its rank and its
  crank are both `-1`; counting the parts at least `2` instead would give crank `0`;
* `(3, 3)` has no part equal to `1`, so its crank is its largest part `3`, while its rank is `1`;
  its conjugate `(2, 2, 2)` has rank `-1`;
* the coefficient of `X` in the crank generating series is `z⁻¹`, so the crank counts of size one
  are not symmetric.
-/

open Nat.Partition LaurentPolynomial

example : (Nat.Partition.ofSums 7 {3, 2, 1, 1} rfl).rank = -1 := by
  simp [rank_def, Multiset.filter_singleton]

example : (Nat.Partition.ofSums 7 {3, 2, 1, 1} rfl).crank = -1 := by
  rw [crank_of_one_mem (by simp)]
  simp [Multiset.filter_singleton]

example : (Nat.Partition.ofSums 6 {3, 3} rfl).rank = 1 := by
  simp [rank_def, Multiset.filter_singleton]

example : (Nat.Partition.ofSums 6 {3, 3} rfl).crank = 3 := by
  rw [crank_of_one_notMem (by simp)]
  simp

example : (Nat.Partition.ofSums 6 {3, 3} rfl).conjugate.rank = -1 := by
  rw [rank_conjugate]
  simp [rank_def, Multiset.filter_singleton]

example : PowerSeries.coeff 1 (crankGenFun ℤ) = T (-1) :=
  coeff_one_crankGenFun
