/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Named partitions

This file records some partitions of `n` that are referred to by name.  Two of them are the
extremes: `Nat.Partition.ones n = (1ⁿ)`, the finest partition, into `n` parts equal to `1`, is the
opposite extreme to Mathlib's coarsest partition `Nat.Partition.indiscrete n = (n)`, whose parts
are the single part `n` when `n ≠ 0`, and none when `n = 0`.  The third is
`Nat.Partition.singletonSecondRow n = (n+1, 1)`, the partition of `n+2` with two parts whose
second part is a single box; it is written at `n+2` so that both parts are positive with no
hypothesis on `n`.

It also records `TauCeti.parts_equivCast`, the transport of a partition along an equality of the
number being partitioned: such a transport leaves the parts alone, and
`Nat.Partition.card_parts_le`, which says a partition of `n` has at most `n` parts, while the
squares of its parts sum to at least `n` (`Nat.Partition.le_sum_sq_parts`).
Positive-part counts determine the parts even for partitions of different numbers
(`Nat.Partition.parts_eq_of_count_succ`); zero never occurs as a part, so filtering the
parts by positivity keeps them all (`Nat.Partition.filter_pos_parts`). Finally,
`Nat.Partition.sum_sort_parts` and `Nat.Partition.sort_parts_injective` say that the
decreasingly sorted parts of a partition of `n` sum to `n` and determine the partition.
-/

public section

namespace TauCeti

/-- **Transporting a partition along an equality of the number being partitioned does not change
its parts.** -/
theorem parts_equivCast {m l : ℕ} (h : m = l) (p : m.Partition) :
    (Equiv.cast (congrArg Nat.Partition h) p).parts = p.parts := by
  subst h; rfl

namespace Nat.Partition

/-- The partition `(1ⁿ)` of `n` into `n` parts, each equal to `1`.

This is the finest partition of `n`, opposite to Mathlib's coarsest `Nat.Partition.indiscrete n`,
whose parts are the single part `n` when `n ≠ 0`, and none when `n = 0`.

The parts are exposed only through `Nat.Partition.ones_parts`. -/
def ones (n : ℕ) : n.Partition :=
  _root_.Nat.Partition.ofSums n (Multiset.replicate n 1) (by simp)

@[simp]
theorem ones_parts (n : ℕ) : (ones n).parts = Multiset.replicate n 1 := by
  simp [ones, Multiset.filter_eq_self, Multiset.mem_replicate]

/-- The product of the factorials of the parts of the coarsest partition `(n)` is `n !`.

For `n = 0` this is the empty product, and `0! = 1` agrees with it. -/
@[simp]
theorem prod_map_factorial_indiscrete (n : ℕ) :
    ((_root_.Nat.Partition.indiscrete n).parts.map Nat.factorial).prod = n.factorial := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp [_root_.Nat.Partition.indiscrete_parts hn.ne']

/-- The partition `(n+1, 1)` of `n+2`: two parts, the second a single box.

This is the shape usually written `(n-1, 1)` at `n`; writing it at `n+2` keeps both parts positive
with no hypothesis on `n`.  It is the unique shape with two rows whose second row is a single box,
and the coarsest shape other than `Nat.Partition.indiscrete`.

The parts are exposed only through `Nat.Partition.singletonSecondRow_parts`. -/
def singletonSecondRow (n : ℕ) : (n + 2).Partition :=
  _root_.Nat.Partition.ofSums (n + 2) {n + 1, 1} (by simp)

/-- The parts of `(n+1, 1)`. -/
@[simp]
theorem singletonSecondRow_parts (n : ℕ) : (singletonSecondRow n).parts = {n + 1, 1} := by
  simp [singletonSecondRow, Multiset.filter_eq_self]

/-- The decreasingly sorted parts of `(n+1, 1)`. -/
theorem sort_parts_singletonSecondRow (n : ℕ) :
    (singletonSecondRow n).parts.sort (· ≥ ·) = [n + 1, 1] := by
  rw [singletonSecondRow_parts, Multiset.insert_eq_cons,
    Multiset.sort_cons _ _ _ (by simp), Multiset.sort_singleton]

end Nat.Partition

end TauCeti

namespace Nat.Partition

/-- Zero has multiplicity zero in every partition. -/
@[simp]
theorem count_parts_zero {n : ℕ} (p : n.Partition) : p.parts.count 0 = 0 := by
  exact Multiset.count_eq_zero.mpr fun h => (p.parts_pos h).ne' rfl

/-- Every part of a partition is positive, so keeping the positive parts keeps them all. -/
@[simp]
theorem filter_pos_parts {n : ℕ} (p : n.Partition) : p.parts.filter (0 < ·) = p.parts :=
  Multiset.filter_eq_self.mpr fun _ => p.parts_pos

/-- Equal multiplicities of all positive parts determine the parts of two partitions,
even when the numbers being partitioned are not assumed equal. -/
theorem parts_eq_of_count_succ {m n : ℕ} {p : m.Partition} {q : n.Partition}
    (h : ∀ k, p.parts.count (k + 1) = q.parts.count (k + 1)) : p.parts = q.parts := by
  apply Multiset.ext.mpr
  intro k
  cases k with
  | zero => simp
  | succ k => exact h k

/-- **A partition of `n` has at most `n` parts**, since every part is at least `1`. -/
theorem card_parts_le {n : ℕ} (μ : n.Partition) : μ.parts.card ≤ n := by
  simpa [μ.parts_sum] using μ.parts.card_nsmul_le_sum (a := 1) fun _ hx => μ.parts_pos hx

/-- The sum of the squares of the parts of a partition of `n` is at least `n`. -/
theorem le_sum_sq_parts {n : ℕ} (μ : n.Partition) : n ≤ (μ.parts.map (· ^ 2)).sum :=
  calc n = (μ.parts.map id).sum := by rw [Multiset.map_id, μ.parts_sum]
    _ ≤ _ := Multiset.sum_map_le_sum_map _ _ fun x _ => Nat.le_self_pow two_ne_zero x

/-- The decreasingly sorted parts of a partition of `n` sum to `n`. -/
@[simp]
theorem sum_sort_parts {n : ℕ} (μ : n.Partition) : (μ.parts.sort (· ≥ ·)).sum = n := by
  rw [← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]

/-- A partition is determined by its decreasingly sorted parts. -/
theorem sort_parts_injective {n : ℕ} :
    Function.Injective fun μ : n.Partition => μ.parts.sort (· ≥ ·) :=
  fun μ ν h => Nat.Partition.ext <| by simpa using congrArg ((↑) : List ℕ → Multiset ℕ) h

end Nat.Partition
