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

It also records `TauCeti.parts_equivCast`: transporting a partition along an equality of the
number being partitioned leaves its parts alone.  A partition of `n` has at most `n` parts
(`Nat.Partition.card_parts_le`), while every positive power of its parts sums to at least `n`
(`Nat.Partition.le_sum_pow_parts`).
Two partitions, even of different numbers, have the same parts exactly when their positive-part
counts agree (`Nat.Partition.parts_eq_iff_count_succ`); zero never occurs as a part, so filtering
the parts by positivity keeps them all (`Nat.Partition.filter_pos_parts`), a partition has no parts
only when partitioning zero (`Nat.Partition.parts_eq_zero_iff`), and it has at most one part
only when it is the coarsest partition (`Nat.Partition.card_parts_le_one_iff`). Finally,
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
  cases n <;> simp

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

/-- A partition has no parts if and only if it is a partition of zero. -/
@[simp]
theorem parts_eq_zero_iff {n : ℕ} (p : n.Partition) : p.parts = 0 ↔ n = 0 :=
  ⟨fun h => by simpa [h] using p.parts_sum.symm, fun hn => by subst hn; simp⟩

/-- Every partition of a nonzero integer has at least one part. -/
theorem parts_ne_zero {n : ℕ} (p : n.Partition) (hn : n ≠ 0) : p.parts ≠ 0 :=
  mt p.parts_eq_zero_iff.mp hn

/-- Zero has multiplicity zero in every partition. -/
@[simp]
theorem count_parts_zero {n : ℕ} (p : n.Partition) : p.parts.count 0 = 0 :=
  Multiset.count_eq_zero.mpr fun h => (p.parts_pos h).ne' rfl

/-- Every part of a partition is positive, so keeping the positive parts keeps them all. -/
@[simp]
theorem filter_pos_parts {n : ℕ} (p : n.Partition) : p.parts.filter (0 < ·) = p.parts :=
  Multiset.filter_eq_self.mpr fun _ => p.parts_pos

/-- Two partitions have the same parts if and only if every positive number occurs in them with
the same multiplicity, even when the numbers being partitioned are not assumed equal. -/
theorem parts_eq_iff_count_succ {m n : ℕ} {p : m.Partition} {q : n.Partition} :
    p.parts = q.parts ↔ ∀ k, p.parts.count (k + 1) = q.parts.count (k + 1) := by
  refine ⟨fun h k => by rw [h], fun h => Multiset.ext.mpr fun k => ?_⟩
  cases k with
  | zero => simp
  | succ k => exact h k

/-- **A partition of `n` has at most `n` parts**, since every part is at least `1`. -/
theorem card_parts_le {n : ℕ} (μ : n.Partition) : μ.parts.card ≤ n := by
  simpa [μ.parts_sum] using μ.parts.card_nsmul_le_sum (a := 1) fun _ hx => μ.parts_pos hx

/-- A partition of `n` has at most one part if and only if it is the coarsest partition
`Nat.Partition.indiscrete n`. -/
@[simp]
theorem card_parts_le_one_iff {n : ℕ} (p : n.Partition) :
    p.parts.card ≤ 1 ↔ p = indiscrete n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact iff_of_true (by simp) (Subsingleton.elim _ _)
  refine ⟨fun hle => Nat.Partition.ext ?_, by rintro rfl; simp [indiscrete_parts hn]⟩
  -- A nonempty multiset with at most one element is a singleton `{a}`, and `a` is the sum `n`.
  obtain ⟨a, ha⟩ :=
    Multiset.card_eq_one.mp (hle.antisymm (Multiset.card_pos.mpr (p.parts_ne_zero hn)))
  have hsum : a = n := by rw [← p.parts_sum, ha, Multiset.sum_singleton]
  rw [ha, indiscrete_parts hn, hsum]

/-- For every positive exponent `k`, the sum of the `k`-th powers of the parts of a partition of
`n` is at least `n`. -/
theorem le_sum_pow_parts {n k : ℕ} (μ : n.Partition) (hk : k ≠ 0) :
    n ≤ (μ.parts.map (· ^ k)).sum :=
  μ.parts_sum.ge.trans <| Multiset.sum_le_sum_map _ fun x _ => Nat.le_self_pow hk x

/-- The decreasingly sorted parts of a partition of `n` sum to `n`. -/
@[simp]
theorem sum_sort_parts {n : ℕ} (μ : n.Partition) : (μ.parts.sort (· ≥ ·)).sum = n := by
  rw [← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]

/-- A partition is determined by its decreasingly sorted parts. -/
theorem sort_parts_injective {n : ℕ} :
    Function.Injective fun μ : n.Partition => μ.parts.sort (· ≥ ·) :=
  fun μ ν h => Nat.Partition.ext <| by simpa using congrArg ((↑) : List ℕ → Multiset ℕ) h

end Nat.Partition
