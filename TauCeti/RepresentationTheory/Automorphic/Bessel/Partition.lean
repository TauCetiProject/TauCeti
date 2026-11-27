/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Basic

/-!
# Bessel partitions

The Bessel coefficient of index `ℓ` in dimension `d` has geometric partition
`[2 * ℓ + 1, 1^(d - 2 * ℓ - 1)]`. This file constructs that partition when
`2 * ℓ + 1 ≤ d` and computes its parts and their number. At index zero it is the
partition into ones. The index is determined by the partition.

This is only the combinatorial label of a coefficient. A rational Bessel datum also
requires an isotropic flag and an anisotropic vector in its middle space; neither
is supplied by this partition or by the dimension inequality.

The partition is that of Jiang–Zhang, *Arthur parameters and cuspidal automorphic
modules of classical groups*, Annals of Mathematics 191 (2020), §2.3, (2.9).
-/

public section

namespace TauCeti

/-- The geometric partition `[2ℓ+1, 1^(d-2ℓ-1)]` of a Bessel coefficient of index `ℓ`
in dimension `d`. The inequality ensures that its leading part fits in `d`. -/
def besselPartition (d ℓ : ℕ) (h : 2 * ℓ + 1 ≤ d) : Nat.Partition d where
  parts := (2 * ℓ + 1) ::ₘ Multiset.replicate (d - 2 * ℓ - 1) 1
  parts_pos := by
    intro i hi
    simp only [Multiset.mem_cons, Multiset.mem_replicate] at hi
    rcases hi with rfl | ⟨_, rfl⟩ <;> omega
  parts_sum := by
    simp only [Multiset.sum_cons, Multiset.sum_replicate, smul_eq_mul, mul_one]
    omega

/-- The leading odd part followed by the remaining ones. -/
@[simp]
theorem besselPartition_parts (d ℓ : ℕ) (h : 2 * ℓ + 1 ≤ d) :
    (besselPartition d ℓ h).parts =
      (2 * ℓ + 1) ::ₘ Multiset.replicate (d - 2 * ℓ - 1) 1 := (rfl)

/-- A Bessel partition of index `ℓ` in dimension `d` has `d - 2 * ℓ` parts. -/
theorem card_parts_besselPartition (d ℓ : ℕ) (h : 2 * ℓ + 1 ≤ d) :
    (besselPartition d ℓ h).parts.card = d - 2 * ℓ := by
  simp only [besselPartition_parts, Multiset.card_cons, Multiset.card_replicate]
  omega

/-- Index zero gives the all-ones partition, including dimension one. -/
@[simp]
theorem besselPartition_zero (d : ℕ) (h : 2 * 0 + 1 ≤ d) :
    besselPartition d 0 h = Nat.Partition.ones d := by
  apply _root_.Nat.Partition.ext
  simp only [besselPartition_parts, Nat.Partition.ones_parts, mul_zero, zero_add,
    Nat.sub_zero]
  rw [← Multiset.replicate_succ, Nat.sub_add_cancel (by omega)]

/-- Membership distinguishes the leading part from the ones, which occur only when
there is room after the leading part. -/
theorem mem_parts_besselPartition {d ℓ i : ℕ} (h : 2 * ℓ + 1 ≤ d) :
    i ∈ (besselPartition d ℓ h).parts ↔
      i = 2 * ℓ + 1 ∨ i = 1 ∧ 2 * ℓ + 1 < d := by
  simp only [besselPartition_parts, Multiset.mem_cons, Multiset.mem_replicate]
  omega

/-- Two valid Bessel indices give the same partition exactly when they are equal. -/
@[simp]
theorem besselPartition_inj {d ℓ k : ℕ}
    (hℓ : 2 * ℓ + 1 ≤ d) (hk : 2 * k + 1 ≤ d) :
    besselPartition d ℓ hℓ = besselPartition d k hk ↔ ℓ = k := by
  constructor
  · intro heq
    have hc := congrArg (fun p : Nat.Partition d => p.parts.card) heq
    simp only [card_parts_besselPartition] at hc
    omega
  · rintro rfl
    rfl

end TauCeti
