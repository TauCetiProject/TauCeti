/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.Defs
public import TauCeti.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.Combinatorics.Enumerative.Partition.Dominance
public import TauCeti.LinearAlgebra.End.JordanChain.Basic
import TauCeti.Combinatorics.Enumerative.Partition.Conjugate

/-!
# The Jordan partition of a nilpotent endomorphism

The lengths of a Jordan-chain basis form a native `Nat.Partition` of the dimension.
This partition is independent of the chosen chains: the multiplicity of each positive
part is the drop in successive increases of the kernel dimensions. Conversely,
the partition recovers all those dimensions, and therefore completely determines
conjugacy of nilpotent endomorphisms between finite-dimensional vector spaces.

`Module.End.jordanPartition` makes this invariant available without choosing chains.
`Module.End.JordanChainBasis.jordanPartition_eq` identifies it with any supplied chain
basis, and `Module.End.exists_linearEquiv_conj_eq_iff_jordanPartition_parts_eq` gives the
conjugacy criterion. No algebraic closure or characteristic assumption is needed.

The dominance order on Jordan partitions compares ranks of powers:
`Module.End.jordanPartition_dominates_jordanPartition_iff` says that the Jordan partition of `f`
dominates that of `g` exactly when `rank (g ^ k) ≤ rank (f ^ k)` for every `k`. For nilpotent
matrices this is the combinatorial side of the description of orbit closures by dominance.

## References

* P. R. Halmos, *Finite-Dimensional Vector Spaces*, §57.
-/

public section

open Module Finset

namespace Module.End.JordanChainBasis

variable {K V : Type*} [Semiring K] [StrongRankCondition K] [AddCommMonoid V] [Module K V]
  {f : End K V} {ι : Type*} [Fintype ι]

/-- The partition whose parts are the lengths of the chains. -/
noncomputable def partition (c : f.JordanChainBasis ι) : Nat.Partition (finrank K V) where
  parts := Finset.univ.val.map c.len
  parts_pos := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hk
    exact c.len_pos i
  parts_sum := c.finrank_eq_sum_len.symm

/-- The parts of a chain partition are the chain lengths, with their multiplicities. -/
@[simp]
theorem partition_parts (c : f.JordanChainBasis ι) :
    c.partition.parts = Finset.univ.val.map c.len := (rfl)

/-- The multiplicity of a part is the number of chains of that length. -/
theorem count_partition_parts (c : f.JordanChainBasis ι) (k : ℕ) :
    c.partition.parts.count k = #{i | c.len i = k} := by
  classical
  simp [Multiset.count_map, ← Finset.filter_val, eq_comm]

end Module.End.JordanChainBasis

namespace Module.End.JordanChainBasis

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  {f : End K V} {ι : Type*} [Fintype ι]

/-- The partition recovers the dimensions of the kernels of all powers. -/
theorem finrank_ker_pow_eq_sum_partition (c : f.JordanChainBasis ι) (k : ℕ) :
    finrank K (LinearMap.ker (f ^ k)) = (c.partition.parts.map (min k)).sum := by
  simpa [Multiset.map_map, Function.comp_def] using c.finrank_ker_pow k

/-- Positive-part multiplicities are recovered from successive kernel dimensions. -/
theorem count_partition_parts_succ (c : f.JordanChainBasis ι) (k : ℕ) :
    c.partition.parts.count (k + 1) =
      (finrank K (LinearMap.ker (f ^ (k + 1))) - finrank K (LinearMap.ker (f ^ k))) -
        (finrank K (LinearMap.ker (f ^ (k + 2))) -
          finrank K (LinearMap.ker (f ^ (k + 1)))) := by
  rw [c.count_partition_parts, c.card_len_eq_add_one]

/-- The number of parts larger than `k` is the increase in kernel dimension from
power `k` to power `k + 1`. -/
theorem card_filter_partition_parts (c : f.JordanChainBasis ι) (k : ℕ) :
    (c.partition.parts.filter (k < ·)).card =
      finrank K (LinearMap.ker (f ^ (k + 1))) - finrank K (LinearMap.ker (f ^ k)) := by
  classical
  have hcard : (c.partition.parts.filter (k < ·)).card = #{i | k < c.len i} := by
    simp [Multiset.filter_map, ← Finset.filter_val]
  rw [hcard, c.finrank_ker_pow_succ]
  omega

end Module.End.JordanChainBasis

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A nilpotent endomorphism has a partition whose positive-part multiplicities are the
drops in successive increases of its kernel dimensions. -/
private theorem exists_partition_count_eq (f : End K V) (hf : IsNilpotent f) :
    ∃ p : Nat.Partition (finrank K V), ∀ k,
      p.parts.count (k + 1) =
        (finrank K (LinearMap.ker (f ^ (k + 1))) - finrank K (LinearMap.ker (f ^ k))) -
          (finrank K (LinearMap.ker (f ^ (k + 2))) -
            finrank K (LinearMap.ker (f ^ (k + 1)))) := by
  obtain ⟨ι, _, ⟨c⟩⟩ := exists_jordanChainBasis hf
  exact ⟨c.partition, c.count_partition_parts_succ⟩

/-- The Jordan partition of a nilpotent endomorphism, with each Jordan block contributing
its size as a part. It is characterized by `count_jordanPartition_parts_succ`. -/
noncomputable def jordanPartition (f : End K V) (hf : IsNilpotent f) :
    Nat.Partition (finrank K V) :=
  (f.exists_partition_count_eq hf).choose

/-- The multiplicity of the part `k + 1` is the drop in kernel-dimension increases
from `k` to `k + 1` and from `k + 1` to `k + 2`. -/
theorem count_jordanPartition_parts_succ (f : End K V) (hf : IsNilpotent f) (k : ℕ) :
    (f.jordanPartition hf).parts.count (k + 1) =
      (finrank K (LinearMap.ker (f ^ (k + 1))) - finrank K (LinearMap.ker (f ^ k))) -
        (finrank K (LinearMap.ker (f ^ (k + 2))) -
          finrank K (LinearMap.ker (f ^ (k + 1)))) :=
  (f.exists_partition_count_eq hf).choose_spec k

/-- Every Jordan-chain basis gives the same Jordan partition. -/
theorem JordanChainBasis.jordanPartition_eq {f : End K V} {ι : Type*} [Fintype ι]
    (c : f.JordanChainBasis ι) (hf : IsNilpotent f) : f.jordanPartition hf = c.partition := by
  apply Nat.Partition.ext
  apply Nat.Partition.parts_eq_of_count_succ
  intro k
  rw [count_jordanPartition_parts_succ, c.count_partition_parts_succ]

/-- The Jordan partition determines all dimensions of kernels of powers. -/
theorem finrank_ker_pow_eq_sum_jordanPartition (f : End K V) (hf : IsNilpotent f) (k : ℕ) :
    finrank K (LinearMap.ker (f ^ k)) = ((f.jordanPartition hf).parts.map (min k)).sum := by
  obtain ⟨ι, _, ⟨c⟩⟩ := exists_jordanChainBasis hf
  rw [c.jordanPartition_eq hf]
  exact c.finrank_ker_pow_eq_sum_partition k

/-- Two nilpotent endomorphisms have equal Jordan-partition parts exactly when all their
kernel dimensions agree, even on different vector spaces. -/
theorem jordanPartition_parts_eq_iff
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : End K V) (g : End K W) (hf : IsNilpotent f) (hg : IsNilpotent g) :
    (f.jordanPartition hf).parts = (g.jordanPartition hg).parts ↔
      ∀ k, finrank K (LinearMap.ker (f ^ k)) = finrank K (LinearMap.ker (g ^ k)) := by
  constructor
  · intro h k
    rw [f.finrank_ker_pow_eq_sum_jordanPartition hf,
      g.finrank_ker_pow_eq_sum_jordanPartition hg, h]
  · intro h
    apply Nat.Partition.parts_eq_of_count_succ
    intro k
    simp only [count_jordanPartition_parts_succ, h]

/-- The Jordan partition is a complete conjugacy invariant for nilpotent endomorphisms,
including endomorphisms of different vector spaces. -/
theorem exists_linearEquiv_conj_eq_iff_jordanPartition_parts_eq
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : End K V) (g : End K W) (hf : IsNilpotent f) (hg : IsNilpotent g) :
    (∃ e : V ≃ₗ[K] W, e.conj f = g) ↔
      (f.jordanPartition hf).parts = (g.jordanPartition hg).parts :=
  (exists_linearEquiv_conj_eq_iff hf hg).trans (jordanPartition_parts_eq_iff f g hf hg).symm

/-- Conjugating an endomorphism preserves its Jordan partition. -/
@[simp]
theorem jordanPartition_conj (f : End K V) (e : V ≃ₗ[K] V)
    (h : IsNilpotent (e.conj f)) :
    (e.conj f).jordanPartition h =
      f.jordanPartition ((IsNilpotent.map_iff e.conjRingEquiv.injective).mp h) := by
  exact Nat.Partition.ext
    ((exists_linearEquiv_conj_eq_iff_jordanPartition_parts_eq f (e.conj f)
      ((IsNilpotent.map_iff e.conjRingEquiv.injective).mp h) h).mp ⟨e, rfl⟩).symm

/-- The length of column `k + 1` of the Jordan diagram is the increase in kernel dimension
from the `k`th to the `(k + 1)`st power. -/
theorem card_filter_jordanPartition_parts (f : End K V) (hf : IsNilpotent f) (k : ℕ) :
    ((f.jordanPartition hf).parts.filter (k < ·)).card =
      finrank K (LinearMap.ker (f ^ (k + 1))) - finrank K (LinearMap.ker (f ^ k)) := by
  obtain ⟨ι, _, ⟨c⟩⟩ := exists_jordanChainBasis hf
  rw [c.jordanPartition_eq hf, c.card_filter_partition_parts]

/-- The Jordan partition of `f` dominates that of `g` exactly when, for every `k`, the rank of
`g ^ k` is at most the rank of `f ^ k`. -/
theorem jordanPartition_dominates_jordanPartition_iff (f g : End K V) (hf : IsNilpotent f)
    (hg : IsNilpotent g) :
    (f.jordanPartition hf).Dominates (g.jordanPartition hg) ↔
      ∀ k, finrank K (LinearMap.range (g ^ k)) ≤ finrank K (LinearMap.range (f ^ k)) := by
  rw [Nat.Partition.dominates_iff_forall_sum_map_min_le]
  refine forall_congr' fun k => ?_
  rw [← f.finrank_ker_pow_eq_sum_jordanPartition hf, ← g.finrank_ker_pow_eq_sum_jordanPartition hg]
  have := (f ^ k).finrank_range_add_finrank_ker
  have := (g ^ k).finrank_range_add_finrank_ker
  omega

/-- The zero operator has one part of size one for each dimension, including no parts on
the zero-dimensional space. -/
@[simp]
theorem jordanPartition_zero :
    (0 : End K V).jordanPartition IsNilpotent.zero =
      TauCeti.Nat.Partition.ones (finrank K V) := by
  have hcol := (0 : End K V).card_filter_jordanPartition_parts IsNilpotent.zero 1
  -- Rewrite inside the kernel's type argument, which simp does not visit.
  rw [zero_pow (by decide : (1 + 1 : ℕ) ≠ 0), pow_one, Nat.sub_self] at hcol
  have hlen := Multiset.filter_eq_nil.mp (Multiset.card_eq_zero.mp hcol)
  have hparts := Multiset.eq_replicate_card.mpr fun k hk =>
    Nat.le_antisymm (Nat.le_of_not_gt (hlen k hk))
      (Nat.Partition.parts_pos _ hk)
  have hdim := ((0 : End K V).jordanPartition IsNilpotent.zero).parts_sum
  rw [hparts] at hdim
  simp only [Multiset.sum_replicate, smul_eq_mul, mul_one] at hdim
  apply Nat.Partition.ext
  simpa only [TauCeti.Nat.Partition.ones_parts, hdim] using hparts

end Module.End
