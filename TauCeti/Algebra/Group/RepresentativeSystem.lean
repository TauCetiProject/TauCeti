/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Systems of coset representatives and character orthogonality

Let `A` be an additive commutative group and `K, H : AddSubgroup A`. A family `y : ι → A` is a
*system of representatives* of `K` modulo `H` (`TauCeti.IsRepresentativeSystem y K H`) if every
`y i` lies in `K` and every `x ∈ K` is congruent modulo `H` to a unique `y i`.

Chosen representatives of `K ⧸ (H.addSubgroupOf K)` form a system of representatives
(`TauCeti.IsRepresentativeSystem.out`), any system has cardinality equal to the relative index
`H.relIndex K` (`TauCeti.IsRepresentativeSystem.card_eq_relIndex`), sums over `y` of functions
invariant under `H` are unchanged by translation by elements of `K`
(`TauCeti.IsRepresentativeSystem.sum_add_left`), and character sums over `y` satisfy orthogonality
over any integral domain (`TauCeti.IsRepresentativeSystem.sum_character`).

## Main results

* `TauCeti.IsRepresentativeSystem`: predicate that `y : ι → A` represents each coset of `K / H`
  once.
* `TauCeti.IsRepresentativeSystem.out`: canonical system of representatives via quotient choice.
* `TauCeti.IsRepresentativeSystem.card_eq_relIndex`: `Nat.card ι = H.relIndex K`.
* `TauCeti.IsRepresentativeSystem.sum_add_left`: translation invariance of sums of `H`-periodic
  functions over a representative system.
* `TauCeti.IsRepresentativeSystem.sum_character`: character orthogonality over a representative
  system in any integral domain.

## Provenance

Adapted from `New.IsRepresentativeSystem`, `New.IsRepresentativeSystem.out`,
`New.IsRepresentativeSystem.card_eq_relIndex`, `New.IsRepresentativeSystem.sum_add_left`, and
`New.IsRepresentativeSystem.sum_character` (file `src/Lib/Weil/Construction/FourierInversion.lean`)
in grh-lean (https://github.com/lsernau/grh-lean, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Finset

namespace TauCeti

variable {A ι : Type*} [AddCommGroup A] {K H : AddSubgroup A} {y : ι → A}

/-- A family `y : ι → A` is a system of representatives of `K` modulo `H` if every `y i` lies in
`K` and every `x ∈ K` is congruent modulo `H` to a unique `y i`. -/
structure IsRepresentativeSystem (y : ι → A) (K H : AddSubgroup A) : Prop where
  /-- Every representative lies in `K`. -/
  mem : ∀ i : ι, y i ∈ K
  /-- Every element of `K` is congruent modulo `H` to a unique representative. -/
  existsUnique : ∀ x ∈ K, ∃! i : ι, x - y i ∈ H

namespace IsRepresentativeSystem

/-- Two representatives whose difference lies in `H` have the same index. -/
theorem eq_of_sub_mem (hy : IsRepresentativeSystem y K H) {i j : ι} (h : y i - y j ∈ H) :
    i = j :=
  (hy.existsUnique _ (hy.mem i)).unique (by simp) h

/-- Chosen representatives of the quotient `K ⧸ (H.addSubgroupOf K)` form a system of
representatives of `K` modulo `H`. -/
theorem out (K H : AddSubgroup A) :
    IsRepresentativeSystem (fun q : K ⧸ H.addSubgroupOf K ↦ (q.out : A)) K H := by
  refine ⟨fun q ↦ q.out.property, fun x hx ↦ ?_⟩
  lift x to K using hx
  refine ⟨QuotientAddGroup.mk x, ?_, fun q hq ↦ ?_⟩
  · have h : QuotientAddGroup.mk (x - (QuotientAddGroup.mk x : K ⧸ H.addSubgroupOf K).out) =
        (0 : K ⧸ H.addSubgroupOf K) := by simp
    exact AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h)
  · have h : (QuotientAddGroup.mk x : K ⧸ H.addSubgroupOf K) = q := by
      rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem]
      exact AddSubgroup.mem_addSubgroupOf.mpr hq
    exact h.symm

/-- A system of representatives of `K` modulo `H` has cardinality `[K : H ⊓ K]`. -/
theorem card_eq_relIndex (hy : IsRepresentativeSystem y K H) : Nat.card ι = H.relIndex K := by
  refine Nat.card_eq_of_bijective
    (fun i ↦ (QuotientAddGroup.mk (⟨y i, hy.mem i⟩ : K) : K ⧸ H.addSubgroupOf K))
    ⟨fun i j h ↦ ?_, fun q ↦ ?_⟩
  · exact hy.eq_of_sub_mem (AddSubgroup.mem_addSubgroupOf.mp (QuotientAddGroup.eq_iff_sub_mem.mp h))
  · obtain ⟨i, hi, -⟩ := hy.existsUnique q.out q.out.property
    refine ⟨i, ?_⟩
    rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_iff_sub_mem]
    exact AddSubgroup.mem_addSubgroupOf.mpr (by simpa [neg_sub] using neg_mem hi)

/-- If `f` is constant on the cosets of `H` in `K`, its sum over a representative system is
unchanged by translation by any element of `K`. -/
theorem sum_add_left (hy : IsRepresentativeSystem y K H) [Fintype ι] {M : Type*}
    [AddCommMonoid M] {f : A → M} (hf : ∀ x ∈ K, ∀ x' ∈ K, x - x' ∈ H → f x = f x')
    {a : A} (ha : a ∈ K) :
    ∑ i : ι, f (a + y i) = ∑ i : ι, f (y i) := by
  choose σ hσ using fun i : ι ↦ (hy.existsUnique (a + y i) (add_mem ha (hy.mem i))).exists
  have h_inj : Function.Injective σ := fun i j h ↦
    hy.eq_of_sub_mem (by simpa [h] using sub_mem (hσ i) (hσ j))
  exact Fintype.sum_bijective σ h_inj.bijective_of_finite _ _ fun i ↦
    hf _ (add_mem ha (hy.mem i)) _ (hy.mem _) (hσ i)

/-- **Character orthogonality over a representative system.** For a multiplicative map `ψ : A → R`
into a commutative ring without zero divisors that is trivial on `H`, the sum `∑ i, ψ (y i)`
equals `|ι|` if `ψ` is trivial on `K`, and `0` otherwise. -/
theorem sum_character (hy : IsRepresentativeSystem y K H) [Fintype ι] {R : Type*}
    [CommRing R] [IsDomain R] {ψ : A → R}
    (h_add : ∀ x x' : A, ψ (x + x') = ψ x * ψ x') (h_triv : ∀ x ∈ H, ψ x = 1) :
    ∑ i : ι, ψ (y i) = by classical exact if ∀ x ∈ K, ψ x = 1 then (Fintype.card ι : R) else 0 := by
  classical
  split_ifs with h
  · simp [h _ (hy.mem _)]
  · obtain ⟨a, ha, ha_ne⟩ : ∃ a ∈ K, ψ a ≠ 1 := by simpa using h
    have h_congr : ∀ x ∈ K, ∀ x' ∈ K, x - x' ∈ H → ψ x = ψ x' := fun x _ x' _ h_sub ↦ by
      rw [← sub_add_cancel x x', h_add, h_triv _ h_sub, one_mul]
    have h_eq : ψ a * ∑ i : ι, ψ (y i) = ∑ i : ι, ψ (y i) := by
      rw [mul_sum]
      simpa only [← h_add] using hy.sum_add_left h_congr ha
    have h_mul : (ψ a - 1) * ∑ i : ι, ψ (y i) = 0 := by
      rw [sub_mul, one_mul, h_eq, sub_self]
    exact (mul_eq_zero.mp h_mul).resolve_left (sub_ne_zero.mpr ha_ne)

end IsRepresentativeSystem

end TauCeti
