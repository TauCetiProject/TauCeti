/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Cardinal.Partition.Pigeonhole
import Mathlib.Tactic.FinCases

/-!
# Regression examples: homogeneous sets and the partition relation

These examples exercise the partition-calculus vocabulary from a downstream module, through
public statements only:

* for the colouring `(x + y) mod 2` of the increasing pairs of `ℕ`, the even numbers form a
  homogeneous set and `{0, 1, 2}` does not;
* the pair colouring `x mod 2` (the smaller point) makes `ℕ` end-homogeneous but not homogeneous,
  and the pair colouring `y mod 2` (the larger point) does not make `{0, 1, 2}` end-homogeneous;
* `0 → (0)¹_0` and `3 → (2)¹_2` hold and `2 → (2)¹_2` fails;
* the pigeonhole instance `ℵ₁ → (ℵ₁)¹_ℵ₀`.
-/

public section

open Cardinal Set TauCeti

namespace TauCeti.Examples.Partition

/-- The increasing pair `(a, b)` of natural numbers. -/
def pair (a b : ℕ) (h : a < b) : Fin 2 ↪o ℕ :=
  .ofStrictMono ![a, b] <| Fin.strictMono_iff_lt_succ.2 fun i ↦ by
    fin_cases i
    simpa using h

@[simp] theorem pair_zero (a b : ℕ) (h : a < b) : pair a b h 0 = a := (rfl)

@[simp] theorem pair_one (a b : ℕ) (h : a < b) : pair a b h 1 = b := (rfl)

theorem pair_mem {a b : ℕ} (h : a < b) {H : Set ℕ} (ha : a ∈ H) (hb : b ∈ H) :
    ∀ k, pair a b h k ∈ H := by
  intro k
  fin_cases k
  exacts [ha, hb]

-- The even numbers are homogeneous for the colouring `(x + y) mod 2` of increasing pairs.
example : IsHomogeneousOn (fun s : Fin 2 ↪o ℕ ↦ (s 0 + s 1) % 2) {n | n % 2 = 0} := by
  refine isHomogeneousOn_def.2 fun s t hs ht ↦ ?_
  have : s 0 % 2 = 0 := hs 0
  have : s 1 % 2 = 0 := hs 1
  have : t 0 % 2 = 0 := ht 0
  have : t 1 % 2 = 0 := ht 1
  omega

-- `{0, 1, 2}` is not: the pair `(0, 1)` has colour `1` and `(0, 2)` colour `0`.
example : ¬ IsHomogeneousOn (fun s : Fin 2 ↪o ℕ ↦ (s 0 + s 1) % 2) {0, 1, 2} := fun h ↦ by
  simpa using isHomogeneousOn_def.1 h (pair 0 1 (by simp)) (pair 0 2 (by simp))
    (pair_mem _ (by simp) (by simp)) (pair_mem _ (by simp) (by simp))

-- The pair colouring by the smaller point makes `ℕ` end-homogeneous ...
example : IsEndHomogeneousOn (n := 0) (fun s : Fin 2 ↪o ℕ ↦ s 0 % 2) univ :=
  isEndHomogeneousOn_def.2 fun _ _ _ _ h ↦ by simpa using congrArg (· % 2) (h 0)

-- ... but not homogeneous: `(0, 1)` has colour `0` and `(1, 2)` colour `1`.
example : ¬ IsHomogeneousOn (fun s : Fin 2 ↪o ℕ ↦ s 0 % 2) univ := fun h ↦ by
  simpa using isHomogeneousOn_def.1 h (pair 0 1 (by simp)) (pair 1 2 (by simp))
    (fun _ ↦ trivial) (fun _ ↦ trivial)

-- The pair colouring by the larger point does not make `{0, 1, 2}` end-homogeneous: `(0, 1)` and
-- `(0, 2)` agree on their first point and have colours `1` and `0`.
example : ¬ IsEndHomogeneousOn (n := 0) (fun s : Fin 2 ↪o ℕ ↦ s 1 % 2) {0, 1, 2} := fun h ↦ by
  simpa using isEndHomogeneousOn_def.1 h (pair 0 1 (by simp)) (pair 0 2 (by simp))
    (pair_mem _ (by simp) (by simp)) (pair_mem _ (by simp) (by simp)) fun k ↦ by fin_cases k; rfl

-- `0 → (0)¹_0`: the empty set is homogeneous (Erdős and Rado's colour-witness form fails here).
example : PartitionRel.{0} 0 0 1 0 :=
  partitionRel_def.2 fun _ _ _ _ _ c ↦ ⟨∅, by simp, isHomogeneousOn_empty c⟩

-- `3 → (2)¹_2`: two colours on three points leave a fibre with two points.
example : PartitionRel.{0} 3 2 1 2 := by
  rw [partitionRel_one_iff]
  intro X D hX hD f
  obtain ⟨x, y, hxy, hne⟩ : ∃ x y, f x = f y ∧ x ≠ y := by
    by_contra! h
    have := (mk_le_of_injective fun x y hxy ↦ h x y hxy).trans hD
    rw [hX] at this
    exact absurd this (by norm_num)
  refine ⟨{x, y}, ?_, ?_⟩
  · rw [mk_insert (by simpa using hne), mk_singleton, one_add_one_eq_two]
  · rintro a (rfl | rfl) b (rfl | rfl) <;> simp [hxy]

-- `2 → (2)¹_2` fails: colouring the two points of a two-element order differently leaves no
-- homogeneous set with two points.
example : ¬ PartitionRel.{0} 2 2 1 2 := fun h ↦ by
  obtain ⟨H, hH, hc⟩ := partitionRel_one_iff.1 h Bool Bool (by simp) (by simp) id
  have : #H ≤ 1 := mk_le_one_iff_set_subsingleton.2 fun x hx y hy ↦ hc x hx y hy
  exact absurd (hH.trans this) (by norm_num)

-- The pigeonhole instance `ℵ₁ → (ℵ₁)¹_ℵ₀`.
example : PartitionRel.{0} ℵ₁ ℵ₁ 1 ℵ₀ :=
  partitionRel_one_of_isRegular isRegular_aleph_one aleph0_lt_aleph_one

end TauCeti.Examples.Partition
