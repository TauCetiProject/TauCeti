/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fundamental
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
import Mathlib.Data.Multiset.Bind

/-!
# Local ramification data and weighted partitions

For a finite extension of fields, `TauCeti.Place.localData` records the pair consisting of the
ramification index and the relative residue degree at each place above a fixed place. For an
algebraic function field, repeating each index by its residue degree gives a partition of the
extension degree. If all residue degrees are one, its parts are the unweighted ramification
indices; this applies in particular over algebraically closed constants. The local data depend
only on the fibre with its ramification indices and relative degrees, so a bijection of fibres
preserving both identifies them (`TauCeti.Place.localData_eq_of_equiv`).

The finite fibre and the sum of products are supplied by
`TauCeti.Place.finite_setOf_restrict_eq` and
`TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField`.
The partition uses Mathlib's `Nat.Partition` without discarding residue degrees.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.1, especially Theorem 3.1.11.
-/

public section

namespace TauCeti.Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']

variable (k F)

/-- The local pairs `(e, f)` at the places above `P`, with one entry per place, retaining
multiplicity when different places have the same invariants. -/
noncomputable def localData (P : Place k F) : Multiset (ℕ × ℕ) :=
  (finite_setOf_restrict_eq (k' := k') (F' := F') k F P).toFinset.val.map
    fun P' ↦ (ramificationIdx F P', relativeDegree k F P')

/-- The local data are the ramification and relative residue degrees on the finite fibre. -/
theorem localData_def (P : Place k F) :
    localData (k' := k') (F' := F') k F P =
      (finite_setOf_restrict_eq (k' := k') (F' := F') k F P).toFinset.val.map
        (fun P' ↦ (ramificationIdx F P', relativeDegree k F P')) :=
  (rfl)

/-- A pair occurs exactly when it is realized by a place above `P`. -/
@[simp]
theorem mem_localData {P : Place k F} {ef : ℕ × ℕ} :
    ef ∈ localData (k' := k') (F' := F') k F P ↔
      ∃ P' : Place k' F', P'.restrict k F = P ∧
        (ramificationIdx F P', relativeDegree k F P') = ef := by
  classical
  simp [localData_def]

/-- The number of local-data entries is the number of places above `P`. -/
@[simp]
theorem card_localData (P : Place k F) :
    (localData (k' := k') (F' := F') k F P).card =
      {P' : Place k' F' | P'.restrict k F = P}.ncard := by
  rw [localData_def, Multiset.card_map, Finset.card_val,
    Set.ncard_eq_toFinset_card _ (finite_setOf_restrict_eq k F P)]

section Transport

variable {k F} {l : Type*} {l' : Type*} {L : Type*} {L' : Type*} [Field l] [Field l'] [Field L]
  [Field L'] [Algebra l l'] [Algebra l L] [Algebra l' L'] [Algebra L L'] [Algebra l L']
  [IsScalarTower l l' L'] [IsScalarTower l L L'] [FiniteDimensional L L']

/-- **Local data are invariant under a matching of fibres**: a bijection between the places of
`F'` and those of `L'` carrying the places above `P` onto the places above `Q`, with the same
ramification indices and relative degrees, identifies the local data at `Q` with those at `P`.
Transport along an isomorphism of extensions, or along a substitution of the base field, provides
such a bijection. -/
theorem localData_eq_of_equiv (P : Place k F) (Q : Place l L) (Φ : Place k' F' ≃ Place l' L')
    (hΦ : ∀ P', (Φ P').restrict l L = Q ↔ P'.restrict k F = P)
    (he : ∀ P', P'.restrict k F = P → ramificationIdx L (Φ P') = ramificationIdx F P')
    (hf : ∀ P', P'.restrict k F = P → relativeDegree l L (Φ P') = relativeDegree k F P') :
    localData (k' := l') (F' := L') l L Q = localData (k' := k') (F' := F') k F P := by
  have hs : (finite_setOf_restrict_eq (k' := l') (F' := L') l L Q).toFinset =
      (finite_setOf_restrict_eq (k' := k') (F' := F') k F P).toFinset.map Φ.toEmbedding := by
    ext Q'
    simp only [Finset.mem_map_equiv, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    rw [← hΦ, Equiv.apply_symm_apply]
  rw [localData_def, localData_def, hs, Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl fun P' hP' ↦ ?_
  have hP' : P'.restrict k F = P := by simpa using hP'
  simp [he P' hP', hf P' hP']

end Transport

variable [Algebra.IsIntegral k k']

/-- The fundamental identity expressed in the local-data multiset. -/
theorem sum_mul_localData (hF : IsFunctionField k F) (P : Place k F) :
    ((localData (k' := k') (F' := F') k F P).map fun ef ↦ ef.1 * ef.2).sum =
      Module.finrank F F' := by
  classical
  rw [localData_def, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField k F hF P
    fun P' ↦ (finite_setOf_restrict_eq k F P).mem_toFinset

/-- The partition of `[F' : F]` in which the ramification index at a place above `P` occurs
as many times as its relative residue degree. Unlike the unweighted indices, these parts sum
to the extension degree without any rationality assumption on the places. -/
noncomputable def weightedRamificationPartition (hF : IsFunctionField k F) (P : Place k F) :
    Nat.Partition (Module.finrank F F') where
  parts := (localData (k' := k') (F' := F') k F P).bind
    fun ef ↦ Multiset.replicate ef.2 ef.1
  parts_pos hi := by
    obtain ⟨ef, hef, hi⟩ := Multiset.mem_bind.mp hi
    obtain ⟨P', -, rfl⟩ := (mem_localData k F).mp hef
    exact (Multiset.mem_replicate.mp hi).2 ▸ ramificationIdx_pos F P'
  parts_sum := by
    simpa [Multiset.sum_bind, Multiset.sum_replicate, mul_comm] using
      sum_mul_localData (k' := k') (F' := F') k F hF P

/-- The parts are obtained by repeating each ramification index by its relative residue degree. -/
theorem parts_weightedRamificationPartition (hF : IsFunctionField k F) (P : Place k F) :
    (weightedRamificationPartition (k' := k') (F' := F') k F hF P).parts =
      (localData (k' := k') (F' := F') k F P).bind
        (fun ef ↦ Multiset.replicate ef.2 ef.1) :=
  (rfl)

/-- A part is precisely a ramification index realized above `P`. Multiplicities are specified by
`parts_weightedRamificationPartition`, not by this membership statement. -/
@[simp]
theorem mem_parts_weightedRamificationPartition (hF : IsFunctionField k F)
    {P : Place k F} {e : ℕ} :
    e ∈ (weightedRamificationPartition (k' := k') (F' := F') k F hF P).parts ↔
      ∃ P' : Place k' F', P'.restrict k F = P ∧ ramificationIdx F P' = e := by
  rw [parts_weightedRamificationPartition]
  simp only [Multiset.mem_bind, mem_localData]
  constructor
  · rintro ⟨ef, ⟨P', hP', rfl⟩, he⟩
    exact ⟨P', hP', (Multiset.mem_replicate.mp he).2.symm⟩
  · rintro ⟨P', hP', rfl⟩
    exact ⟨_, ⟨P', hP', rfl⟩,
      Multiset.mem_replicate.mpr ⟨by have := one_le_relativeDegree k F P'; omega, rfl⟩⟩

/-- The number of weighted parts is the sum of the relative residue degrees. -/
theorem card_parts_weightedRamificationPartition (hF : IsFunctionField k F) (P : Place k F) :
    (weightedRamificationPartition (k' := k') (F' := F') k F hF P).parts.card =
      ((localData (k' := k') (F' := F') k F P).map Prod.snd).sum := by
  simp [parts_weightedRamificationPartition, Multiset.card_bind]

/-- When every place above `P` has relative residue degree one, the partition consists of the
unweighted ramification indices, one per place. -/
theorem parts_weightedRamificationPartition_of_relativeDegree_eq_one
    (hF : IsFunctionField k F) (P : Place k F)
    (hf : ∀ P' : Place k' F', P'.restrict k F = P → relativeDegree k F P' = 1) :
    (weightedRamificationPartition (k' := k') (F' := F') k F hF P).parts =
      (localData (k' := k') (F' := F') k F P).map Prod.fst := by
  rw [parts_weightedRamificationPartition, ← Multiset.bind_singleton]
  apply Multiset.bind_congr
  intro ef hef
  obtain ⟨P', hP', rfl⟩ := (mem_localData k F).mp hef
  simp [hf P' hP']

/-- Over algebraically closed constants the weighted partition is the unweighted multiset of
ramification indices. -/
theorem parts_weightedRamificationPartition_of_isAlgClosed [IsAlgClosed k]
    (hF : IsFunctionField k F) (P : Place k F) :
    (weightedRamificationPartition (k' := k) (F' := F') k F hF P).parts =
      (localData (k' := k) (F' := F') k F P).map Prod.fst := by
  apply parts_weightedRamificationPartition_of_relativeDegree_eq_one
  intro P' _
  have hdeg := degree_eq_degree_restrict_mul_relativeDegree k F P'
  rw [P'.degree_eq_one_of_isAlgClosed_of_isFunctionField hF.finite_extension,
    (P'.restrict k F).degree_eq_one_of_isAlgClosed_of_isFunctionField hF, one_mul] at hdeg
  exact hdeg.symm

end TauCeti.Place
