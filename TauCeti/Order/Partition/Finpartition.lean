/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Setoid.Partition
public import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Set.Finite.Range

/-!
# Finite partition helpers

This file contains general-purpose constructions and facts about finite partitions: the partition
of the top element into an element and its complement, the partition of a type into the fibres of
a map to a finite type, the associated indexed partition, cardinality bounds for common
refinements, and the behavior of intersections of parts under refinement.
-/

public section

namespace Finpartition

/-- The finite partition of the top element into an element and its complement, omitting either
part when it is bottom. -/
noncomputable def bipartition {α : Type*} [BooleanAlgebra α] [DecidableEq α] (s : α) :
    Finpartition (⊤ : α) :=
  Finpartition.ofErase {s, sᶜ} (Set.PairwiseDisjoint.supIndep (by
    simp [Set.pairwiseDisjoint_insert, disjoint_compl_right])) (by simp)

@[simp]
theorem parts_bipartition {α : Type*} [BooleanAlgebra α] [DecidableEq α] (s : α) :
    (bipartition s).parts = ({s, sᶜ} : Finset α).erase ⊥ :=
  by simp [bipartition]

/-- A bipartition has at most two parts. -/
theorem card_parts_bipartition_le {α : Type*} [BooleanAlgebra α] [DecidableEq α] (s : α) :
    (bipartition s).parts.card ≤ 2 := by
  rw [parts_bipartition]
  exact Finset.card_erase_le.trans (Finset.card_insert_le _ _ |>.trans_eq (by simp))

/-- A non-bottom element is a part of its bipartition. -/
theorem mem_bipartition_of_ne_bot {α : Type*} [BooleanAlgebra α] [DecidableEq α] {s : α}
    (hs : s ≠ ⊥) :
    s ∈ (bipartition s).parts := by
  simp [parts_bipartition, hs]

/-- The number of parts in a common refinement is at most the product of the two part counts. -/
theorem card_parts_inf_le_mul {α : Type*} [DistribLattice α] [OrderBot α] [DecidableEq α]
    {a : α} (P Q : Finpartition a) :
    (P ⊓ Q).parts.card ≤ P.parts.card * Q.parts.card := by
  rw [Finpartition.parts_inf]
  exact Finset.card_erase_le.trans
    (Finset.card_image_le.trans_eq (Finset.card_product _ _))

variable {Ω : Type*} {u : Set Ω}

section Fibers

variable {κ : Type*} [Finite κ] {g : Ω → κ} {s : Set Ω}

open Classical in
/-- The finite partition of `Set.univ` into the nonempty fibres of a map to a finite type. -/
noncomputable def ofFibers (g : Ω → κ) : Finpartition (Set.univ : Set Ω) :=
  ofErase (Set.finite_range fun i : κ => g ⁻¹' {i}).toFinset
    (Finset.supIndep_iff_pairwiseDisjoint.mpr fun s hs t ht hst => by
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hs ht
      obtain ⟨i, rfl⟩ := hs
      obtain ⟨j, rfl⟩ := ht
      exact (Set.disjoint_singleton.2 fun hij =>
        hst (congrArg (fun k => g ⁻¹' {k}) hij)).preimage g)
    (by
      rw [Finset.sup_id_set_eq_sUnion, Set.Finite.coe_toFinset, Set.sUnion_range]
      exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨g x, rfl⟩)

/-- The parts of `Finpartition.ofFibers g` are the fibres of `g` through the points of `Ω`. -/
@[simp]
theorem mem_ofFibers_parts : s ∈ (ofFibers g).parts ↔ ∃ x, g ⁻¹' {g x} = s := by
  classical
  rw [ofFibers, ofErase_parts, Finset.mem_erase, Set.Finite.mem_toFinset, Set.bot_eq_empty,
    ← Set.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨⟨x, hx⟩, i, rfl⟩
    exact ⟨x, by rw [Set.mem_preimage, Set.mem_singleton_iff] at hx; rw [hx]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, rfl⟩, g x, rfl⟩

/-- The map `g` is constant on every part of `Finpartition.ofFibers g`. -/
theorem apply_eq_of_mem_ofFibers_parts (hs : s ∈ (ofFibers g).parts) {x x' : Ω} (hx : x ∈ s)
    (hx' : x' ∈ s) : g x = g x' := by
  obtain ⟨y, rfl⟩ := mem_ofFibers_parts.1 hs
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
  rw [hx, hx']

end Fibers

/-- The indexed partition associated to a finite partition of `Set.univ`, indexed by its actual
parts.  Its `index` sends each point to the unique part containing it. -/
noncomputable def indexedPartition (P : Finpartition (Set.univ : Set Ω)) :
    IndexedPartition (fun p : P.parts => (p : Set Ω)) :=
  IndexedPartition.mk' _
    (fun p q hne => P.disjoint p.property q.property fun h => hne (Subtype.ext h))
    (fun p => Set.nonempty_iff_ne_empty.mpr (P.ne_bot p.property))
    (fun x => by
      obtain ⟨p, ⟨hp, hxp⟩, _⟩ := P.isPartition_parts.2 x
      exact ⟨⟨p, hp⟩, hxp⟩)

/-- Under refinement, a part of the finer partition is either contained in a given part of the
coarser one or disjoint from it. -/
theorem inter_part_eq_self_or_eq_empty_of_le {P Q : Finpartition u} (href : Q ≤ P)
    {r : Set Ω} (hr : r ∈ Q.parts) {p : Set Ω} (hp : p ∈ P.parts) :
    r ∩ p = r ∨ r ∩ p = ∅ := by
  obtain ⟨p', hp', hrp'⟩ := href hr
  by_cases h : p' = p
  · exact Or.inl (Set.inter_eq_self_of_subset_left (h ▸ hrp'))
  · refine Or.inr (Set.eq_empty_of_subset_empty fun x hx => ?_)
    exact absurd hx.2 (Set.disjoint_left.mp (P.disjoint hp' hp h) (hrp' hx.1))

end Finpartition
