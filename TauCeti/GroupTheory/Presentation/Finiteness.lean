/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Table
public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# Finite coset certificates for group presentations

A `GroupPresentation.CosetCertificate` checks a table for a subgroup of the exact
`GroupPresentation.Group`. Signed presentation words are encoded in a doubled alphabet:
the first half consists of the generators, and the second half of their inverses.
The table uses the presentation's relators together with both inverse-cancellation relations
for each generator. A certificate may also supply signed words with proofs that they equal one
in the exact presented group.

A checked table gives finite index without assuming finiteness of the presented group.
When the subgroup is finite, it gives finiteness and the upper bound
`Nat.card P.Group ≤ Nat.card H * k`. This supplies the upper-bound step of
CFSG basic properties P0; recognition from a finite model is in `Presentation.Recognition`.
-/

public section

namespace TauCeti

namespace PresentationWord

/-- Encode a signed word using positive generators followed by inverse generators. -/
@[expose]
def toTableWord {n : ℕ} (w : PresentationWord (Fin n)) : List (Fin (n + n)) :=
  w.map fun x ↦ if x.2 then x.1.castAdd n else Fin.natAdd n x.1

/-- Evaluating the encoded word agrees with the free-group evaluation of the signed word. -/
theorem prod_toTableWord {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (w : PresentationWord (Fin n)) :
    (w.toTableWord.map (Fin.addCases g (fun i ↦ (g i)⁻¹))).prod =
      FreeGroup.lift g (FreeGroup.mk w) := by
  rw [FreeGroup.lift_mk, toTableWord, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨i, b⟩ _
  cases b <;>
    simp only [Function.comp_apply, Bool.false_eq_true, ↓reduceIte,
      Fin.addCases_left, Fin.addCases_right, Bool.cond_false, Bool.cond_true]

end PresentationWord

namespace GroupPresentation

variable (P : GroupPresentation)

/-- The presentation generators and their inverses, indexed by the table alphabet. -/
def tableGenerators : Fin (P.generatorCount + P.generatorCount) → P.Group :=
  Fin.addCases PresentedGroup.of (fun i ↦ (PresentedGroup.of i)⁻¹)

/-- The doubled alphabet still generates the exact presented group. -/
theorem closure_range_tableGenerators :
    Subgroup.closure (Set.range P.tableGenerators) = ⊤ := by
  apply top_unique
  rw [← PresentedGroup.closure_range_of P.relatorSet]
  apply Subgroup.closure_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i.castAdd P.generatorCount, by simp [tableGenerators]⟩

/-- The signed-word encoding evaluates to the canonical quotient of the free group. -/
theorem prod_toTableWord (w : PresentationWord (Fin P.generatorCount)) :
    (w.toTableWord.map P.tableGenerators).prod =
      PresentedGroup.mk P.relatorSet (FreeGroup.mk w) := by
  change (w.toTableWord.map
    (Fin.addCases PresentedGroup.of (fun i ↦ (PresentedGroup.of i)⁻¹))).prod = _
  rw [PresentationWord.prod_toTableWord]
  exact (FreeGroup.lift_unique (PresentedGroup.mk P.relatorSet) (fun _ ↦ rfl)).symm

/-- Relators for a table: the exact signed presentation relators and both cancellations.

Both cancellation orientations are included because the table checker deduces the first edge
of a scanned word. -/
@[expose]
def tableRelators : List (List (Fin (P.generatorCount + P.generatorCount))) :=
  P.relators.map PresentationWord.toTableWord ++
    (List.finRange P.generatorCount).flatMap fun i ↦
      [[i.castAdd P.generatorCount, Fin.natAdd P.generatorCount i],
       [Fin.natAdd P.generatorCount i, i.castAdd P.generatorCount]]

/-- Every relation used by the table checker holds in the exact presented group. -/
theorem prod_tableRelators :
    ∀ r ∈ P.tableRelators, (r.map P.tableGenerators).prod = 1 := by
  intro r hr
  rw [tableRelators, List.mem_append] at hr
  rcases hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [P.prod_toTableWord]
    obtain ⟨t, ht, rfl⟩ := (P.mem_relators_iff w).mp hw
    exact PresentedGroup.one_of_mem
      ((P.mem_relatorSet_iff _).mpr ⟨t, ht, t.toWord_toFreeGroup.symm⟩)
  · obtain ⟨i, -, hr⟩ := List.mem_flatMap.mp hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        tableGenerators, Fin.addCases_left, Fin.addCases_right, mul_inv_cancel, inv_mul_cancel]

/-- A checked coset table for a subgroup of the presented group.

The subgroup words need only belong to `H`; they need not generate it. In particular, one
certificate can be used with a larger subgroup whose order is easier to bound. No finiteness
assumption on `P.Group` or `H` is part of the certificate. Additional relators carry proofs in
`P.Group`; checking that they close in the finite table does not establish their validity. -/
structure CosetCertificate (H : Subgroup P.Group) (k : ℕ) where
  /-- The finite table, including its representative words. -/
  table : CosetTable (P.generatorCount + P.generatorCount) k
  /-- Signed words known to lie in the subgroup. -/
  subgroupWords : List (PresentationWord (Fin P.generatorCount))
  /-- Additional signed relators, each proved equal to one in the exact presented group.
  The empty default leaves the original relators and cancellations as the only scan words. -/
  extraRelators : {rs : List (PresentationWord (Fin P.generatorCount)) //
    ∀ w ∈ rs, PresentedGroup.mk P.relatorSet (FreeGroup.mk w) = 1} := ⟨[], by simp⟩
  /-- Edge deductions, using the doubled alphabet. -/
  deductions : List (Fin k × List (Fin (P.generatorCount + P.generatorCount)))
  /-- Every edge follows from the presentation relators, certified extras, and subgroup words. -/
  checked :
    table.check (P.tableRelators ++ extraRelators.val.map PresentationWord.toTableWord)
      (subgroupWords.map PresentationWord.toTableWord) deductions = true
  /-- Each subgroup word represents an element of the actual subgroup. -/
  subgroupWords_mem : ∀ w ∈ subgroupWords,
    PresentedGroup.mk P.relatorSet (FreeGroup.mk w) ∈ H

namespace CosetCertificate

variable {P} {H : Subgroup P.Group} {k : ℕ} (C : P.CosetCertificate H k)

include C

private theorem prod_relators :
    ∀ r ∈ P.tableRelators ++ C.extraRelators.val.map PresentationWord.toTableWord,
      (r.map P.tableGenerators).prod = 1 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact P.prod_tableRelators r hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [P.prod_toTableWord]
    exact C.extraRelators.property w hw

private theorem prod_subgroupWords :
    ∀ r ∈ C.subgroupWords.map PresentationWord.toTableWord,
      (r.map P.tableGenerators).prod ∈ H := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  rw [P.prod_toTableWord]
  exact C.subgroupWords_mem w hw

/-- The certificate bounds the index of the subgroup by the number of table rows. -/
theorem index_le : H.index ≤ k :=
  CosetTable.index_le P.closure_range_tableGenerators C.checked C.prod_relators
    C.prod_subgroupWords

/-- A checked table certifies finite index, even when the subgroup is infinite. -/
theorem finiteIndex : H.FiniteIndex :=
  CosetTable.finiteIndex P.closure_range_tableGenerators C.checked C.prod_relators
    C.prod_subgroupWords

/-- A finite subgroup and a checked finite coset table make the presented group finite. -/
theorem finite [Finite H] : Finite P.Group :=
  (Subgroup.finite_iff_finite_and_finiteIndex H).mpr ⟨inferInstance, C.finiteIndex⟩

/-- The order is at most the subgroup order times the number of table rows. -/
theorem natCard_le : Nat.card P.Group ≤ Nat.card H * k := by
  rw [← H.card_mul_index]
  exact Nat.mul_le_mul_left _ C.index_le

end CosetCertificate

end GroupPresentation

end TauCeti
