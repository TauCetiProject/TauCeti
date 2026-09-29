/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GeneratingCount
public import TauCeti.GroupTheory.Perm.ConjClass

/-!
# Generating counts by cycle type

A cycle type in a permutation subgroup can contain several conjugacy classes of that subgroup.
Consequently, counting product-one triples with prescribed cycle types requires a sum over three
sets of conjugacy classes. The generating count below applies this sum to the subgroup-lattice
generating counts, and identifies it with generating triples of the prescribed cycle types.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, §1.5.
* M. Musty, S. Schiavone, J. Sijsling and J. Voight, *A database of Belyi maps*, §2.
-/

open Equiv

public section

namespace TauCeti

variable {α : Type*} [Fintype α] [DecidableEq α]

open scoped Classical in
/-- The number of product-one triples generating `G` with three specified full cycle types.
Each type is refined into the conjugacy classes of `G` that it meets. -/
noncomputable def _root_.Subgroup.genCountType (G : Subgroup (Perm α))
    (lam0 lam1 laminf : Multiset ℕ) : ℕ :=
  ∑ C0 ∈ G.classesOfFullCycleType lam0,
    ∑ C1 ∈ G.classesOfFullCycleType lam1,
      ∑ Cinf ∈ G.classesOfFullCycleType laminf,
        (generatingProductOneTriples C0 C1 Cinf ⊤).card

open scoped Classical in
/-- The class-sum formula for the generating count with prescribed full cycle types. -/
theorem _root_.Subgroup.genCountType_def (G : Subgroup (Perm α))
    (lam0 lam1 laminf : Multiset ℕ) :
    G.genCountType lam0 lam1 laminf =
      ∑ C0 ∈ G.classesOfFullCycleType lam0,
        ∑ C1 ∈ G.classesOfFullCycleType lam1,
          ∑ Cinf ∈ G.classesOfFullCycleType laminf,
            (generatingProductOneTriples C0 C1 Cinf ⊤).card := (rfl)

open scoped Classical in
/-- The product-one triples of `G` that generate `G` and have the prescribed cycle types. -/
noncomputable def _root_.Subgroup.generatingTriplesOfFullCycleType
    (G : Subgroup (Perm α)) (lam0 lam1 laminf : Multiset ℕ) :
    Finset (G × G × G) :=
  Finset.univ.filter fun p => p.2.2 * p.2.1 * p.1 = 1 ∧
    productOneGeneratedSubgroup p = ⊤ ∧
    (p.1 : Perm α).fullCycleType = lam0 ∧
    (p.2.1 : Perm α).fullCycleType = lam1 ∧
    (p.2.2 : Perm α).fullCycleType = laminf

open Classical in
@[simp] theorem _root_.Subgroup.mem_generatingTriplesOfFullCycleType
    (G : Subgroup (Perm α)) {lam0 lam1 laminf : Multiset ℕ} {p : G × G × G} :
    p ∈ G.generatingTriplesOfFullCycleType lam0 lam1 laminf ↔
      p.2.2 * p.2.1 * p.1 = 1 ∧ productOneGeneratedSubgroup p = ⊤ ∧
      (p.1 : Perm α).fullCycleType = lam0 ∧
      (p.2.1 : Perm α).fullCycleType = lam1 ∧
      (p.2.2 : Perm α).fullCycleType = laminf := by
  simp [Subgroup.generatingTriplesOfFullCycleType]

/-- Summing the generating counts over the three class refinements counts exactly the triples
of the prescribed cycle types. -/
theorem _root_.Subgroup.card_generatingTriplesOfFullCycleType
    (G : Subgroup (Perm α)) (lam0 lam1 laminf : Multiset ℕ) :
    (G.generatingTriplesOfFullCycleType lam0 lam1 laminf).card =
      G.genCountType lam0 lam1 laminf := by
  classical
  let index : Finset ((ConjClasses G × ConjClasses G) × ConjClasses G) :=
    (G.classesOfFullCycleType lam0 |>.product (G.classesOfFullCycleType lam1)).product
      (G.classesOfFullCycleType laminf)
  let classOf : G × G × G → (ConjClasses G × ConjClasses G) × ConjClasses G :=
    fun p => ((ConjClasses.mk p.1, ConjClasses.mk p.2.1), ConjClasses.mk p.2.2)
  have hmaps : ((G.generatingTriplesOfFullCycleType lam0 lam1 laminf : Finset (G × G × G)) :
      Set (G × G × G)).MapsTo classOf index := by
    intro p hp
    obtain ⟨_, _, h0, h1, hi⟩ := G.mem_generatingTriplesOfFullCycleType.mp hp
    -- `MapsTo` coerces the index finset to a set; recover finset membership first.
    change classOf p ∈ index
    change ((ConjClasses.mk p.1, ConjClasses.mk p.2.1), ConjClasses.mk p.2.2) ∈
      ((G.classesOfFullCycleType lam0) ×ˢ (G.classesOfFullCycleType lam1)) ×ˢ
        (G.classesOfFullCycleType laminf)
    simp only [Finset.mem_product, Subgroup.mem_classesOfFullCycleType_mk]
    exact ⟨⟨h0, h1⟩, hi⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  simp only [index, Finset.product_eq_sprod, Finset.sum_product,
    Subgroup.genCountType_def]
  apply Finset.sum_congr rfl
  intro C0 h0
  apply Finset.sum_congr rfl
  intro C1 h1
  apply Finset.sum_congr rfl
  intro Cinf hi
  congr 1
  ext p
  simp only [Finset.mem_filter, G.mem_generatingTriplesOfFullCycleType,
    mem_generatingProductOneTriples, mem_productOneTriples]
  constructor
  · rintro ⟨⟨hprod, hgen, hp0, hp1, hpi⟩, hclasses⟩
    have hc0 : ConjClasses.mk p.1 = C0 := congrArg (fun x => x.1.1) hclasses
    have hc1 : ConjClasses.mk p.2.1 = C1 := congrArg (fun x => x.1.2) hclasses
    have hci : ConjClasses.mk p.2.2 = Cinf := congrArg (fun x => x.2) hclasses
    exact ⟨⟨hc0, hc1, hci, hprod⟩, hgen⟩
  · rintro ⟨⟨hc0, hc1, hci, hprod⟩, hgen⟩
    have hp0 := (G.mem_classesOfFullCycleType_mk lam0 p.1).mp (hc0 ▸ h0)
    have hp1 := (G.mem_classesOfFullCycleType_mk lam1 p.2.1).mp (hc1 ▸ h1)
    have hpi := (G.mem_classesOfFullCycleType_mk laminf p.2.2).mp (hci ▸ hi)
    exact ⟨⟨hprod, hgen, hp0, hp1, hpi⟩, by simp [classOf, hc0, hc1, hci]⟩

end TauCeti
