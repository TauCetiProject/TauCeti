/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.SizeFormula
public import TauCeti.RepresentationTheory.CharacterTable.GeneratingCount
public import TauCeti.GroupTheory.Perm.ConjClass

/-!
# Generating counts by cycle type

A cycle type in a permutation subgroup can contain several conjugacy classes of that subgroup.
Consequently, counting product-one triples with prescribed cycle types requires a sum over three
sets of conjugacy classes. The generating count below applies this sum to the subgroup-lattice
generating counts, and identifies it with the generating triples of a passport. Combined with the
normalizer formula, this computes passport size from counts internal to its monodromy group.

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
/-- The product-one triples of `G` that generate `G` and have the prescribed cycle types. -/
noncomputable def _root_.Subgroup.generatingTriplesOfType
    (G : Subgroup (Perm α)) (lam0 lam1 laminf : Multiset ℕ) :
    Finset (G × G × G) :=
  Finset.univ.filter fun p => p.2.2 * p.2.1 * p.1 = 1 ∧
    productOneGeneratedSubgroup p = ⊤ ∧
    (p.1 : Perm α).fullCycleType = lam0 ∧
    (p.2.1 : Perm α).fullCycleType = lam1 ∧
    (p.2.2 : Perm α).fullCycleType = laminf

open Classical in
@[simp] theorem _root_.Subgroup.mem_generatingTriplesOfType
    (G : Subgroup (Perm α)) {lam0 lam1 laminf : Multiset ℕ} {p : G × G × G} :
    p ∈ G.generatingTriplesOfType lam0 lam1 laminf ↔
      p.2.2 * p.2.1 * p.1 = 1 ∧ productOneGeneratedSubgroup p = ⊤ ∧
      (p.1 : Perm α).fullCycleType = lam0 ∧
      (p.2.1 : Perm α).fullCycleType = lam1 ∧
      (p.2.2 : Perm α).fullCycleType = laminf := by
  simp [Subgroup.generatingTriplesOfType]

/-- Summing the generating counts over the three class refinements counts exactly the triples
of the prescribed cycle types. -/
theorem _root_.Subgroup.card_generatingTriplesOfType
    (G : Subgroup (Perm α)) (lam0 lam1 laminf : Multiset ℕ) :
    (G.generatingTriplesOfType lam0 lam1 laminf).card =
      G.genCountType lam0 lam1 laminf := by
  classical
  let index : Finset ((ConjClasses G × ConjClasses G) × ConjClasses G) :=
    (G.classesOfFullCycleType lam0 |>.product (G.classesOfFullCycleType lam1)).product
      (G.classesOfFullCycleType laminf)
  let classOf : G × G × G → (ConjClasses G × ConjClasses G) × ConjClasses G :=
    fun p => ((ConjClasses.mk p.1, ConjClasses.mk p.2.1), ConjClasses.mk p.2.2)
  have hmaps : ((G.generatingTriplesOfType lam0 lam1 laminf : Finset (G × G × G)) :
      Set (G × G × G)).MapsTo classOf index := by
    intro p hp
    obtain ⟨_, _, h0, h1, hi⟩ := G.mem_generatingTriplesOfType.mp hp
    -- `MapsTo` coerces the target finset to a set; expose finset membership before splitting
    -- the product index into its three class conditions.
    change classOf p ∈ index
    change ((ConjClasses.mk p.1, ConjClasses.mk p.2.1), ConjClasses.mk p.2.2) ∈
      ((G.classesOfFullCycleType lam0) ×ˢ (G.classesOfFullCycleType lam1)) ×ˢ
        (G.classesOfFullCycleType laminf)
    simp only [Finset.mem_product, Subgroup.mem_classesOfFullCycleType_mk]
    exact ⟨⟨h0, h1⟩, hi⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  unfold index
  simp only [Finset.product_eq_sprod, Finset.sum_product]
  -- The product-sum rewrite leaves the three class binders paired; present them separately.
  change (∑ C0 ∈ G.classesOfFullCycleType lam0,
    ∑ C1 ∈ G.classesOfFullCycleType lam1,
      ∑ Cinf ∈ G.classesOfFullCycleType laminf,
        {p ∈ G.generatingTriplesOfType lam0 lam1 laminf |
          classOf p = ((C0, C1), Cinf)}.card) =
      G.genCountType lam0 lam1 laminf
  unfold Subgroup.genCountType
  apply Finset.sum_congr rfl
  intro C0 h0
  apply Finset.sum_congr rfl
  intro C1 h1
  apply Finset.sum_congr rfl
  intro Cinf hi
  congr 1
  ext p
  simp only [Finset.mem_filter, G.mem_generatingTriplesOfType,
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

namespace PassportSpec

variable {n : ℕ}

private theorem generatedSubgroup_subtype_eq_top_iff (P : PassportSpec n)
    (p : P.G × P.G × P.G) :
    productOneGeneratedSubgroup p = ⊤ ↔
      Subgroup.closure {(p.1 : Perm (Fin n)), (p.2.1 : Perm (Fin n))} = P.G := by
  rw [← Subgroup.map_subtype_inj]
  rw [← productOneGeneratedSubgroup_map P.G.subtype p,
    productOneGeneratedSubgroup_def]
  rw [← MonoidHom.range_eq_map]
  simp

/-- The class sum `genCountType` is the number of generating triples of a passport, before
quotienting by its normalizer. -/
theorem card_generatingTriples_eq_genCountType (P : PassportSpec n) :
    P.generatingTriples.card = P.G.genCountType P.lam0 P.lam1 P.laminf := by
  classical
  rw [← P.G.card_generatingTriplesOfType]
  let lift : (p : Perm (Fin n) × Perm (Fin n) × Perm (Fin n)) →
      p ∈ P.generatingTriples → P.G × P.G × P.G := fun p hp => by
    obtain ⟨hprod, hgen, -⟩ := mem_generatingTriples.mp hp
    have hx : p.1 ∈ P.G := by
      rw [← hgen]
      exact Subgroup.subset_closure (by simp)
    have hy : p.2.1 ∈ P.G := by
      rw [← hgen]
      exact Subgroup.subset_closure (by simp)
    have hzrel : p.2.2 * (p.2.1 * p.1) = 1 := by
      simpa only [mul_assoc] using hprod
    have hz : p.2.2 ∈ P.G := by
      rw [eq_inv_of_mul_eq_one_left hzrel]
      exact P.G.inv_mem (P.G.mul_mem hy hx)
    exact (⟨p.1, hx⟩, ⟨p.2.1, hy⟩, ⟨p.2.2, hz⟩)
  refine Finset.card_bij lift ?_ ?_ ?_
  · intro p hp
    obtain ⟨hprod, hgen, htypes⟩ := mem_generatingTriples.mp hp
    apply P.G.mem_generatingTriplesOfType.mpr
    refine ⟨?_, (generatedSubgroup_subtype_eq_top_iff P (lift p hp)).mpr ?_, ?_, ?_, ?_⟩
    · apply Subtype.ext
      exact hprod
    · simpa only [lift] using hgen
    · simpa only [lift] using congrArg Prod.fst htypes
    · simpa only [lift] using congrArg (fun t => t.2.1) htypes
    · simpa only [lift] using congrArg (fun t => t.2.2) htypes
  · intro p hp q hq heq
    apply Prod.ext
    · exact congrArg (fun x : P.G × P.G × P.G => (x.1 : Perm (Fin n))) heq
    apply Prod.ext
    · exact congrArg (fun x : P.G × P.G × P.G => (x.2.1 : Perm (Fin n))) heq
    · exact congrArg (fun x : P.G × P.G × P.G => (x.2.2 : Perm (Fin n))) heq
  · intro q hq
    obtain ⟨hprod, hgen, h0, h1, hi⟩ := P.G.mem_generatingTriplesOfType.mp hq
    let p : Perm (Fin n) × Perm (Fin n) × Perm (Fin n) :=
      ((q.1 : Perm (Fin n)), (q.2.1 : Perm (Fin n)), (q.2.2 : Perm (Fin n)))
    have hp : p ∈ P.generatingTriples := by
      apply mem_generatingTriples.mpr
      refine ⟨?_, (generatedSubgroup_subtype_eq_top_iff P q).mp hgen, ?_⟩
      · exact congrArg Subtype.val hprod
      · exact Prod.ext h0 (Prod.ext h1 hi)
    refine ⟨p, hp, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      rfl
    apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- The normalizer order divides the generating count by cycle type times the centralizer
order. This is the exact divisibility behind the natural-number passport-size formula. -/
theorem card_normalizer_dvd_genCountType_mul_card_centralizer (P : PassportSpec n) :
    Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) ∣
      P.G.genCountType P.lam0 P.lam1 P.laminf *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) := by
  rw [← P.card_generatingTriples_eq_genCountType, ← P.card_generatingTriples]
  exact P.card_normalizer_dvd_card_generatingTriple_mul_card_centralizer

/-- A passport's size is the generating count by cycle type, multiplied by the centralizer
order and divided by the normalizer order. -/
theorem passportSize_eq_genCountType_mul_card_centralizer_div_card_normalizer
    (P : PassportSpec n) (hn : n ≠ 0) (hG : MulAction.IsPretransitive P.G (Fin n)) :
    P.passportSize =
      P.G.genCountType P.lam0 P.lam1 P.laminf *
        Nat.card (Subgroup.centralizer (P.G : Set (Perm (Fin n)))) /
          Nat.card (Subgroup.normalizer (P.G : Set (Perm (Fin n)))) := by
  rw [← P.card_generatingTriples_eq_genCountType]
  exact P.passportSize_eq_card_generatingTriples_mul_card_centralizer_div_card_normalizer hn hG

end PassportSpec

end TauCeti
