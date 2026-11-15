/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GeneratingCount.Basic
public import TauCeti.Algebra.Group.Subgroup.Conjugates

/-!
# Generating counts grouped by subgroup conjugacy

Simultaneous conjugation preserves the ambient conjugacy classes of a product-one triple
and conjugates the subgroup it generates. Thus generating counts are constant on subgroup
conjugacy classes. The subgroup-lattice partition can be grouped by these classes, with
multiplicity the index of the normalizer, not the index of the subgroup itself.

The classes of entries are always those of the ambient group. In particular, restricting
an ambient class to a subgroup need not give a single class of that subgroup.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications* (2004), §5.3.
-/

public section

namespace TauCeti

open scoped Pointwise

variable {G : Type*} [Group G] [Fintype G]

open scoped Classical in
/-- Conjugating the specified subgroup does not change its generating count for three fixed
ambient conjugacy classes. -/
@[simp] theorem card_generatingProductOneTriples_map_conj
    (C0 C1 Cinf : ConjClasses G) (H : Subgroup G) (g : G) :
    (generatingProductOneTriples C0 C1 Cinf (H.map (MulAut.conj g))).card =
      (generatingProductOneTriples C0 C1 Cinf H).card := by
  classical
  let f := MulAut.conj g
  have hclass (x : G) : ConjClasses.mk (f x) = ConjClasses.mk x :=
    (f.smul_conjClasses_mk x).symm.trans (mulAut_conj_smul_conjClasses g _)
  have hmem (p : G × G × G) :
      (f p.1, f p.2.1, f p.2.2) ∈ generatingProductOneTriples C0 C1 Cinf (H.map f) ↔
        p ∈ generatingProductOneTriples C0 C1 Cinf H := by
    have hrel : f p.2.2 * f p.2.1 * f p.1 = 1 ↔ p.2.2 * p.2.1 * p.1 = 1 := by
      simpa only [map_mul, map_one] using
        (f.injective.eq_iff (a := p.2.2 * p.2.1 * p.1) (b := 1))
    have hgen : productOneGeneratedSubgroup (f p.1, f p.2.1, f p.2.2) =
        (productOneGeneratedSubgroup p).map f :=
      productOneGeneratedSubgroup_map f.toMonoidHom p
    have hinj : Function.Injective (Subgroup.map (f : G →* G)) :=
      Subgroup.map_injective f.injective
    simp only [mem_generatingProductOneTriples, mem_productOneTriples, hclass,
      hgen, hrel, hinj.eq_iff]
  exact (Finset.card_equiv (f.toEquiv.prodCongr (f.toEquiv.prodCongr f.toEquiv))
    (fun p ↦ (hmem p).symm)).symm

open scoped Classical in
/-- The product-one triples in `H` are counted by conjugacy classes of subgroups of `H`.
The multiplicity of `K ≤ H` is `[H : N_H(K)]`, so the subgroup-index bookkeeping is
`[H : K] = [H : N_H(K)] * [N_H(K) : K]`, not a weight of `[H : K]`. The three entry
classes remain classes of the ambient group `G`. -/
theorem card_productOneTriplesIn_eq_sum_conjugacy_generating
    (C0 C1 Cinf : ConjClasses G) (H : Subgroup G) :
    (productOneTriplesIn C0 C1 Cinf H).card =
      ∑ ω : MulAction.orbitRel.Quotient (ConjAct H) (Subgroup H),
        (generatingProductOneTriples C0 C1 Cinf (ω.out.map H.subtype)).card *
          (Subgroup.normalizer (ω.out : Set H)).index := by
  classical
  have hsum : (productOneTriplesIn C0 C1 Cinf H).card =
      ∑ K : Subgroup H, (generatingProductOneTriples C0 C1 Cinf (K.map H.subtype)).card := by
    rw [card_productOneTriplesIn_eq_sum_generating, ← Finset.sum_subtype_eq_sum_filter]
    simpa only [Finset.subtype_univ] using
      (Fintype.sum_equiv (Subgroup.MapSubtype.orderIso H).toEquiv
        (fun K ↦ (generatingProductOneTriples C0 C1 Cinf (K.map H.subtype)).card)
        (fun K ↦ (generatingProductOneTriples C0 C1 Cinf K.1).card)
        (fun K ↦ congrArg (fun J ↦ (generatingProductOneTriples C0 C1 Cinf J).card)
          (Subgroup.MapSubtype.orderIso_apply_coe H K).symm)).symm
  have hinvariant (g : H) (K : Subgroup H) :
      (generatingProductOneTriples C0 C1 Cinf
        ((K.map (MulAut.conj g)).map H.subtype)).card =
        (generatingProductOneTriples C0 C1 Cinf (K.map H.subtype)).card := by
    have hmap : (K.map (MulAut.conj g)).map H.subtype =
        (K.map H.subtype).map (MulAut.conj (g : G)) :=
      K.map_map_conj H.subtype g
    rw [hmap, card_generatingProductOneTriples_map_conj]
  rw [hsum, sum_subgroups_eq_sum_conjugacy _ hinvariant]
  simp only [smul_eq_mul, mul_comm]

open scoped Classical in
/-- The total product-one count is a sum over conjugacy classes of subgroups. Each generating
count is multiplied by the number of conjugates of its subgroup, the normalizer index. -/
theorem card_productOneTriples_eq_sum_conjugacy_generating (C0 C1 Cinf : ConjClasses G) :
    (productOneTriples C0 C1 Cinf).card =
      ∑ ω : MulAction.orbitRel.Quotient (ConjAct G) (Subgroup G),
        (generatingProductOneTriples C0 C1 Cinf ω.out).card *
          (Subgroup.normalizer (ω.out : Set G)).index := by
  classical
  rw [card_productOneTriples_eq_sum_generating, sum_subgroups_eq_sum_conjugacy
    (fun H ↦ (generatingProductOneTriples C0 C1 Cinf H).card)
    (fun g H ↦ card_generatingProductOneTriples_map_conj C0 C1 Cinf H g)]
  simp only [smul_eq_mul, mul_comm]

end TauCeti
