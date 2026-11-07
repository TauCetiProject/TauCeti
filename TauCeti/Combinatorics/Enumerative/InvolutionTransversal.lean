/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Set.Card

/-!
# Transversals of a fixed-point-free involution on a finite set

Let `f : α → α` map a finite set `S` to itself, involutively and without fixed points, so that
`S` is partitioned into the two-element orbits `{a, f a}`. A *transversal* of `f` on `S` is a
subset `T ⊆ S` meeting each orbit exactly once; equivalently, `a ∈ T ↔ f a ∉ T` for every
`a ∈ S`.

This file introduces `TauCeti.IsInvolutionTransversal`, provides the two ways of recognising a
transversal (by the defining equivalence, or from a covering by `T` and its image), records the
resulting splitting of a product over `S`, and counts the transversals: there are `2 ^ (#S / 2)`
of them, one binary choice per orbit.

The counting theorem is the combinatorial half of `TauCeti.ncard_setOf_mul_map_eq_prod`, where
`f` is the action of a ring endomorphism, acting involutively on a set of primes of a Dedekind
domain, and a transversal picks one prime from each conjugate pair.

A fixed-point-free involution of a whole type is a perfect matching in the sense of
`TauCeti.IsPerfectMatching`; the notion here is its relative form, carried by a `Finset` rather
than by a type, which is what the arithmetic application supplies.

The induction used for the count — strip off one orbit, doubling the number of transversals —
is the one in `exists_transversal_family` of the formalization
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), written for Alpöge's
disproof of the uniform-constant Erdős unit-distance conjecture, where it is run on ideals of a
CM field rather than on an abstract finite set.

## Main definitions

* `TauCeti.IsInvolutionTransversal`: `T` meets every orbit `{a, f a}`, `a ∈ S`, exactly once.

## Main results

* `TauCeti.isInvolutionTransversal_of_cover`: a subset disjoint from its image and covering `S`
  together with it is a transversal.
* `TauCeti.IsInvolutionTransversal.prod_mul_prod_comp`: a transversal splits a product over `S`
  into the product over `T` and the product over `T` of the composite with `f`.
* `TauCeti.ncard_setOf_isInvolutionTransversal`: there are `2 ^ (#S / 2)` transversals.
-/

public section

namespace TauCeti

variable {α : Type*} {f : α → α} {S T : Finset α}

/-- `T` is a transversal of the involution `f` on the finite set `S`: a subset of `S` containing
exactly one of `a` and `f a` for every `a ∈ S`. -/
structure IsInvolutionTransversal (f : α → α) (S T : Finset α) : Prop where
  /-- A transversal is a subset of the set it is a transversal of. -/
  subset : T ⊆ S
  /-- A transversal contains exactly one element of each orbit. -/
  mem_iff_notMem : ∀ a ∈ S, (a ∈ T ↔ f a ∉ T)

namespace IsInvolutionTransversal

/-- A transversal omits the partner of each of its elements. -/
theorem map_notMem_of_mem (hT : IsInvolutionTransversal f S T) {a : α} (ha : a ∈ S)
    (haT : a ∈ T) :
    f a ∉ T := (hT.mem_iff_notMem a ha).1 haT

/-- A transversal contains the partner of each element of `S` it omits. -/
theorem map_mem_of_notMem (hT : IsInvolutionTransversal f S T) {a : α} (ha : a ∈ S)
    (haT : a ∉ T) :
    f a ∈ T := by
  by_contra h
  exact haT ((hT.mem_iff_notMem a ha).2 h)

end IsInvolutionTransversal

/-- A subset of `S` disjoint from its image and covering `S` together with it is a transversal. -/
theorem isInvolutionTransversal_of_cover (hinvol : ∀ a ∈ S, f (f a) = a) (hsub : T ⊆ S)
    (hdisj : ∀ a ∈ T, f a ∉ T) (hcover : ∀ a ∈ S, a ∈ T ∨ ∃ b ∈ T, f b = a) :
    IsInvolutionTransversal f S T where
  subset := hsub
  mem_iff_notMem a ha := by
    refine ⟨hdisj a, fun hfa => ?_⟩
    obtain haT | ⟨b, hbT, hb⟩ := hcover a ha
    · exact haT
    · rw [← hb, hinvol b (hsub hbT)] at hfa
      exact absurd hbT hfa

/-- A transversal of `f` on `S` splits a product over `S`: the factors indexed by `T` and the
factors indexed by its `f`-image together exhaust `S`. -/
theorem IsInvolutionTransversal.prod_mul_prod_comp (hT : IsInvolutionTransversal f S T)
    {M : Type*} [CommMonoid M] (g : α → M) (hmaps : ∀ a ∈ S, f a ∈ S)
    (hinvol : ∀ a ∈ S, f (f a) = a) :
    (∏ a ∈ T, g a) * (∏ a ∈ T, g (f a)) = ∏ a ∈ S, g a := by
  classical
  have hinj : Set.InjOn f T := fun x hx y hy hxy => by
    rw [← hinvol x (hT.subset hx), ← hinvol y (hT.subset hy), hxy]
  rw [← Finset.prod_image hinj, ← Finset.prod_union]
  · congr 1
    refine Finset.Subset.antisymm ?_ fun a ha => ?_
    · refine Finset.union_subset hT.subset fun a ha => ?_
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      exact hmaps b (hT.subset hb)
    · by_cases haT : a ∈ T
      · exact Finset.mem_union_left _ haT
      · exact Finset.mem_union_right _
          (Finset.mem_image.2 ⟨f a, hT.map_mem_of_notMem ha haT, hinvol a ha⟩)
  · refine Finset.disjoint_left.2 fun a haT ha => ?_
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
    exact hT.map_notMem_of_mem (hT.subset hb) hb haT

/-- There are only finitely many transversals, since each is a subset of `S`. -/
theorem finite_setOf_isInvolutionTransversal (f : α → α) (S : Finset α) :
    {T : Finset α | IsInvolutionTransversal f S T}.Finite :=
  Set.Finite.subset S.powerset.finite_toSet fun _ hT => Finset.mem_powerset.2 hT.subset

/-- Membership in `S` with the orbit `{a, f a}` removed. -/
private lemma mem_sdiff_pair_iff [DecidableEq α] {a x : α} :
    x ∈ S \ {a, f a} ↔ x ∈ S ∧ x ≠ a ∧ x ≠ f a := by
  simp

/-- Removing one orbit `{a, f a}` of an involution preserves its properties on the rest. -/
private lemma map_mem_sdiff_pair [DecidableEq α]
    (hmaps : ∀ x ∈ S, f x ∈ S) (hinvol : ∀ x ∈ S, f (f x) = x)
    {a x : α} (ha : a ∈ S) (hx : x ∈ S \ {a, f a}) : f x ∈ S \ {a, f a} := by
  obtain ⟨hxS, hxa, hxb⟩ := mem_sdiff_pair_iff.1 hx
  refine mem_sdiff_pair_iff.2 ⟨hmaps x hxS, fun h => hxb ?_, fun h => hxa ?_⟩
  · rw [← hinvol x hxS, h]
  · rw [← hinvol x hxS, h, hinvol a ha]

/-- Adjoining an element `c` of the orbit `{a, f a}` to a transversal of `S \ {a, f a}` gives a
transversal of `S`. -/
private lemma isInvolutionTransversal_insert_of_sdiff_pair [DecidableEq α]
    (hinvol : ∀ x ∈ S, f (f x) = x)
    (hfree : ∀ x ∈ S, f x ≠ x) {a c : α} (hc : c ∈ S)
    (hcpair : ({c, f c} : Finset α) = {a, f a}) {T' : Finset α}
    (hT' : IsInvolutionTransversal f (S \ {a, f a}) T') :
    IsInvolutionTransversal f S (insert c T') := by
  have hS'c : S \ {a, f a} = S \ {c, f c} := by rw [hcpair]
  have hfcT' : f c ∉ T' := fun h => (by simp [hS'c] : f c ∉ S \ {a, f a}) (hT'.subset h)
  refine ⟨Finset.insert_subset hc (hT'.subset.trans Finset.sdiff_subset), fun x hx => ?_⟩
  by_cases hxc : x = c
  · subst hxc
    simp [Finset.mem_insert, hfree x hx, hfcT']
  by_cases hxfc : x = f c
  · subst hxfc
    simp [Finset.mem_insert, hinvol c hc, hfree c hc, hfcT']
  have hxS' : x ∈ S \ {a, f a} := by rw [hS'c]; simp [hx, hxc, hxfc]
  have hfxc : f x ≠ c := fun h => hxfc (by rw [← hinvol x hx, h])
  rw [Finset.mem_insert, Finset.mem_insert]
  simp only [hxc, hfxc, false_or]
  exact hT'.mem_iff_notMem x hxS'

/-- Restricting a transversal of `S` to `S \ {a, f a}` gives a transversal there. -/
private lemma isInvolutionTransversal_sdiff_pair [DecidableEq α] (hmaps : ∀ x ∈ S, f x ∈ S)
    (hinvol : ∀ x ∈ S, f (f x) = x) {a : α} (ha : a ∈ S) (hT : IsInvolutionTransversal f S T) :
    IsInvolutionTransversal f (S \ {a, f a}) (T \ {a, f a}) := by
  refine ⟨Finset.sdiff_subset_sdiff hT.subset (Finset.Subset.refl _), fun x hx => ?_⟩
  obtain ⟨hxS, hxa, hxb⟩ := mem_sdiff_pair_iff.1 hx
  obtain ⟨_, hfxa, hfxb⟩ := mem_sdiff_pair_iff.1 (map_mem_sdiff_pair hmaps hinvol ha hx)
  rw [Finset.mem_sdiff, Finset.mem_sdiff]
  simp only [Finset.mem_insert, Finset.mem_singleton, hxa, hxb, hfxa, hfxb, or_self,
    not_false_eq_true, and_true]
  exact hT.mem_iff_notMem x hxS

/-- The transversals of `S` are the two extensions, by `a` or by `f a`, of the transversals of
`S \ {a, f a}`. -/
private lemma setOf_isInvolutionTransversal_eq_image_union [DecidableEq α]
    (hmaps : ∀ x ∈ S, f x ∈ S)
    (hinvol : ∀ x ∈ S, f (f x) = x) (hfree : ∀ x ∈ S, f x ≠ x) {a : α} (ha : a ∈ S) :
    {T : Finset α | IsInvolutionTransversal f S T} =
      (insert a '' {T : Finset α | IsInvolutionTransversal f (S \ {a, f a}) T}) ∪
        (insert (f a) '' {T : Finset α | IsInvolutionTransversal f (S \ {a, f a}) T}) := by
  ext T
  constructor
  · intro hT
    by_cases haT : a ∈ T
    · have herase : T \ {a, f a} = T.erase a := by
        have hfaT : f a ∉ T := hT.map_notMem_of_mem ha haT
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        grind
      exact Or.inl ⟨_, isInvolutionTransversal_sdiff_pair hmaps hinvol ha hT, by
        rw [herase]; exact Finset.insert_erase haT⟩
    · have hfaT : f a ∈ T := hT.map_mem_of_notMem ha haT
      have herase : T \ {a, f a} = T.erase (f a) := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        grind
      exact Or.inr ⟨_, isInvolutionTransversal_sdiff_pair hmaps hinvol ha hT, by
        rw [herase]; exact Finset.insert_erase hfaT⟩
  · rintro (⟨T', hT', rfl⟩ | ⟨T', hT', rfl⟩)
    · exact isInvolutionTransversal_insert_of_sdiff_pair hinvol hfree ha rfl hT'
    · exact isInvolutionTransversal_insert_of_sdiff_pair hinvol hfree (hmaps a ha)
        (by rw [hinvol a ha, Finset.pair_comm]) hT'

/-- Removing one orbit `{a, f a}` of a fixed-point-free involution halves the number of
transversals: each transversal of the rest extends in exactly two ways. -/
private lemma ncard_setOf_isInvolutionTransversal_eq_two_mul [DecidableEq α]
    (hmaps : ∀ x ∈ S, f x ∈ S)
    (hinvol : ∀ x ∈ S, f (f x) = x) (hfree : ∀ x ∈ S, f x ≠ x) {a : α} (ha : a ∈ S) :
    {T : Finset α | IsInvolutionTransversal f S T}.ncard =
      2 * {T : Finset α | IsInvolutionTransversal f (S \ {a, f a}) T}.ncard := by
  have haS' : a ∉ S \ {a, f a} := by simp
  have hfaS' : f a ∉ S \ {a, f a} := by simp
  have hinsert : ∀ c ∉ S \ {a, f a},
      Set.InjOn (insert c) {T : Finset α | IsInvolutionTransversal f (S \ {a, f a}) T} := by
    intro c hc T₁ h₁ T₂ h₂ h
    rw [← Finset.erase_insert (fun h' => hc (h₁.subset h')),
      ← Finset.erase_insert (fun h' => hc (h₂.subset h')), h]
  have hdisj : Disjoint
      (insert a '' {T : Finset α | IsInvolutionTransversal f (S \ {a, f a}) T})
      (insert (f a) '' {T : Finset α | IsInvolutionTransversal f (S \ {a, f a}) T}) := by
    rw [Set.disjoint_left]
    rintro U ⟨T₁, _, rfl⟩ ⟨T₂, h₂, h⟩
    have hmem : a ∈ insert (f a) T₂ := h ▸ Finset.mem_insert_self a T₁
    rcases Finset.mem_insert.1 hmem with h' | h'
    · exact hfree a ha h'.symm
    · exact haS' (h₂.subset h')
  have hfin := finite_setOf_isInvolutionTransversal f (S \ {a, f a})
  rw [setOf_isInvolutionTransversal_eq_image_union hmaps hinvol hfree ha,
    Set.ncard_union_eq hdisj (hfin.image _) (hfin.image _),
    (hinsert a haS').ncard_image, (hinsert (f a) hfaS').ncard_image, two_mul]

/-- **The transversal count.** A fixed-point-free involution of a finite set `S` has exactly
`2 ^ (#S / 2)` transversals: one binary choice per orbit. -/
theorem ncard_setOf_isInvolutionTransversal (hmaps : ∀ a ∈ S, f a ∈ S)
    (hinvol : ∀ a ∈ S, f (f a) = a) (hfree : ∀ a ∈ S, f a ≠ a) :
    {T : Finset α | IsInvolutionTransversal f S T}.ncard = 2 ^ (S.card / 2) := by
  classical
  revert hmaps hinvol hfree
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hmaps hinvol hfree
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · have hsingle : {T : Finset α | IsInvolutionTransversal f ∅ T} = {∅} :=
        Set.eq_singleton_iff_unique_mem.2
          ⟨⟨Finset.Subset.refl _, fun a ha => absurd ha (by simp)⟩,
            fun T hT => Finset.subset_empty.1 hT.subset⟩
      simp [hsingle]
    -- Induction step: remove the orbit `{a, f a}` of a chosen element, which doubles the count
    -- while `#S` drops by `2`.
    have hab : f a ≠ a := hfree a ha
    have hpair : ({a, f a} : Finset α) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ha
      · exact Finset.mem_singleton.1 hx ▸ hmaps a ha
    have hpaircard : ({a, f a} : Finset α).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hab.symm), Finset.card_singleton]
    have hcard : S.card = (S \ {a, f a}).card + 2 := by
      have h2 : 2 ≤ S.card := hpaircard ▸ Finset.card_le_card hpair
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 hpair, hpaircard]
      omega
    have hssub : S \ {a, f a} ⊂ S := ⟨Finset.sdiff_subset, fun h => by simpa using h ha⟩
    rw [ncard_setOf_isInvolutionTransversal_eq_two_mul hmaps hinvol hfree ha,
      ih _ hssub (fun x hx => map_mem_sdiff_pair hmaps hinvol ha hx)
        (fun x hx => hinvol x (Finset.sdiff_subset hx))
        (fun x hx => hfree x (Finset.sdiff_subset hx)), hcard]
    have hhalf : ((S \ {a, f a}).card + 2) / 2 = (S \ {a, f a}).card / 2 + 1 := by omega
    rw [hhalf, pow_succ]
    omega

end TauCeti
