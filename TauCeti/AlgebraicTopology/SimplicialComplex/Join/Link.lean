/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Star

/-!
# Links in joins

The link of a nonempty face in a join is the join of its links in the two factors. The face is
represented as a disjoint sum, so the formula keeps the two vertex types separate. This is the
combinatorial join calculation used when reducing links of higher-dimensional faces to the
vertex-link cases in the combinatorial-manifold construction.

The description follows Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter
2, and Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2 (1999),
299--320.
-/

public section

open Finset TauCeti

namespace PreAbstractSimplicialComplex

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
  {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}
  {s : Finset α} {t : Finset β}

/-- The link of a face in a join is the join of the links of its two projections. -/
theorem link_join (h : s.disjSum t ∈ join K L) :
    link (join K L) (s.disjSum t) = join (link K s) (link L t) := by
  obtain ⟨hne, hs, ht⟩ := disjSum_mem_join_iff.mp h
  refine SetLike.ext fun ρ => ?_
  constructor
  · intro hmem
    rcases mem_link.mp hmem with ⟨hρ, hdis, hρst⟩
    have hρparts := mem_join_iff.mp hρ
    have hρstparts := mem_join_iff.mp hρst
    apply mem_join_iff.mpr
    refine ⟨hρparts.1, ?_, ?_⟩
    · by_cases hleft : ρ.toLeft = ∅
      · exact Or.inl hleft
      · right
        have hleftUnion : ρ.toLeft ∪ s ∈ K := by
          rcases hρstparts.2.1 with hempty | hface
          · exfalso
            rw [Finset.toLeft_union, Finset.toLeft_disjSum] at hempty
            apply hleft
            apply Finset.eq_empty_of_forall_notMem
            intro a ha
            have ha' : a ∈ ρ.toLeft ∪ s := Finset.mem_union_left s ha
            exact (Finset.notMem_empty a) (hempty ▸ ha')
          · simpa only [Finset.toLeft_union, Finset.toLeft_disjSum] using hface
        have hdis' : Disjoint ρ.toLeft s := by
          refine Finset.disjoint_left.mpr ?_
          intro a haρ has
          have hnot : Sum.inl a ∉ s.disjSum t :=
            (Finset.disjoint_left.mp hdis) (Finset.mem_toLeft.mp haρ)
          exact hnot (Finset.mem_disjSum.mpr (Or.inl ⟨a, has, rfl⟩))
        exact mem_link.mpr ⟨hρparts.2.1.resolve_left hleft, hdis', hleftUnion⟩
    · by_cases hright : ρ.toRight = ∅
      · exact Or.inl hright
      · right
        have hrightUnion : ρ.toRight ∪ t ∈ L := by
          rcases hρstparts.2.2 with hempty | hface
          · exfalso
            rw [Finset.toRight_union, Finset.toRight_disjSum] at hempty
            apply hright
            apply Finset.eq_empty_of_forall_notMem
            intro b hb
            have hb' : b ∈ ρ.toRight ∪ t := Finset.mem_union_left t hb
            exact (Finset.notMem_empty b) (hempty ▸ hb')
          · simpa only [Finset.toRight_union, Finset.toRight_disjSum] using hface
        have hdis' : Disjoint ρ.toRight t := by
          refine Finset.disjoint_left.mpr ?_
          intro b hbρ hbt
          have hnot : Sum.inr b ∉ s.disjSum t :=
            (Finset.disjoint_left.mp hdis) (Finset.mem_toRight.mp hbρ)
          exact hnot (Finset.mem_disjSum.mpr (Or.inr ⟨b, hbt, rfl⟩))
        exact mem_link.mpr ⟨hρparts.2.2.resolve_left hright, hdis', hrightUnion⟩
  · intro hmem
    rcases mem_join_iff.mp hmem with ⟨hρne, hleft, hright⟩
    have hρ : ρ ∈ join K L := mem_join_iff.mpr ⟨hρne,
      hleft.imp_right fun h => (mem_link.mp h).1,
      hright.imp_right fun h => (mem_link.mp h).1⟩
    have hdis : Disjoint ρ (s.disjSum t) := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxρ
      rcases x with a | b
      · have haρ : a ∈ ρ.toLeft := (Finset.mem_toLeft (u := ρ)).mpr hxρ
        have hnot : a ∉ s := by
          rcases hleft with he | hl
          · simp [he] at haρ
          · exact (Finset.disjoint_left.mp (mem_link.mp hl).2.1) haρ
        intro hxa
        have has : a ∈ s := by
          rcases Finset.mem_disjSum.mp hxa with ⟨a', ha', haa'⟩ | ⟨b', hb', hab'⟩
          · cases haa'
            exact ha'
          · cases hab'
        exact hnot has
      · have hbρ : b ∈ ρ.toRight := (Finset.mem_toRight (u := ρ)).mpr hxρ
        have hnot : b ∉ t := by
          rcases hright with he | hr
          · simp [he] at hbρ
          · exact (Finset.disjoint_left.mp (mem_link.mp hr).2.1) hbρ
        intro hxb
        have hbt : b ∈ t := by
          rcases Finset.mem_disjSum.mp hxb with ⟨a', ha', haa'⟩ | ⟨b', hb', hbb'⟩
          · cases haa'
          · cases hbb'
            exact hb'
        exact hnot hbt
    have hρst : ρ ∪ s.disjSum t ∈ join K L := by
      apply mem_join_iff.mpr
      refine ⟨hρne.mono subset_union_left, ?_, ?_⟩
      · rw [Finset.toLeft_union, Finset.toLeft_disjSum]
        rcases hleft with he | hl
        · rcases hs with hs | hs
          · exact Or.inl (by rw [he, empty_union]; exact hs)
          · exact Or.inr (by rw [he, empty_union]; exact hs)
        · exact Or.inr (mem_link.mp hl).2.2
      · rw [Finset.toRight_union, Finset.toRight_disjSum]
        rcases hright with he | hr
        · rcases ht with ht | ht
          · exact Or.inl (by rw [he, empty_union]; exact ht)
          · exact Or.inr (by rw [he, empty_union]; exact ht)
        · exact Or.inr (mem_link.mp hr).2.2
    exact mem_link.mpr ⟨hρ, hdis, hρst⟩

end PreAbstractSimplicialComplex
