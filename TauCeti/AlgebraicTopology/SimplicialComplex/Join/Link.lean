/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.LinkStar

/-!
# Links in joins

The link in a join of a disjoint sum of componentwise faces (allowing empty components) is the
join of the component links. The face is represented as a disjoint sum, so the formula keeps the
two vertex types separate. This is the combinatorial join calculation used when reducing links of
higher-dimensional faces to the vertex-link cases in the combinatorial-manifold construction.

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

private theorem toLeft_mem_link_of_mem_join {ρ : Finset (α ⊕ β)}
    (hρ : ρ ∈ join K L) (hρst : ρ ∪ s.disjSum t ∈ join K L)
    (hdis : Disjoint ρ (s.disjSum t)) :
    ρ.toLeft = ∅ ∨ ρ.toLeft ∈ link K s := by
  have hρparts := mem_join_iff.mp hρ
  have hρstparts := mem_join_iff.mp hρst
  by_cases hleft : ρ.toLeft = ∅
  · exact Or.inl hleft
  · right
    have hleftUnion : ρ.toLeft ∪ s ∈ K := by
      have h := hρstparts.2.1
      rw [Finset.toLeft_union, Finset.toLeft_disjSum] at h
      exact h.resolve_left <| Finset.nonempty_iff_ne_empty.mp <|
        (Finset.nonempty_iff_ne_empty.mpr hleft).mono subset_union_left
    exact mem_link.mpr ⟨hρparts.2.1.resolve_left hleft,
      (Finset.disjoint_disjSum_iff.mp hdis).1, hleftUnion⟩

private theorem toRight_mem_link_of_mem_join {ρ : Finset (α ⊕ β)}
    (hρ : ρ ∈ join K L) (hρst : ρ ∪ s.disjSum t ∈ join K L)
    (hdis : Disjoint ρ (s.disjSum t)) :
    ρ.toRight = ∅ ∨ ρ.toRight ∈ link L t := by
  have hρparts := mem_join_iff.mp hρ
  have hρstparts := mem_join_iff.mp hρst
  by_cases hright : ρ.toRight = ∅
  · exact Or.inl hright
  · right
    have hrightUnion : ρ.toRight ∪ t ∈ L := by
      have h := hρstparts.2.2
      rw [Finset.toRight_union, Finset.toRight_disjSum] at h
      exact h.resolve_left <| Finset.nonempty_iff_ne_empty.mp <|
        (Finset.nonempty_iff_ne_empty.mpr hright).mono subset_union_left
    exact mem_link.mpr ⟨hρparts.2.2.resolve_left hright,
      (Finset.disjoint_disjSum_iff.mp hdis).2, hrightUnion⟩

private theorem toLeft_union_mem_of_mem_link {ρ : Finset (α ⊕ β)}
    (hleft : ρ.toLeft = ∅ ∨ ρ.toLeft ∈ link K s) (hs : s = ∅ ∨ s ∈ K) :
    (ρ ∪ s.disjSum t).toLeft = ∅ ∨ (ρ ∪ s.disjSum t).toLeft ∈ K := by
  rw [Finset.toLeft_union, Finset.toLeft_disjSum]
  rcases hleft with he | hl
  · rcases hs with hs | hs
    · exact Or.inl (by rw [he, empty_union]; exact hs)
    · exact Or.inr (by rw [he, empty_union]; exact hs)
  · exact Or.inr (mem_link.mp hl).2.2

private theorem toRight_union_mem_of_mem_link {ρ : Finset (α ⊕ β)}
    (hright : ρ.toRight = ∅ ∨ ρ.toRight ∈ link L t) (ht : t = ∅ ∨ t ∈ L) :
    (ρ ∪ s.disjSum t).toRight = ∅ ∨ (ρ ∪ s.disjSum t).toRight ∈ L := by
  rw [Finset.toRight_union, Finset.toRight_disjSum]
  rcases hright with he | hr
  · rcases ht with ht | ht
    · exact Or.inl (by rw [he, empty_union]; exact ht)
    · exact Or.inr (by rw [he, empty_union]; exact ht)
  · exact Or.inr (mem_link.mp hr).2.2

/-- The link of a disjoint sum of componentwise faces is the join of the links of its projections.

The left or right component face may be empty. -/
@[simp]
theorem link_join (hs : s = ∅ ∨ s ∈ K) (ht : t = ∅ ∨ t ∈ L) :
    link (join K L) (s.disjSum t) = join (link K s) (link L t) := by
  refine SetLike.ext fun ρ => ?_
  constructor
  · intro hmem
    rcases mem_link.mp hmem with ⟨hρ, hdis, hρst⟩
    apply mem_join_iff.mpr
    refine ⟨(mem_join_iff.mp hρ).1, ?_, ?_⟩
    · exact toLeft_mem_link_of_mem_join hρ hρst hdis
    · exact toRight_mem_link_of_mem_join hρ hρst hdis
  · intro hmem
    rcases mem_join_iff.mp hmem with ⟨hρne, hleft, hright⟩
    have hρ : ρ ∈ join K L := mem_join_iff.mpr ⟨hρne,
      hleft.imp_right fun h => (mem_link.mp h).1,
      hright.imp_right fun h => (mem_link.mp h).1⟩
    have hdis : Disjoint ρ (s.disjSum t) := Finset.disjoint_disjSum_iff.mpr ⟨
      hleft.elim (fun h => by simp [h]) (fun h => (mem_link.mp h).2.1),
      hright.elim (fun h => by simp [h]) (fun h => (mem_link.mp h).2.1)⟩
    have hρst : ρ ∪ s.disjSum t ∈ join K L := by
      apply mem_join_iff.mpr
      refine ⟨hρne.mono subset_union_left, ?_, ?_⟩
      · exact toLeft_union_mem_of_mem_link hleft hs
      · exact toRight_union_mem_of_mem_link hright ht
    exact mem_link.mpr ⟨hρ, hdis, hρst⟩

end PreAbstractSimplicialComplex
