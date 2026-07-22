/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join
public import TauCeti.AlgebraicTopology.SimplicialComplex.LinkStar

/-!
# Links in joins of simplicial complexes

This file computes the link of a face in a join.  If `s` and `t` are (possibly empty) faces of
pre-abstract simplicial complexes `K` and `L`, then

`link (join K L) (s.disjSum t) = join (link K s) (link L t)`.

The empty-face convention needs care because a `PreAbstractSimplicialComplex` contains only
nonempty faces: the hypotheses therefore say explicitly that each component is either empty or a
face.  The one-sided formulas, where the chosen face lies entirely in one factor, are derived as
corollaries.

This is the interaction between links and joins required by the combinatorial-manifold part of
the geometric-topology roadmap.  In particular, it lets recursive sphere and ball constructions
compute their vertex links componentwise.  The result follows the standard join and link formulas
in Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapters 2--3.

## Main results

* `PreAbstractSimplicialComplex.link_join`: the link of a two-component face in a join.
* `PreAbstractSimplicialComplex.link_join_map_inl`: the link of a face from the left factor.
* `PreAbstractSimplicialComplex.link_join_map_inr`: the link of a face from the right factor.
-/

public section

namespace TauCeti

open Finset Function Sum

namespace PreAbstractSimplicialComplex

variable {α β : Type*}
variable {s : Finset α} {t : Finset β}

/-- A face of a join is disjoint from a disjoint-union face exactly when its two projections are
disjoint from the corresponding components. -/
private theorem disjoint_disjSum_iff {u : Finset (α ⊕ β)} :
    Disjoint u (s.disjSum t) ↔ Disjoint u.toLeft s ∧ Disjoint u.toRight t := by
  constructor
  · intro h
    constructor
    · refine Finset.disjoint_left.mpr fun {a} ha hs => ?_
      exact Finset.disjoint_left.mp h (by simpa using ha) (by simpa using hs)
    · refine Finset.disjoint_left.mpr fun {b} hb ht => ?_
      exact Finset.disjoint_left.mp h (by simpa using hb) (by simpa using ht)
  · rintro ⟨hl, hr⟩
    refine Finset.disjoint_left.mpr fun {x} hu hst => ?_
    cases x with
    | inl a => exact Finset.disjoint_left.mp hl (by simpa using hu) (by simpa using hst)
    | inr b => exact Finset.disjoint_left.mp hr (by simpa using hu) (by simpa using hst)

variable [DecidableEq α] [DecidableEq β]
variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}

/-- Union with a disjoint-union face is computed componentwise under the left and right
projections. -/
private theorem toLeft_union_disjSum (u : Finset (α ⊕ β)) :
    (u ∪ s.disjSum t).toLeft = u.toLeft ∪ s := by
  rw [toLeft_union, toLeft_disjSum]

/-- Union with a disjoint-union face is computed componentwise under the right projection. -/
private theorem toRight_union_disjSum (u : Finset (α ⊕ β)) :
    (u ∪ s.disjSum t).toRight = u.toRight ∪ t := by
  rw [toRight_union, toRight_disjSum]

/-- The link of a face in a join is the join of its component links.  Since pre-abstract
simplicial complexes omit the empty face, each component of the chosen face is allowed either to
be empty or to be a face of its factor. -/
theorem link_join (hs : s = ∅ ∨ s ∈ K) (ht : t = ∅ ∨ t ∈ L) :
    link (join K L) (s.disjSum t) = join (link K s) (link L t) := by
  apply SetLike.ext
  intro u
  change u ∈ link (join K L) (s.disjSum t) ↔ u ∈ join (link K s) (link L t)
  constructor
  · intro hu
    obtain ⟨hu, hdis, hunion⟩ := mem_link.mp hu
    obtain ⟨huls, hurt⟩ := disjoint_disjSum_iff.mp hdis
    have hjoin := mem_join_iff.mp hunion
    rw [toLeft_union_disjSum, toRight_union_disjSum] at hjoin
    obtain ⟨_, hleft, hright⟩ := hjoin
    refine mem_join_iff.mpr ⟨hu, ?_, ?_⟩
    · by_cases h : u.toLeft = ∅
      · exact Or.inl h
      · rcases hleft with hleft | hleft
        · exact (h (Finset.union_eq_empty.mp hleft).1).elim
        · exact Or.inr <| mem_link.mpr ⟨Finset.nonempty_iff_ne_empty.mpr h, huls, hleft⟩
    · by_cases h : u.toRight = ∅
      · exact Or.inl h
      · rcases hright with hright | hright
        · exact (h (Finset.union_eq_empty.mp hright).1).elim
        · exact Or.inr <| mem_link.mpr ⟨Finset.nonempty_iff_ne_empty.mpr h, hurt, hright⟩
  · intro hu
    obtain ⟨hu, hleft, hright⟩ := mem_join_iff.mp hu
    refine mem_link.mpr ⟨hu, disjoint_disjSum_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (hleft.elim (fun h => h ▸ disjoint_empty_left s) fun h => (mem_link.mp h).2.1)
    · exact (hright.elim (fun h => h ▸ disjoint_empty_left t) fun h => (mem_link.mp h).2.1)
    · apply mem_join_iff.mpr
      rw [toLeft_union_disjSum, toRight_union_disjSum]
      refine ⟨(hu.mono subset_union_left), ?_, ?_⟩
      · rcases hleft with hleft | hleft
        · rcases hs with rfl | hs
          · exact Or.inl (by simpa using hleft)
          · exact Or.inr (by simpa [hleft] using hs)
        · exact Or.inr (mem_link.mp hleft).2.2
      · rcases hright with hright | hright
        · rcases ht with rfl | ht
          · exact Or.inl (by simpa using hright)
          · exact Or.inr (by simpa [hright] using ht)
        · exact Or.inr (mem_link.mp hright).2.2

/-- The link of a face lying in the left factor of a join is its link in that factor joined with
the entire right factor. -/
theorem link_join_map_inl (hs : s ∈ K) :
    link (join K L) (s.map (Embedding.inl : α ↪ α ⊕ β)) = join (link K s) L := by
  rw [← disjSum_empty, link_join (Or.inr hs) (Or.inl rfl), link_empty]

/-- The link of a face lying in the right factor of a join is the entire left factor joined with
its link in the right factor. -/
theorem link_join_map_inr (ht : t ∈ L) :
    link (join K L) (t.map (Embedding.inr : β ↪ α ⊕ β)) = join K (link L t) := by
  rw [← empty_disjSum, link_join (Or.inl rfl) (Or.inr ht), link_empty]

end PreAbstractSimplicialComplex

end TauCeti
