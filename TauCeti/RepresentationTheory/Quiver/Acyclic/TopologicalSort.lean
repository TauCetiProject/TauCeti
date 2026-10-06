/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Preorder.Finite
public import TauCeti.RepresentationTheory.Quiver.Acyclic.Basic

/-!
# Topological sorting of an acyclic quiver

Every finite set of vertices of an acyclic quiver can be listed without repetition so that no
arrow runs from an earlier entry to a later one.

## Main results

* `TauCeti.Quiver.IsAcyclic.exists_pairwise_isEmpty_hom`: every finite set of vertices of an
  acyclic quiver has a topological ordering, along which no arrow runs forwards.

## Applications

This ordering is the input to the sink-admissible orderings of
`TauCeti.RepresentationTheory.Quiver.Reflection.Admissible`.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

variable {V : Type u} [_root_.Quiver.{v} V]

namespace Quiver

/-- A nonempty finite set of vertices of an acyclic quiver contains a vertex emitting no arrow
into the set: a maximal vertex for the reachability preorder cannot, since an arrow out of it
would have to be matched by a path back. -/
private theorem exists_isEmpty_hom_mem (h : IsAcyclic V) {s : Finset V} (hs : s.Nonempty) :
    ∃ i ∈ s, ∀ b ∈ s, IsEmpty (i ⟶ b) := by
  let : LE V := ⟨fun a b ↦ Nonempty (Path a b)⟩
  have : IsTrans V (· ≤ · : V → V → Prop) := ⟨fun a b c hab hbc ↦ by
    obtain ⟨p⟩ : Nonempty (Path a b) := hab
    obtain ⟨r⟩ : Nonempty (Path b c) := hbc
    exact ⟨p.comp r⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_maximal hs
  refine ⟨i, hi, fun b hb ↦ ⟨fun e ↦ ?_⟩⟩
  obtain ⟨p⟩ : Nonempty (Path b i) := hmax hb (⟨e.toPath⟩ : Nonempty (Path i b))
  obtain rfl : i = b := h.eq_of_paths e.toPath p
  exact (h.isEmpty_hom_self i).elim e

/-- **Topological sorting.** Every finite set of vertices of an acyclic quiver can be listed without
repetition so that no arrow runs from an earlier entry to a later one. -/
theorem IsAcyclic.exists_pairwise_isEmpty_hom (h : IsAcyclic V) (s : Finset V) :
    ∃ l : List V, l.Nodup ∧ (∀ v : V, v ∈ l ↔ v ∈ s) ∧
      l.Pairwise fun x y ↦ IsEmpty (x ⟶ y) := by
  classical
  -- Peel off a vertex emitting no arrow inside the set, and recurse on the rest.
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨[], List.nodup_nil, by simp, List.Pairwise.nil⟩
    · obtain ⟨i, his, hsink⟩ := exists_isEmpty_hom_mem h hs
      obtain ⟨t, htnd, htmem, htp⟩ := ih (s.erase i) (Finset.erase_ssubset his)
      have hit : i ∉ t := fun hc ↦ by simpa using (htmem i).mp hc
      refine ⟨i :: t, List.nodup_cons.mpr ⟨hit, htnd⟩, fun v ↦ ?_,
        List.pairwise_cons.mpr ⟨fun y hy ↦ hsink y (Finset.mem_of_mem_erase ((htmem y).mp hy)),
          htp⟩⟩
      rw [List.mem_cons, htmem v, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨-, hv⟩)
        · exact his
        · exact hv
      · intro hv
        by_cases hvi : v = i
        · exact Or.inl hvi
        · exact Or.inr ⟨hvi, hv⟩

end Quiver

end TauCeti
