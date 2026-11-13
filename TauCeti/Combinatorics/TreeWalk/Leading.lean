/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Basic
public import TauCeti.Combinatorics.TreeWalk.Canonical
public import TauCeti.Combinatorics.TraceWord.Counting

/-!
# Leading trace words as canonical tree walks

A cyclic word of length `2 * m` with no singleton unordered edge and `m + 1` vertices is a
leading word in the Wigner moment expansion. Labeling each vertex by its first visit turns it
into a closed tree walk. The existing equivalence with Dyck words therefore applies to these
words, not just to walks already supplied in canonical labels.

`canonicalWalk` extends the first-visit canonical labeling of a finite path by zero after its
endpoint. Equality of vertices, and hence equality of unordered edges, is preserved and reflected.
`isTreeWalk_canonicalWalk_cyclic` applies the vertex and edge counting estimates to identify
canonicalized leading cyclic words as tree walks.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open Finset

namespace TauCeti.TreeWalk

variable {α : Type*} [DecidableEq α] {m : ℕ}

/-- A closed path with `m + 1` vertices and each unordered edge traversed twice becomes a tree
walk after first-visit relabeling. No order on the original vertex type is needed. -/
theorem isTreeWalk_canonicalWalk (w : Fin (2 * m + 1) → α)
    (hclosed : w (Fin.last (2 * m)) = w 0)
    (hv : #(univ.image w) = m + 1)
    (he : ∀ i : Fin (2 * m),
      #{j : Fin (2 * m) | s(w j.castSucc, w j.succ) = s(w i.castSucc, w i.succ)} = 2) :
    IsTreeWalk m (canonicalWalk w) where
  root := canonicalWalk_zero w
  closed := by
    rw [← canonicalWalk_zero w]
    exact (canonicalWalk_eq_iff w (Fin.last _) 0).2 hclosed
  le_self i _ := canonicalWalk_le w i
  card_vertices := (card_fixed_canonicalWalk w).trans hv
  card_edge i hi := by
    have hedge (a b : Fin (2 * m)) :
        s(canonicalWalk w a.castSucc, canonicalWalk w a.succ) =
          s(canonicalWalk w b.castSucc, canonicalWalk w b.succ) ↔
        s(w a.castSucc, w a.succ) = s(w b.castSucc, w b.succ) := by
      simp only [Sym2.eq_iff, canonicalWalk_eq_iff]
    refine Eq.trans ?_ (he ⟨i, hi⟩)
    apply card_bij (fun j hj => (⟨j, mem_range.mp (mem_filter.mp hj).1⟩ : Fin (2 * m)))
    · intro j hj
      simp only [mem_filter, mem_univ, true_and]
      apply (hedge _ ⟨i, hi⟩).mp
      simpa only [Fin.val_castSucc, Fin.val_succ] using (mem_filter.mp hj).2
    · intro j hj k hk h
      exact Fin.mk.inj h
    · intro j hj
      refine ⟨j.val, mem_filter.mpr ⟨mem_range.mpr j.isLt, ?_⟩, rfl⟩
      have hh := (hedge j ⟨i, hi⟩).mpr (mem_filter.mp hj).2
      simpa only [Fin.val_castSucc, Fin.val_succ] using hh

/-- A leading cyclic trace word becomes a tree walk under first-visit labeling. The endpoint
is added by cycling back to the initial vertex. The no-singleton condition alone, together with
the maximal vertex count, forces the required double traversal of every edge. The cyclic word
has positive length; the path theorem also covers the zero-step walk. -/
theorem isTreeWalk_canonicalWalk_cyclic [NeZero m] (w : Fin (2 * m) → α)
    (h : ∀ i, ∃ j ≠ i, s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) :
    IsTreeWalk m (canonicalWalk (fun i : Fin (2 * m + 1) =>
      w (Fin.ofNat (2 * m) i.val))) := by
  let v : Fin (2 * m + 1) → α := fun i => w (Fin.ofNat (2 * m) i.val)
  have hcast (i : Fin (2 * m)) : v i.castSucc = w i := by simp [v]
  have hsucc (i : Fin (2 * m)) : v i.succ = w (finRotate (2 * m) i) := by
    apply congrArg w
    rw [finRotate_apply]
    apply Fin.ext
    simp [Fin.val_add, Fin.ofNat_eq_cast, Nat.add_mod]
  have himage : univ.image v = univ.image w := by
    ext x
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, hcast i⟩
  apply isTreeWalk_canonicalWalk v
  · simp [v]
  · rw [himage, hv]
  · have he := ne_and_card_edge_fiber_eq_two_of_no_singleton_edge_of_card_image_eq w h hv
    intro i
    simpa only [hcast, hsucc] using he.2 i

end TauCeti.TreeWalk
