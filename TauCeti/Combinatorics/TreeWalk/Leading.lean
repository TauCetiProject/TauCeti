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

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {n m : ℕ}

/-- First-visit labels of a finite path, extended by zero after its endpoint. -/
def canonicalWalk (w : Fin (n + 1) → α) (i : ℕ) : ℕ :=
  ((List.ofFn w).firstVisitCanonical)[i]?.getD 0

/-- At a time within the path, the canonical label is the first occurrence index. -/
theorem canonicalWalk_apply (w : Fin (n + 1) → α) {i : ℕ} (hi : i < n + 1) :
    canonicalWalk w i = (List.ofFn w).idxOf (w ⟨i, hi⟩) := by
  rw [canonicalWalk, List.getElem?_eq_getElem (by
    rw [List.firstVisitCanonical_length, List.length_ofFn]
    exact hi), Option.getD_some,
    List.firstVisitCanonical_getElem _ (by simpa only [List.length_ofFn] using hi),
    List.getElem_ofFn]

/-- The canonical path is padded by zeros after its endpoint. -/
@[simp] theorem canonicalWalk_eq_zero (w : Fin (n + 1) → α) {i : ℕ} (hi : n < i) :
    canonicalWalk w i = 0 := by
  rw [canonicalWalk, List.getElem?_eq_none (by
    rw [List.firstVisitCanonical_length, List.length_ofFn]
    omega)]
  rfl

/-- Canonical labels preserve and reflect equality of vertices. -/
@[simp] theorem canonicalWalk_eq_iff (w : Fin (n + 1) → α) (i j : Fin (n + 1)) :
    canonicalWalk w i = canonicalWalk w j ↔ w i = w j := by
  rw [canonicalWalk_apply w i.isLt, canonicalWalk_apply w j.isLt]
  exact List.idxOf_inj (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- Injective relabeling leaves the padded canonical walk unchanged. -/
@[simp] theorem canonicalWalk_comp (w : Fin (n + 1) → α) (f : α → β)
    (hf : Set.InjOn f (Set.range w)) :
    canonicalWalk (f ∘ w) = canonicalWalk w := by
  funext i
  simp only [canonicalWalk, ← List.map_ofFn]
  rw [List.firstVisitCanonical_map _ f (by
    intro x y hx hy hxy
    exact hf (List.mem_ofFn.mp hx) (List.mem_ofFn.mp hy) hxy)]

/-- A first occurrence cannot be later than the time of the current visit. -/
theorem canonicalWalk_le (w : Fin (n + 1) → α) (i : ℕ) : canonicalWalk w i ≤ i := by
  by_cases hi : i < n + 1
  · rw [canonicalWalk_apply w hi]
    by_contra h
    have hnot := List.not_of_lt_findIdx (xs := List.ofFn w)
      (p := fun x => x == w ⟨i, hi⟩) (i := i) (by simpa [List.idxOf] using h)
    simp only [List.getElem_ofFn, beq_self_eq_true, Bool.true_eq_false] at hnot
  · rw [canonicalWalk_eq_zero w (by omega)]
    exact Nat.zero_le _

/-- The canonical walk starts at zero. -/
@[simp] theorem canonicalWalk_zero (w : Fin (n + 1) → α) : canonicalWalk w 0 = 0 :=
  Nat.eq_zero_of_le_zero (canonicalWalk_le w 0)

/-- First-visit labels are fixed points of the canonical walk. -/
@[simp] theorem canonicalWalk_idem (w : Fin (n + 1) → α) (i : ℕ) :
    canonicalWalk w (canonicalWalk w i) = canonicalWalk w i := by
  by_cases hi : i < n + 1
  · have hc : canonicalWalk w i < n + 1 := (canonicalWalk_le w i).trans_lt hi
    rw [canonicalWalk_apply w hc]
    have hget : w ⟨canonicalWalk w i, hc⟩ = w ⟨i, hi⟩ := by
      have := List.getElem_idxOf (xs := List.ofFn w) (x := w ⟨i, hi⟩)
        (by simpa only [List.length_ofFn, canonicalWalk_apply w hi] using hc)
      simpa only [canonicalWalk_apply w hi, List.getElem_ofFn] using this
    rw [hget, ← canonicalWalk_apply w hi]
  · have hz : canonicalWalk w i = 0 := canonicalWalk_eq_zero w (by omega)
    simp only [hz, canonicalWalk_zero]

/-- Fixed first-visit labels are in bijection with the distinct vertices of the original path. -/
theorem card_fixed_canonicalWalk (w : Fin (n + 1) → α) :
    #{i ∈ range (n + 1) | canonicalWalk w i = i} = #(univ.image w) := by
  let c : Fin (n + 1) → ℕ := fun i => canonicalWalk w i
  have hfix : {i ∈ range (n + 1) | canonicalWalk w i = i} = univ.image c := by
    ext i
    simp only [mem_filter, mem_range, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hi, h⟩
      exact ⟨⟨i, hi⟩, h⟩
    · rintro ⟨j, rfl⟩
      exact ⟨(canonicalWalk_le w j).trans_lt j.isLt, canonicalWalk_idem w j⟩
  rw [hfix]
  have himage : univ.image c = (univ.image w).image (fun x => (List.ofFn w).idxOf x) := by
    simp only [image_image]
    congr 1
    funext i
    exact canonicalWalk_apply w i.isLt
  rw [himage]
  apply card_image_of_injOn
  intro x hx y hy hxy
  obtain ⟨i, -, rfl⟩ := mem_image.mp hx
  exact (List.idxOf_inj (List.mem_ofFn.mpr ⟨i, rfl⟩)).1 hxy

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
