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

variable {α : Type*} {m : ℕ}

/-- A cyclic word viewed as a path, with its initial vertex repeated at the endpoint. -/
def cyclicPath {k : ℕ} [NeZero k] (w : Fin k → α) : Fin (k + 1) → α :=
  fun i ↦ w (Fin.ofNat k i.val)

/-- Evaluate the path extension by reducing the index modulo the cyclic word's length. -/
theorem cyclicPath_apply {k : ℕ} [NeZero k] (w : Fin k → α) (i : Fin (k + 1)) :
    cyclicPath w i = w (Fin.ofNat k i.val) := (rfl)

@[simp] theorem cyclicPath_castSucc {k : ℕ} [NeZero k] (w : Fin k → α) (i : Fin k) :
    cyclicPath w i.castSucc = w i := by
  simp [cyclicPath]

@[simp] theorem cyclicPath_succ {k : ℕ} [NeZero k] (w : Fin k → α) (i : Fin k) :
    cyclicPath w i.succ = w (finRotate k i) := by
  apply congrArg w
  simp [finRotate_apply, Fin.ext_iff, Fin.val_add, Fin.ofNat_eq_cast, Nat.add_mod]

@[simp] theorem cyclicPath_zero {k : ℕ} [NeZero k] (w : Fin k → α) :
    cyclicPath w 0 = w 0 := by
  simp [cyclicPath]

@[simp] theorem cyclicPath_last {k : ℕ} [NeZero k] (w : Fin k → α) :
    cyclicPath w (Fin.last k) = w 0 := by
  simp [cyclicPath]

/-- Repeating the initial vertex at the endpoint preserves the set of visited vertices. -/
@[simp] theorem range_cyclicPath {k : ℕ} [NeZero k] (w : Fin k → α) :
    Set.range (cyclicPath w) = Set.range w := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.ofNat k i.val, (cyclicPath_apply w i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, cyclicPath_castSucc w i⟩

/-- Vertex relabeling commutes with extending a cyclic word to a path. -/
theorem comp_cyclicPath {β : Type*} {k : ℕ} [NeZero k] (f : α → β) (w : Fin k → α) :
    f ∘ cyclicPath w = cyclicPath (f ∘ w) := (rfl)

/-- The path extension determines the original cyclic word. -/
@[simp] theorem cyclicPath_inj {k : ℕ} [NeZero k] {w₁ w₂ : Fin k → α} :
    cyclicPath w₁ = cyclicPath w₂ ↔ w₁ = w₂ := by
  constructor
  · intro h
    funext i
    simpa only [cyclicPath_castSucc] using congrFun h i.castSucc
  · rintro rfl
    rfl

variable [DecidableEq α]

@[simp] theorem image_cyclicPath {k : ℕ} [NeZero k] (w : Fin k → α) :
    univ.image (cyclicPath w) = univ.image w := by
  ext x
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.ofNat k i.val, by simp [cyclicPath]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.castSucc, cyclicPath_castSucc w i⟩

/-- A leading cyclic word has two occurrences of every edge when viewed as a path. -/
theorem card_edge_fiber_cyclicPath [NeZero m] (w : Fin (2 * m) → α)
    (h : ∀ i, ∃ j ≠ i, s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i)))
    (hv : #(univ.image w) = m + 1) (i : Fin (2 * m)) :
    #{j : Fin (2 * m) |
      s(cyclicPath w j.castSucc, cyclicPath w j.succ) =
        s(cyclicPath w i.castSucc, cyclicPath w i.succ)} = 2 := by
  simpa only [cyclicPath_castSucc, cyclicPath_succ] using
    (ne_and_card_edge_fiber_eq_two_of_no_singleton_edge_of_card_image_eq w h hv).2 i

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
    IsTreeWalk m (canonicalWalk (cyclicPath w)) :=
  isTreeWalk_canonicalWalk (cyclicPath w) (by simp) (by simpa using hv)
    (card_edge_fiber_cyclicPath w h hv)

end TauCeti.TreeWalk
