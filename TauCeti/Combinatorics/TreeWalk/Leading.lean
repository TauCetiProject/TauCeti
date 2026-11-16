/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Basic
public import TauCeti.Combinatorics.TreeWalk.Canonical
public import TauCeti.Combinatorics.TreeWalk.Relabeling
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
canonicalized leading cyclic words as tree walks. Combining the Catalan count of closed tree walks
with the falling-factorial count of vertex relabelings then enumerates all leading closed paths and
leading cyclic trace words on a finite vertex set: there are
`(Fintype.card α).descFactorial (m + 1) * catalan m` of them
(`TauCeti.TreeWalk.card_filter_closed_and_card_image_eq_and_card_edge_eq_two` and
`TauCeti.TreeWalk.card_filter_no_singleton_edge_and_card_image_eq`).

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

/-! ### Catalan enumeration of leading walks -/

section Enumeration

/-- Restricting a closed tree walk to `Fin (2 * m + 1)` preserves its canonical walk. -/
private theorem canonicalWalk_restrict_closedTreeWalk (w : ClosedTreeWalk m) :
    canonicalWalk (fun i : Fin (2 * m + 1) ↦ w.1 i) = w.1 := by
  funext i
  by_cases hi : i < 2 * m + 1
  · rw [canonicalWalk_apply _ hi]
    set l := List.ofFn fun j : Fin (2 * m + 1) ↦ w.1 j
    have hlen : l.length = 2 * m + 1 := List.length_ofFn
    have hmem : w.1 i ∈ l := List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩
    have hidx_lt : l.idxOf (w.1 i) < l.length := List.idxOf_lt_length_of_mem hmem
    have hget_idx : l[l.idxOf (w.1 i)] = w.1 i := List.getElem_idxOf hidx_lt
    have hle_idx : w.1 i ≤ l.idxOf (w.1 i) := by
      have hk : l.idxOf (w.1 i) ≤ 2 * m := by omega
      have hwk := w.2.1.le_self (l.idxOf (w.1 i)) hk
      have hval : w.1 (l.idxOf (w.1 i)) = w.1 i := by
        simpa only [l, List.getElem_ofFn] using hget_idx
      omega
    have hwi_lt : w.1 i < 2 * m + 1 := (w.2.1.le_self i (by omega)).trans_lt hi
    have hget_wi : l[w.1 i]'(by omega) = w.1 i := by
      simp only [l, List.getElem_ofFn]
      exact w.2.1.idem (by omega)
    have hidx_le : l.idxOf (w.1 i) ≤ w.1 i := by
      by_contra hgt
      have hnot := List.not_of_lt_findIdx (xs := l) (p := (· == w.1 i)) (i := w.1 i)
        (by simpa [List.idxOf] using Nat.lt_of_not_ge hgt)
      simp [hget_wi] at hnot
    exact le_antisymm hidx_le hle_idx
  · rw [canonicalWalk_eq_zero _ (by omega), w.2.2 i (by omega)]

/-- The restriction of a closed tree walk to `Fin (2 * m + 1)` visits `m + 1` vertices. -/
private theorem card_image_restrict_closedTreeWalk (w : ClosedTreeWalk m) :
    #(univ.image fun i : Fin (2 * m + 1) ↦ w.1 i) = m + 1 := by
  rw [← card_fixed_canonicalWalk (fun i : Fin (2 * m + 1) ↦ w.1 i),
    canonicalWalk_restrict_closedTreeWalk]
  exact w.2.1.card_vertices

/-- A path on `α` is a closed double-traversal tree path if and only if its canonical walk lies in
`ClosedTreeWalk m`. -/
private theorem isTreeWalk_canonicalWalk_iff (v : Fin (2 * m + 1) → α) :
    (v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
      ∀ i : Fin (2 * m),
        #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2) ↔
      IsTreeWalk m (canonicalWalk v) := by
  constructor
  · rintro ⟨hclosed, hv, he⟩
    exact isTreeWalk_canonicalWalk v hclosed hv he
  · intro hw
    refine ⟨?_, ?_, ?_⟩
    · apply (canonicalWalk_eq_iff v (Fin.last (2 * m)) 0).mp
      simp [hw.closed, hw.root]
    · rw [← card_fixed_canonicalWalk v]
      exact hw.card_vertices
    · intro i
      have hedge (a b : Fin (2 * m)) :
          s(v a.castSucc, v a.succ) = s(v b.castSucc, v b.succ) ↔
            s(canonicalWalk v a.val, canonicalWalk v (a.val + 1)) =
              s(canonicalWalk v b.val, canonicalWalk v (b.val + 1)) := by
        simp only [Sym2.eq_iff, ← canonicalWalk_eq_iff v, Fin.val_castSucc, Fin.val_succ]
      refine Eq.trans ?_ (hw.card_edge i.val i.isLt)
      refine card_bij (fun j _ ↦ j.val) (fun j hj ↦ ?_) (fun _ _ _ _ h ↦ Fin.ext h) ?_
      · exact mem_filter.mpr ⟨mem_range.mpr j.isLt, (hedge j i).mp (mem_filter.mp hj).2⟩
      · intro j hj
        obtain ⟨hjr, hje⟩ := mem_filter.mp hj
        let j' : Fin (2 * m) := ⟨j, mem_range.mp hjr⟩
        exact ⟨j', mem_filter.mpr ⟨mem_univ _, (hedge j' i).mpr hje⟩, rfl⟩

/-- **Catalan enumeration of leading closed paths.** On a finite vertex type `α`, the closed paths
of length `2 * m` visiting `m + 1` vertices and traversing each unordered edge twice number
`(Fintype.card α).descFactorial (m + 1) * catalan m`. This holds for `m = 0` as well, where the
`Fintype.card α` zero-step paths each visit one vertex. -/
theorem card_filter_closed_and_card_image_eq_and_card_edge_eq_two [Fintype α] :
    #({v : Fin (2 * m + 1) → α |
        v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
          ∀ i : Fin (2 * m),
            #{j : Fin (2 * m) |
              s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2} : Finset _) =
      (Fintype.card α).descFactorial (m + 1) * catalan m := by
  classical
  let L : Finset (Fin (2 * m + 1) → α) :=
    {v | v (Fin.last (2 * m)) = v 0 ∧ #(univ.image v) = m + 1 ∧
      ∀ i : Fin (2 * m),
        #{j : Fin (2 * m) | s(v j.castSucc, v j.succ) = s(v i.castSucc, v i.succ)} = 2}
  let canon : ↥L → ClosedTreeWalk m := fun v ↦
    ⟨canonicalWalk v.1, (isTreeWalk_canonicalWalk_iff v.1).mp (mem_filter.mp v.2).2,
      fun i hi ↦ canonicalWalk_eq_zero v.1 hi⟩
  let : Fintype (ClosedTreeWalk m) := Fintype.ofEquiv _ (closedTreeWalkEquiv m).symm
  have hcardL : #L = Fintype.card ↥L := (Fintype.card_coe L).symm
  rw [hcardL, ← Fintype.card_congr (Equiv.sigmaFiberEquiv canon), Fintype.card_sigma]
  have hfiber (w : ClosedTreeWalk m) :
      Fintype.card {v : ↥L // canon v = w} =
        (Fintype.card α).descFactorial (m + 1) := by
    let ef : {v : ↥L // canon v = w} ≃
        {v : Fin (2 * m + 1) → α //
          canonicalWalk v = canonicalWalk (fun i : Fin (2 * m + 1) ↦ w.1 i)} :=
      { toFun := fun v ↦ ⟨v.1.1, (congrArg Subtype.val v.2).trans
          (canonicalWalk_restrict_closedTreeWalk w).symm⟩
        invFun := fun v ↦ ⟨⟨v.1, mem_filter.mpr ⟨mem_univ _,
          (isTreeWalk_canonicalWalk_iff v.1).mpr (by
            rw [v.2, canonicalWalk_restrict_closedTreeWalk]
            exact w.2.1)⟩⟩,
          Subtype.ext (v.2.trans (canonicalWalk_restrict_closedTreeWalk w))⟩
        left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
        right_inv := fun _ ↦ Subtype.ext rfl }
    rw [Fintype.card_congr ef, ← Nat.card_eq_fintype_card, card_canonicalWalk_eq,
      Nat.card_eq_fintype_card, card_image_restrict_closedTreeWalk]
  simp_rw [hfiber, sum_const, card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card (α := ClosedTreeWalk m), card_closedTreeWalk, mul_comm]

/-- **Catalan enumeration of leading cyclic trace words.** For `m ≠ 0`, there are
`(Fintype.card α).descFactorial (m + 1) * catalan m` cyclic words of length `2 * m` on `α` with no
singleton unordered edge and `m + 1` visited vertices. -/
theorem card_filter_no_singleton_edge_and_card_image_eq [Fintype α] (hm : m ≠ 0) :
    #({w : Fin (2 * m) → α |
        (∀ t, ∃ s ≠ t,
          s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1} : Finset _) =
      (Fintype.card α).descFactorial (m + 1) * catalan m := by
  have : NeZero m := ⟨hm⟩
  rw [← card_filter_closed_and_card_image_eq_and_card_edge_eq_two (α := α) (m := m)]
  refine card_bij (fun w _ ↦ cyclicPath w) (fun w hw ↦ ?_) (fun _ _ _ _ h ↦ cyclicPath_inj.mp h) ?_
  · obtain ⟨hno, hv⟩ := (mem_filter.mp hw).2
    refine mem_filter.mpr ⟨mem_univ _, ?_, ?_, card_edge_fiber_cyclicPath w hno hv⟩
    · simp
    · simpa using hv
  · intro v hv
    obtain ⟨hclosed, hvcard, hedge⟩ := (mem_filter.mp hv).2
    let w : Fin (2 * m) → α := fun i ↦ v i.castSucc
    have hvw : cyclicPath w = v := by
      funext j
      exact Fin.lastCases (motive := fun j ↦ cyclicPath w j = v j)
        (by simp [w, hclosed]) (fun i ↦ by simp [w]) j
    refine ⟨w, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, hvw⟩
    · intro t
      have hcard : #{s : Fin (2 * m) |
          s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))} = 2 := by
        have heq := hedge t
        rw [← hvw] at heq
        simpa only [cyclicPath_castSucc, cyclicPath_succ] using heq
      obtain ⟨a, b, hab, hpair⟩ := card_eq_two.mp hcard
      by_cases hta : t = a
      · refine ⟨b, hta ▸ hab.symm, ?_⟩
        have hb : b ∈ ({a, b} : Finset (Fin (2 * m))) := by simp
        rw [← hpair] at hb
        exact (mem_filter.mp hb).2
      · refine ⟨a, Ne.symm hta, ?_⟩
        have ha : a ∈ ({a, b} : Finset (Fin (2 * m))) := by simp
        rw [← hpair] at ha
        exact (mem_filter.mp ha).2
    · rw [← image_cyclicPath w, hvw, hvcard]

end Enumeration

end TauCeti.TreeWalk
