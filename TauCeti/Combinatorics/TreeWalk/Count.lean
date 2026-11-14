/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Leading
public import TauCeti.Combinatorics.TreeWalk.Relabeling

/-!
# Counting closed tree paths and leading trace words

A closed path of length `2 * m` on a vertex set `α` that visits `m + 1` distinct vertices and
traverses every unordered edge twice canonically relabels to a `ClosedTreeWalk m`. Conversely,
each of the `catalan m` closed tree walks in first-visit labeling is already its own canonical
walk on `{0, …, 2 * m}`, visits `m + 1` vertices, and therefore admits
`(Nat.card α).descFactorial (m + 1)` realizations in `α`.

For `m ≠ 0`, extending a cyclic word by repeating its initial vertex gives a bijection between
leading cyclic trace words of length `2 * m` (those without singleton unordered edges that visit
`m + 1` vertices) and closed double-traversal tree paths. Consequently, on a finite `n`-element
vertex set there are `catalan m * n.descFactorial (m + 1)` leading cyclic trace words of length
`2 * m`.

## Main definitions

* `TauCeti.TreeWalk.closedTreePathEquiv`: closed double-traversal tree paths of length `2 * m` are
  equivalent to pairs of a `ClosedTreeWalk m` and a realization with that canonical walk.
* `TauCeti.TreeWalk.leadingCyclicWordEquivClosedTreePath`: for `m ≠ 0`, leading cyclic words of
  length `2 * m` are equivalent via `cyclicPath` to closed double-traversal tree paths.

## Main results

* `TauCeti.TreeWalk.canonicalWalk_closedTreeWalk`: restricting a `ClosedTreeWalk m` to
  `Fin (2 * m + 1)` and taking its first-visit canonical walk recovers the original walk.
* `TauCeti.TreeWalk.card_closedTreePath`: there are `catalan m * (Nat.card α).descFactorial (m + 1)`
  closed double-traversal tree paths of length `2 * m` on a finite type `α`.
* `TauCeti.TreeWalk.card_leadingCyclicWord` and `TauCeti.TreeWalk.card_filter_leadingCyclicWord`:
  for `m ≠ 0`, there are `catalan m * n.descFactorial (m + 1)` leading cyclic words of length
  `2 * m` on an `n`-element type.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open Finset

namespace TauCeti.TreeWalk

variable {α : Type*} [DecidableEq α] {m : ℕ}

/-- A closed tree walk in first-visit labeling is already the padded `canonicalWalk` of its
restriction to `Fin (2 * m + 1)`. -/
@[simp] theorem canonicalWalk_closedTreeWalk (u : ClosedTreeWalk m) :
    canonicalWalk (fun i : Fin (2 * m + 1) ↦ u.1 i) = u.1 := by
  let v : Fin (2 * m + 1) → ℕ := fun i ↦ u.1 i
  funext i
  rcases le_or_gt i (2 * m) with hi | hi
  · have hi' : i < 2 * m + 1 := Nat.lt_succ_of_le hi
    set x := u.1 i
    have hxle : x ≤ i := u.2.1.le_self i hi
    have hx' : x < 2 * m + 1 := Nat.lt_succ_of_le (hxle.trans hi)
    have hux : u.1 x = x := u.2.1.idem hi
    set r := canonicalWalk v x
    have hrle : r ≤ x := canonicalWalk_le v x
    have hr' : r < 2 * m + 1 := Nat.lt_succ_of_le (hrle.trans (hxle.trans hi))
    have hvr : v ⟨r, hr'⟩ = v ⟨x, hx'⟩ :=
      (canonicalWalk_eq_iff v ⟨r, hr'⟩ ⟨x, hx'⟩).mp (canonicalWalk_idem v x)
    have hxr : x ≤ r := by
      have hur : u.1 r ≤ r := u.2.1.le_self r (hrle.trans (hxle.trans hi))
      have hvr' : u.1 r = x := hvr.trans hux
      omega
    have hrx : canonicalWalk v x = x := le_antisymm hrle hxr
    have hvi : canonicalWalk v i = canonicalWalk v x :=
      (canonicalWalk_eq_iff v ⟨i, hi'⟩ ⟨x, hx'⟩).mpr hux.symm
    exact hvi.trans hrx
  · exact (canonicalWalk_eq_zero v hi).trans (u.2.2 i hi).symm

/-- Restricting a `ClosedTreeWalk m` to `Fin (2 * m + 1)` visits exactly `m + 1` distinct
vertices. -/
@[simp] theorem card_image_closedTreeWalk (u : ClosedTreeWalk m) :
    #(univ.image (fun i : Fin (2 * m + 1) ↦ u.1 i)) = m + 1 := by
  rw [← card_fixed_canonicalWalk (fun i : Fin (2 * m + 1) ↦ u.1 i),
    canonicalWalk_closedTreeWalk]
  exact u.2.1.card_vertices

/-- Every `ClosedTreeWalk m` has `(Nat.card α).descFactorial (m + 1)` realizations on a finite
vertex type `α`. -/
theorem card_canonicalWalk_closedTreeWalk [Finite α] (u : ClosedTreeWalk m) :
    Nat.card {v : Fin (2 * m + 1) → α // canonicalWalk v = u.1} =
      (Nat.card α).descFactorial (m + 1) := by
  have h := card_canonicalWalk_eq (α := α) (fun i : Fin (2 * m + 1) ↦ u.1 i)
  rwa [canonicalWalk_closedTreeWalk, card_image_closedTreeWalk] at h

private theorem isClosedTreePath_of_canonicalWalk_eq {v : Fin (2 * m + 1) → α}
    {u : ClosedTreeWalk m} (hu : canonicalWalk v = u.1) :
    IsClosedTreePath m v := by
  refine ⟨?_, ?_, ?_⟩
  · apply (canonicalWalk_eq_iff v (Fin.last (2 * m)) 0).mp
    simp only [hu, Fin.val_last, Fin.val_zero]
    exact u.2.1.closed.trans u.2.1.root.symm
  · rw [← card_fixed_canonicalWalk v, hu]
    exact u.2.1.card_vertices
  · intro i
    have hedge (a b : Fin (2 * m)) :
        s(v a.castSucc, v a.succ) = s(v b.castSucc, v b.succ) ↔
          s(u.1 a, u.1 (a + 1)) = s(u.1 b, u.1 (b + 1)) := by
      simp only [Sym2.eq_iff, ← canonicalWalk_eq_iff v, hu, Fin.val_castSucc, Fin.val_succ]
    refine Eq.trans ?_ (u.2.1.card_edge i.val i.isLt)
    apply card_bij (fun j _ ↦ j.val)
    · intro j hj
      exact mem_filter.mpr ⟨mem_range.mpr j.isLt, (hedge j i).mp (mem_filter.mp hj).2⟩
    · intro j _ k _ h
      exact Fin.ext h
    · intro j hj
      obtain ⟨hjr, hje⟩ := mem_filter.mp hj
      refine ⟨⟨j, mem_range.mp hjr⟩, ?_, rfl⟩
      exact mem_filter.mpr ⟨mem_univ _, (hedge ⟨j, mem_range.mp hjr⟩ i).mpr hje⟩

/-- Grouping closed paths of length `2 * m` with `m + 1` vertices and double edge multiplicities
by their first-visit `ClosedTreeWalk m`. -/
def closedTreePathEquiv (m : ℕ) :
    {v : Fin (2 * m + 1) → α // IsClosedTreePath m v} ≃
      (u : ClosedTreeWalk m) × {v : Fin (2 * m + 1) → α // canonicalWalk v = u.1} where
  toFun v :=
    ⟨⟨canonicalWalk v.1, isTreeWalk_canonicalWalk v.1 v.2.1 v.2.2.1 v.2.2.2,
      fun _ hi ↦ canonicalWalk_eq_zero v.1 hi⟩, ⟨v.1, rfl⟩⟩
  invFun p := ⟨p.2.1, isClosedTreePath_of_canonicalWalk_eq p.2.2⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨u, v, hv⟩
    ext <;> simp [hv]

/-- The first component of `closedTreePathEquiv` has underlying map `canonicalWalk v.1`. -/
@[simp] theorem closedTreePathEquiv_apply_fst_coe
    (v : {v : Fin (2 * m + 1) → α // IsClosedTreePath m v}) :
    ((closedTreePathEquiv m v).1 : ℕ → ℕ) = canonicalWalk v.1 :=
  (rfl)

/-- The second component of `closedTreePathEquiv` is the path `v` itself. -/
@[simp] theorem closedTreePathEquiv_apply_snd_coe
    (v : {v : Fin (2 * m + 1) → α // IsClosedTreePath m v}) :
    ((closedTreePathEquiv m v).2 : Fin (2 * m + 1) → α) = v.1 :=
  (rfl)

/-- Evaluating `(closedTreePathEquiv m).symm` returns the underlying realization in `α`. -/
@[simp] theorem closedTreePathEquiv_symm_apply_coe
    (p : (u : ClosedTreeWalk m) × {v : Fin (2 * m + 1) → α // canonicalWalk v = u.1}) :
    ((closedTreePathEquiv (α := α) m).symm p : Fin (2 * m + 1) → α) = p.2.1 :=
  (rfl)

/-- On a finite vertex set `α`, there are `catalan m * (Nat.card α).descFactorial (m + 1)` closed
paths of length `2 * m` visiting `m + 1` vertices and traversing every unordered edge twice. -/
theorem card_closedTreePath [Finite α] (m : ℕ) :
    Nat.card {v : Fin (2 * m + 1) → α // IsClosedTreePath m v} =
      catalan m * (Nat.card α).descFactorial (m + 1) := by
  classical
  let := Fintype.ofFinite α
  rw [Nat.card_congr (closedTreePathEquiv (α := α) m), Nat.card_sigma]
  simp only [card_canonicalWalk_closedTreeWalk, sum_const, card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, card_closedTreeWalk]

/-- For `m ≠ 0`, `cyclicPath` gives an equivalence between leading cyclic trace words of length
`2 * m` and closed double-traversal tree paths of length `2 * m`. -/
def leadingCyclicWordEquivClosedTreePath [NeZero m] :
    {w : Fin (2 * m) → α // IsLeadingCyclicWord m w} ≃
    {v : Fin (2 * m + 1) → α // IsClosedTreePath m v} where
  toFun w := ⟨cyclicPath w.1, by simp, by simpa using w.2.2,
    card_edge_fiber_cyclicPath w.1 w.2.1 w.2.2⟩
  invFun v := by
    let w : Fin (2 * m) → α := fun i ↦ v.1 i.castSucc
    have hcw : cyclicPath w = v.1 := cyclicPath_restrict_eq v.2.1
    refine ⟨w, ⟨?_, ?_⟩⟩
    · intro t
      have he (j : Fin (2 * m)) :
          s(w j, w (finRotate (2 * m) j)) = s(v.1 j.castSucc, v.1 j.succ) := by
        rw [← cyclicPath_castSucc w j, ← cyclicPath_succ w j, hcw]
      have hcard : #{j : Fin (2 * m) |
          s(w j, w (finRotate (2 * m) j)) = s(w t, w (finRotate (2 * m) t))} = 2 := by
        simpa only [he] using v.2.2.2 t
      obtain ⟨s, hs, hst⟩ := exists_mem_ne (by omega : 1 < #{j : Fin (2 * m) |
        s(w j, w (finRotate (2 * m) j)) = s(w t, w (finRotate (2 * m) t))}) t
      exact ⟨s, hst, (mem_filter.mp hs).2⟩
    · rw [← image_cyclicPath w, hcw]
      exact v.2.2.1
  left_inv w := Subtype.ext (funext fun i ↦ cyclicPath_castSucc w.1 i)
  right_inv v := Subtype.ext (cyclicPath_restrict_eq v.2.1)

/-- Applying `leadingCyclicWordEquivClosedTreePath` extends a cyclic word by `cyclicPath`. -/
@[simp] theorem leadingCyclicWordEquivClosedTreePath_apply_coe [NeZero m]
    (w : {w : Fin (2 * m) → α // IsLeadingCyclicWord m w}) :
    (leadingCyclicWordEquivClosedTreePath w : Fin (2 * m + 1) → α) = cyclicPath w.1 :=
  (rfl)

/-- Applying `leadingCyclicWordEquivClosedTreePath.symm` restricts a closed path along
`Fin.castSucc`. -/
@[simp] theorem leadingCyclicWordEquivClosedTreePath_symm_apply_coe [NeZero m]
    (v : {v : Fin (2 * m + 1) → α // IsClosedTreePath m v}) :
    ((leadingCyclicWordEquivClosedTreePath (α := α) (m := m)).symm v : Fin (2 * m) → α) =
      fun i ↦ v.1 i.castSucc :=
  (rfl)

/-- For `m ≠ 0`, there are `catalan m * (Nat.card α).descFactorial (m + 1)` leading cyclic words
of length `2 * m` on a finite vertex type `α`. -/
theorem card_leadingCyclicWord [Finite α] [NeZero m] :
    Nat.card {w : Fin (2 * m) → α // IsLeadingCyclicWord m w} =
      catalan m * (Nat.card α).descFactorial (m + 1) := by
  rw [Nat.card_congr leadingCyclicWordEquivClosedTreePath, card_closedTreePath]

/-- Finset cardinality form of `card_leadingCyclicWord`: for `m ≠ 0`, there are
`catalan m * (Fintype.card α).descFactorial (m + 1)` singleton-free cyclic words of length `2 * m`
visiting `m + 1` vertices. -/
theorem card_filter_leadingCyclicWord [Fintype α] [NeZero m] :
    #({w : Fin (2 * m) → α | IsLeadingCyclicWord m w}) =
      catalan m * (Fintype.card α).descFactorial (m + 1) := by
  have h := card_leadingCyclicWord (α := α) (m := m)
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype] at h

end TauCeti.TreeWalk
