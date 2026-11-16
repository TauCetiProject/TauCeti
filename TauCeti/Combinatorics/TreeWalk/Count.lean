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

Every `ClosedTreeWalk m` is its own canonical walk and admits `(Nat.card α).descFactorial (m + 1)`
realizations on `α`, yielding `catalan m * (Nat.card α).descFactorial (m + 1)` closed tree paths
(`closedTreePathEquiv`) and, for `m ≠ 0`, equally many leading cyclic words
(`leadingCyclicWordEquivClosedTreePath`).

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open Finset

namespace TauCeti.TreeWalk

variable {α : Type*} [DecidableEq α] {m : ℕ}

/-- A closed tree walk in first-visit labeling is the padded `canonicalWalk` of its restriction to
`Fin (2 * m + 1)`. -/
@[simp] theorem canonicalWalk_closedTreeWalk (u : ClosedTreeWalk m) :
    canonicalWalk (fun i : Fin (2 * m + 1) ↦ u.1 i) = u.1 := by
  let v : Fin (2 * m + 1) → ℕ := fun i ↦ u.1 i
  funext i
  rcases le_or_gt i (2 * m) with hi | hi
  · set x := u.1 i; have hxle := u.2.1.le_self i hi; have hux := u.2.1.idem hi
    set r := canonicalWalk v x; have hrle := canonicalWalk_le v x
    have hvr : v ⟨r, by omega⟩ = v ⟨x, by omega⟩ :=
      (canonicalWalk_eq_iff v ⟨r, by omega⟩ ⟨x, by omega⟩).mp (canonicalWalk_idem v x)
    have hrx : r = x := le_antisymm hrle (by
      have := u.2.1.le_self r (hrle.trans (hxle.trans hi))
      have : u.1 r = x := hvr.trans hux; omega)
    exact ((canonicalWalk_eq_iff v ⟨i, by omega⟩ ⟨x, by omega⟩).mpr hux.symm).trans hrx
  · exact (canonicalWalk_eq_zero v hi).trans (u.2.2 i hi).symm

/-- Restricting a `ClosedTreeWalk m` to `Fin (2 * m + 1)` visits `m + 1` distinct vertices. -/
@[simp] theorem card_image_closedTreeWalk (u : ClosedTreeWalk m) :
    #(univ.image (fun i : Fin (2 * m + 1) ↦ u.1 i)) = m + 1 := by
  rw [← card_fixed_canonicalWalk (fun i : Fin (2 * m + 1) ↦ u.1 i), canonicalWalk_closedTreeWalk]
  exact u.2.1.card_vertices

/-- Every `ClosedTreeWalk m` has `(Nat.card α).descFactorial (m + 1)` realizations on `α`. -/
theorem card_canonicalWalk_closedTreeWalk [Finite α] (u : ClosedTreeWalk m) :
    Nat.card {v : Fin (2 * m + 1) → α // canonicalWalk v = u.1} =
      (Nat.card α).descFactorial (m + 1) := by
  have h := card_canonicalWalk_eq (α := α) (fun i : Fin (2 * m + 1) ↦ u.1 i)
  rwa [canonicalWalk_closedTreeWalk, card_image_closedTreeWalk] at h

private theorem isClosedTreePath_of_canonicalWalk_eq {v : Fin (2 * m + 1) → α}
    {u : ClosedTreeWalk m} (hu : canonicalWalk v = u.1) : IsClosedTreePath m v := by
  refine ⟨(canonicalWalk_eq_iff v (Fin.last (2 * m)) 0).mp (by
      simp only [hu, Fin.val_last, Fin.val_zero]; exact u.2.1.closed.trans u.2.1.root.symm),
    by rw [← card_fixed_canonicalWalk v, hu]; exact u.2.1.card_vertices, fun i ↦ ?_⟩
  have hedge (a b : Fin (2 * m)) :
      s(v a.castSucc, v a.succ) = s(v b.castSucc, v b.succ) ↔
        s(u.1 a, u.1 (a + 1)) = s(u.1 b, u.1 (b + 1)) := by
    simp only [Sym2.eq_iff, ← canonicalWalk_eq_iff v, hu, Fin.val_castSucc, Fin.val_succ]
  exact (card_bij (fun j _ ↦ j.val)
    (fun j hj ↦ mem_filter.mpr ⟨mem_range.mpr j.isLt, (hedge j i).mp (mem_filter.mp hj).2⟩)
    (fun _ _ _ _ h ↦ Fin.ext h) fun j hj ↦ let ⟨hjr, hje⟩ := mem_filter.mp hj
      ⟨⟨j, mem_range.mp hjr⟩, mem_filter.mpr ⟨mem_univ _, (hedge ⟨j, _⟩ i).mpr hje⟩, rfl⟩).trans
    (u.2.1.card_edge i.val i.isLt)

/-- Grouping closed tree paths of length `2 * m` by their first-visit `ClosedTreeWalk m`. -/
def closedTreePathEquiv (m : ℕ) :
    {v : Fin (2 * m + 1) → α // IsClosedTreePath m v} ≃
      (u : ClosedTreeWalk m) × {v : Fin (2 * m + 1) → α // canonicalWalk v = u.1} where
  toFun v := ⟨⟨canonicalWalk v.1, isTreeWalk_canonicalWalk v.1 v.2.1 v.2.2.1 v.2.2.2,
    fun _ hi ↦ canonicalWalk_eq_zero v.1 hi⟩, ⟨v.1, rfl⟩⟩
  invFun p := ⟨p.2.1, isClosedTreePath_of_canonicalWalk_eq p.2.2⟩
  left_inv _ := rfl
  right_inv := fun ⟨_, _, hv⟩ ↦ by ext <;> simp [hv]

/-- The first component of `closedTreePathEquiv` has underlying map `canonicalWalk v.1`. -/
@[simp] theorem closedTreePathEquiv_apply_fst_coe
    (v : {v : Fin (2 * m + 1) → α // IsClosedTreePath m v}) :
    ((closedTreePathEquiv m v).1 : ℕ → ℕ) = canonicalWalk v.1 := (rfl)

/-- The second component of `closedTreePathEquiv` is the path `v` itself. -/
@[simp] theorem closedTreePathEquiv_apply_snd_coe
    (v : {v : Fin (2 * m + 1) → α // IsClosedTreePath m v}) :
    ((closedTreePathEquiv m v).2 : Fin (2 * m + 1) → α) = v.1 := (rfl)

/-- Evaluating `(closedTreePathEquiv m).symm` returns the underlying realization in `α`. -/
@[simp] theorem closedTreePathEquiv_symm_apply_coe
    (p : (u : ClosedTreeWalk m) × {v : Fin (2 * m + 1) → α // canonicalWalk v = u.1}) :
    ((closedTreePathEquiv (α := α) m).symm p : Fin (2 * m + 1) → α) = p.2.1 := (rfl)

/-- On a finite vertex set `α`, there are `catalan m * (Nat.card α).descFactorial (m + 1)` closed
double-traversal tree paths of length `2 * m`. -/
theorem card_closedTreePath [Finite α] (m : ℕ) :
    Nat.card {v : Fin (2 * m + 1) → α // IsClosedTreePath m v} =
      catalan m * (Nat.card α).descFactorial (m + 1) := by
  classical
  let _ := Fintype.ofFinite α
  rw [Nat.card_congr (closedTreePathEquiv (α := α) m), Nat.card_sigma]
  simp only [card_canonicalWalk_closedTreeWalk, sum_const, card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, card_closedTreeWalk]

/-- For `m ≠ 0`, `cyclicPath` gives an equivalence between leading cyclic trace words and closed
double-traversal tree paths of length `2 * m`. -/
def leadingCyclicWordEquivClosedTreePath [NeZero m] :
    {w : Fin (2 * m) → α // IsLeadingCyclicWord m w} ≃
    {v : Fin (2 * m + 1) → α // IsClosedTreePath m v} where
  toFun w := ⟨cyclicPath w.1, by simp, by simpa using w.2.2,
    card_edge_fiber_cyclicPath w.1 w.2.1 w.2.2⟩
  invFun v := by
    let w : Fin (2 * m) → α := fun i ↦ v.1 i.castSucc
    have hcw : cyclicPath w = v.1 := cyclicPath_restrict_eq v.2.1
    refine ⟨w, fun t ↦ ?_, by rw [← image_cyclicPath w, hcw]; exact v.2.2.1⟩
    have he (j : Fin (2 * m)) : s(w j, w (finRotate (2 * m) j)) = s(v.1 j.castSucc, v.1 j.succ) :=
      by rw [← cyclicPath_castSucc w j, ← cyclicPath_succ w j, hcw]
    have hcard : 1 < #{j : Fin (2 * m) |
        s(w j, w (finRotate (2 * m) j)) = s(w t, w (finRotate (2 * m) t))} := by
      simp only [he, v.2.2.2 t]; omega
    obtain ⟨s, hs, hst⟩ := exists_mem_ne hcard t
    exact ⟨s, hst, (mem_filter.mp hs).2⟩
  left_inv w := Subtype.ext (funext fun i ↦ cyclicPath_castSucc w.1 i)
  right_inv v := Subtype.ext (cyclicPath_restrict_eq v.2.1)

/-- Applying `leadingCyclicWordEquivClosedTreePath` extends a cyclic word by `cyclicPath`. -/
@[simp] theorem leadingCyclicWordEquivClosedTreePath_apply_coe [NeZero m]
    (w : {w : Fin (2 * m) → α // IsLeadingCyclicWord m w}) :
    (leadingCyclicWordEquivClosedTreePath w : Fin (2 * m + 1) → α) = cyclicPath w.1 := (rfl)

/-- Applying `leadingCyclicWordEquivClosedTreePath.symm` restricts a closed path via `castSucc`. -/
@[simp] theorem leadingCyclicWordEquivClosedTreePath_symm_apply_coe [NeZero m]
    (v : {v : Fin (2 * m + 1) → α // IsClosedTreePath m v}) :
    ((leadingCyclicWordEquivClosedTreePath (α := α) (m := m)).symm v : Fin (2 * m) → α) =
      fun i ↦ v.1 i.castSucc := (rfl)

/-- For `m ≠ 0`, there are `catalan m * (Nat.card α).descFactorial (m + 1)` leading cyclic words
of length `2 * m` on a finite vertex type `α`. -/
theorem card_leadingCyclicWord [Finite α] [NeZero m] :
    Nat.card {w : Fin (2 * m) → α // IsLeadingCyclicWord m w} =
      catalan m * (Nat.card α).descFactorial (m + 1) := by
  rw [Nat.card_congr leadingCyclicWordEquivClosedTreePath, card_closedTreePath]

/-- Finset cardinality form of `card_leadingCyclicWord`. -/
theorem card_filter_leadingCyclicWord [Fintype α] [NeZero m] :
    #({w : Fin (2 * m) → α | IsLeadingCyclicWord m w}) =
      catalan m * (Fintype.card α).descFactorial (m + 1) := by
  have h := card_leadingCyclicWord (α := α) (m := m)
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype] at h

end TauCeti.TreeWalk
