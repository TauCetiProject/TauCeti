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
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Leading trace words as canonical tree walks

A cyclic word of length `2 * m` with no singleton unordered edge and `m + 1` vertices is a
leading word in the Wigner moment expansion. Labeling each vertex by its first visit turns it
into a closed tree walk, and conversely every closed walk whose canonicalization is a tree walk
has this vertex and edge structure.

Combining the `catalan m` count of `ClosedTreeWalk m` with `card_canonicalWalk_eq` counts the
leading paths and, for `m ≠ 0`, the leading cyclic words on a finite vertex set `α` as
`catalan m * (Fintype.card α).descFactorial (m + 1)`. Moreover, every unordered edge of a leading
cyclic word is traversed once in each direction, so its `2 * m` directed steps are distinct and
any commutative-monoid product along the cyclic word factors over the `m` strictly increasing
steps on a linearly ordered vertex set.

## Main definitions

* `TauCeti.TreeWalk.leadingCyclicWordEquiv`: equivalence between leading cyclic words of positive
  length `2 * m` and closed paths of length `2 * m` whose canonicalization is a tree walk.

## Main results

* `TauCeti.TreeWalk.canonicalWalk_closedTreeWalk`: every closed tree walk is fixed by
  `canonicalWalk`.
* `TauCeti.TreeWalk.isTreeWalk_canonicalWalk_iff` and
  `TauCeti.TreeWalk.isTreeWalk_canonicalWalk_cyclic_iff`: necessary and sufficient characterizations
  of paths and cyclic words that canonicalize to tree walks.
* `TauCeti.TreeWalk.card_leading_cyclic_word` and
  `TauCeti.TreeWalk.card_filter_leading_cyclic_word`: leading cyclic words of positive length
  `2 * m` have cardinality `catalan m * (Fintype.card α).descFactorial (m + 1)`.
* `TauCeti.TreeWalk.prod_eq_prod_filter_lt_finRotate`: commutative-monoid products over the steps of
  a leading cyclic word factor over its `m` strictly increasing steps.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open Finset

namespace TauCeti.TreeWalk

section DecidableEq

variable {α : Type*} [DecidableEq α] {m : ℕ}

/-- Every closed tree walk is already in first-visit canonical form. -/
@[simp]
theorem canonicalWalk_closedTreeWalk (c : ClosedTreeWalk m) :
    canonicalWalk (fun i : Fin (2 * m + 1) ↦ c.1 i) = c.1 := by
  set p : Fin (2 * m + 1) → ℕ := fun i ↦ c.1 i
  funext i
  by_cases hi : i < 2 * m + 1
  · set j := c.1 i
    have hj : j < 2 * m + 1 := (c.2.1.le_self i (by omega)).trans_lt hi
    have hpj : p ⟨j, hj⟩ = p ⟨i, hi⟩ := c.2.1.idem (by omega)
    have heq : canonicalWalk p i = canonicalWalk p j :=
      (canonicalWalk_eq_iff p ⟨i, hi⟩ ⟨j, hj⟩).mpr hpj.symm
    set r := canonicalWalk p j
    have hr_le : r ≤ j := canonicalWalk_le p j
    have hr : r < 2 * m + 1 := hr_le.trans_lt hj
    have hpr : p ⟨r, hr⟩ = p ⟨j, hj⟩ :=
      (canonicalWalk_eq_iff p ⟨r, hr⟩ ⟨j, hj⟩).mp (canonicalWalk_idem p j)
    have hj_le : j ≤ r := by
      have hcr : c.1 r = j := by simpa only [p, j] using hpr.trans (c.2.1.idem (by omega))
      exact hcr ▸ c.2.1.le_self r (by omega)
    exact heq.trans (le_antisymm hr_le hj_le)
  · rw [canonicalWalk_eq_zero p (by omega), c.2.2 i (by omega)]

/-- The restriction of `c : ClosedTreeWalk m` to `Fin (2 * m + 1)` visits `m + 1` vertices. -/
@[simp]
theorem card_image_closedTreeWalk (c : ClosedTreeWalk m) :
    #(univ.image fun i : Fin (2 * m + 1) ↦ c.1 i) = m + 1 := by
  rw [← card_fixed_canonicalWalk, canonicalWalk_closedTreeWalk]
  exact c.2.1.card_vertices

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

/-- A finite path canonicalizes to a tree walk of semilength `m` if and only if it is closed,
visits `m + 1` vertices, and traverses every unordered edge twice. -/
theorem isTreeWalk_canonicalWalk_iff (w : Fin (2 * m + 1) → α) :
    IsTreeWalk m (canonicalWalk w) ↔
      w (Fin.last (2 * m)) = w 0 ∧
        #(univ.image w) = m + 1 ∧
        ∀ i : Fin (2 * m),
          #{j : Fin (2 * m) | s(w j.castSucc, w j.succ) = s(w i.castSucc, w i.succ)} = 2 := by
  refine ⟨fun hw ↦ ⟨?_, (card_fixed_canonicalWalk w).symm.trans hw.card_vertices, fun i ↦ ?_⟩,
    fun ⟨hc, hv, he⟩ ↦ isTreeWalk_canonicalWalk w hc hv he⟩
  · refine (canonicalWalk_eq_iff w (Fin.last (2 * m)) 0).mp ?_
    simpa only [Fin.val_last, Fin.val_zero, canonicalWalk_zero] using hw.closed
  · have hedge (a b : Fin (2 * m)) :
        s(w a.castSucc, w a.succ) = s(w b.castSucc, w b.succ) ↔
          s(canonicalWalk w a.castSucc, canonicalWalk w a.succ) =
            s(canonicalWalk w b.castSucc, canonicalWalk w b.succ) := by
      simp only [Sym2.eq_iff, canonicalWalk_eq_iff]
    refine Eq.trans ?_ (hw.card_edge i i.isLt)
    refine card_bij (fun j _ ↦ j.val) (fun j hj ↦ ?_) (fun _ _ _ _ h ↦ Fin.ext h) (fun j hj ↦ ?_)
    · refine mem_filter.mpr ⟨mem_range.mpr j.isLt, ?_⟩
      simpa only [Fin.val_castSucc, Fin.val_succ] using (hedge j i).mp (mem_filter.mp hj).2
    · obtain ⟨hj_lt, hj_eq⟩ := mem_filter.mp hj
      refine ⟨⟨j, mem_range.mp hj_lt⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      exact (hedge ⟨j, mem_range.mp hj_lt⟩ i).mpr
        (by simpa only [Fin.val_castSucc, Fin.val_succ] using hj_eq)

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

omit [DecidableEq α] in
private theorem closed_path_step_cyclic [NeZero m] (w : Fin (2 * m) → α) (i : Fin (2 * m)) :
    (fun t : Fin (2 * m + 1) ↦ w (Fin.ofNat (2 * m) t.val)) i.castSucc = w i ∧
      (fun t : Fin (2 * m + 1) ↦ w (Fin.ofNat (2 * m) t.val)) i.succ = w (finRotate (2 * m) i) := by
  refine ⟨by simp, ?_⟩
  apply congrArg w
  rw [finRotate_apply]
  apply Fin.ext
  simp [Fin.val_add, Fin.ofNat_eq_cast, Nat.add_mod]

/-- A cyclic word of positive length `2 * m` canonicalizes to a tree walk if and only if it has no
singleton unordered edge and visits `m + 1` vertices. -/
theorem isTreeWalk_canonicalWalk_cyclic_iff [NeZero m] (w : Fin (2 * m) → α) :
    IsTreeWalk m (canonicalWalk (fun i : Fin (2 * m + 1) ↦ w (Fin.ofNat (2 * m) i.val))) ↔
      (∀ i, ∃ j ≠ i, s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i))) ∧
        #(univ.image w) = m + 1 := by
  refine ⟨fun hw ↦ ?_, fun ⟨h, hv⟩ ↦ isTreeWalk_canonicalWalk_cyclic w h hv⟩
  obtain ⟨_, hv, he⟩ := (isTreeWalk_canonicalWalk_iff _).mp hw
  have himage : univ.image (fun i : Fin (2 * m + 1) ↦ w (Fin.ofNat (2 * m) i.val)) =
      univ.image w := by
    ext x
    simp only [mem_image, mem_univ, true_and]
    exact ⟨fun ⟨_, h⟩ ↦ ⟨_, h⟩, fun ⟨i, h⟩ ↦ ⟨i.castSucc, by simpa using h⟩⟩
  refine ⟨fun i ↦ ?_, himage ▸ hv⟩
  have hcard : #{j : Fin (2 * m) |
      s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i))} = 2 := by
    simpa only [(closed_path_step_cyclic w _).1, (closed_path_step_cyclic w _).2] using he i
  obtain ⟨a, b, hab, hmem⟩ := card_eq_two.mp hcard
  rcases eq_or_ne a i with rfl | hai
  · have hb : b ∈ ({a, b} : Finset (Fin (2 * m))) := mem_insert_of_mem (mem_singleton_self b)
    rw [← hmem, mem_filter] at hb
    exact ⟨b, hab.symm, hb.2⟩
  · have ha : a ∈ ({a, b} : Finset (Fin (2 * m))) := mem_insert_self a {b}
    rw [← hmem, mem_filter] at ha
    exact ⟨a, hai, ha.2⟩

/-- On a finite vertex set `α`, there are `catalan m * (Nat.card α).descFactorial (m + 1)` paths of
length `2 * m` whose first-visit canonicalization is a tree walk. -/
theorem card_isTreeWalk_canonicalWalk [Finite α] (m : ℕ) :
    Nat.card {v : Fin (2 * m + 1) → α // IsTreeWalk m (canonicalWalk v)} =
      catalan m * (Nat.card α).descFactorial (m + 1) := by
  let shape : {v : Fin (2 * m + 1) → α // IsTreeWalk m (canonicalWalk v)} → ClosedTreeWalk m :=
    fun v ↦ ⟨canonicalWalk v.1, v.2, fun _ hi ↦ canonicalWalk_eq_zero v.1 hi⟩
  have hfib (c : ClosedTreeWalk m) :
      {v : {v : Fin (2 * m + 1) → α // IsTreeWalk m (canonicalWalk v)} // shape v = c} ≃
        {u : Fin (2 * m + 1) → α // canonicalWalk u = canonicalWalk (fun i ↦ c.1 i)} :=
    { toFun := fun v ↦
        ⟨v.1.1, (congrArg Subtype.val v.2).trans (canonicalWalk_closedTreeWalk c).symm⟩
      invFun := fun u ↦ ⟨⟨u.1, by rw [u.2, canonicalWalk_closedTreeWalk]; exact c.2.1⟩,
        Subtype.ext (u.2.trans (canonicalWalk_closedTreeWalk c))⟩
      left_inv := fun _ ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ ↦ Subtype.ext rfl }
  have : Finite (ClosedTreeWalk m) := Finite.of_equiv _ (closedTreeWalkEquiv m).symm
  let _ := Fintype.ofFinite (ClosedTreeWalk m)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv shape), Nat.card_sigma]
  have hcard (c : ClosedTreeWalk m) :
      Nat.card {v : {v : Fin (2 * m + 1) → α // IsTreeWalk m (canonicalWalk v)} // shape v = c} =
        (Nat.card α).descFactorial (m + 1) := by
    rw [Nat.card_congr (hfib c), card_canonicalWalk_eq, card_image_closedTreeWalk]
  simp [hcard, ← Nat.card_eq_fintype_card, card_closedTreeWalk]

/-- Leading cyclic words of positive length `2 * m` are in bijection with closed paths of length
`2 * m` whose canonicalization is a tree walk. -/
def leadingCyclicWordEquiv [NeZero m] :
    {w : Fin (2 * m) → α //
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1} ≃
      {v : Fin (2 * m + 1) → α // IsTreeWalk m (canonicalWalk v)} where
  toFun w := ⟨fun i ↦ w.1 (Fin.ofNat (2 * m) i.val),
    (isTreeWalk_canonicalWalk_cyclic_iff w.1).mpr w.2⟩
  invFun v :=
    have hclosed : v.1 (Fin.last (2 * m)) = v.1 0 :=
      ((isTreeWalk_canonicalWalk_iff v.1).mp v.2).1
    have hcompat : (fun i : Fin (2 * m + 1) ↦ v.1 (Fin.ofNat (2 * m) i.val).castSucc) = v.1 := by
      funext i
      rcases Fin.lastCases (motive := fun i ↦ v.1 (Fin.ofNat (2 * m) i.val).castSucc = v.1 i)
        (by simpa [Fin.ofNat_eq_cast] using hclosed.symm)
        (fun j ↦ congrArg v.1 (Fin.ext (Nat.mod_eq_of_lt j.isLt))) i with h
      exact h
    ⟨fun t ↦ v.1 t.castSucc,
      (isTreeWalk_canonicalWalk_cyclic_iff _).mp (hcompat.symm ▸ v.2)⟩
  left_inv w := Subtype.ext <| funext fun t ↦ congrArg w.1 (Fin.ext (Nat.mod_eq_of_lt t.isLt))
  right_inv v := by
    have hclosed : v.1 (Fin.last (2 * m)) = v.1 0 :=
      ((isTreeWalk_canonicalWalk_iff v.1).mp v.2).1
    refine Subtype.ext (funext fun i ↦ ?_)
    exact Fin.lastCases (motive := fun i ↦ v.1 (Fin.ofNat (2 * m) i.val).castSucc = v.1 i)
      (by simpa [Fin.ofNat_eq_cast] using hclosed.symm)
      (fun j ↦ congrArg v.1 (Fin.ext (Nat.mod_eq_of_lt j.isLt))) i

/-- The forward map of `leadingCyclicWordEquiv` reads the cyclic word modulo `2 * m`. -/
@[simp]
theorem leadingCyclicWordEquiv_apply_coe [NeZero m]
    (w : {w : Fin (2 * m) → α //
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1}) :
    (leadingCyclicWordEquiv w).1 = fun i : Fin (2 * m + 1) ↦ w.1 (Fin.ofNat (2 * m) i.val) :=
  (rfl)

/-- The inverse of `leadingCyclicWordEquiv` drops the terminal vertex of the closed path. -/
@[simp]
theorem leadingCyclicWordEquiv_symm_apply_coe [NeZero m]
    (v : {v : Fin (2 * m + 1) → α // IsTreeWalk m (canonicalWalk v)}) :
    (leadingCyclicWordEquiv.symm v).1 = fun t : Fin (2 * m) ↦ v.1 t.castSucc :=
  (rfl)

/-- On a finite vertex set `α` and for `m ≠ 0`, there are
`catalan m * (Nat.card α).descFactorial (m + 1)` singleton-free cyclic words of length `2 * m`
visiting `m + 1` vertices. -/
theorem card_leading_cyclic_word [Finite α] [NeZero m] :
    Nat.card {w : Fin (2 * m) → α //
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1} =
      catalan m * (Nat.card α).descFactorial (m + 1) := by
  rw [Nat.card_congr leadingCyclicWordEquiv, card_isTreeWalk_canonicalWalk]

/-- In `Finset` filter form, for `m ≠ 0` there are
`catalan m * (Fintype.card α).descFactorial (m + 1)` singleton-free cyclic words of length `2 * m`
visiting `m + 1` vertices. -/
theorem card_filter_leading_cyclic_word [Fintype α] (hm : m ≠ 0) :
    #{w : Fin (2 * m) → α |
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1} =
      catalan m * (Fintype.card α).descFactorial (m + 1) := by
  have : NeZero m := ⟨hm⟩
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, card_leading_cyclic_word,
    Nat.card_eq_fintype_card]

/-- No step of a leading cyclic word is a self-loop. -/
theorem ne_finRotate_of_leading {w : Fin (2 * m) → α}
    (h : ∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t)))
    (hv : #(univ.image w) = m + 1) (t : Fin (2 * m)) :
    w t ≠ w (finRotate (2 * m) t) := by
  have : NeZero m := ⟨by rintro rfl; simp at hv⟩
  set v : Fin (2 * m + 1) → α := fun i ↦ w (Fin.ofNat (2 * m) i.val)
  have hw := isTreeWalk_canonicalWalk_cyclic w h hv
  have hne := hw.ne_succ t.isLt
  have h1 := (closed_path_step_cyclic w t).1
  have h2 := (closed_path_step_cyclic w t).2
  intro heq
  apply hne
  exact (canonicalWalk_eq_iff v t.castSucc t.succ).mpr (by simpa only [v, h1, h2] using heq)

/-- Distinct steps of a leading cyclic word that share an unordered edge traverse it in opposite
directions. -/
theorem eq_and_eq_of_ne_of_sym2_eq {w : Fin (2 * m) → α}
    (h : ∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t)))
    (hv : #(univ.image w) = m + 1) {s t : Fin (2 * m)} (hst : s ≠ t)
    (he : s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) :
    w s = w (finRotate (2 * m) t) ∧ w (finRotate (2 * m) s) = w t := by
  have : NeZero m := ⟨by rintro rfl; simp at hv⟩
  set v : Fin (2 * m + 1) → α := fun i ↦ w (Fin.ofNat (2 * m) i.val)
  have hw := isTreeWalk_canonicalWalk_cyclic w h hv
  have hs := closed_path_step_cyclic w s
  have ht := closed_path_step_cyclic w t
  have hec : s(canonicalWalk v s.castSucc, canonicalWalk v s.succ) =
      s(canonicalWalk v t.castSucc, canonicalWalk v t.succ) := by
    simp only [Sym2.eq_iff, canonicalWalk_eq_iff, v, hs.1, hs.2, ht.1, ht.2]
    exact Sym2.eq_iff.mp he
  obtain ⟨h1, h2⟩ := hw.eq_and_eq_of_sym2_eq s.isLt t.isLt (Fin.val_ne_of_ne hst) hec
  exact ⟨by simpa only [v, hs.1, ht.2] using (canonicalWalk_eq_iff v s.castSucc t.succ).mp h1,
    by simpa only [v, hs.2, ht.1] using (canonicalWalk_eq_iff v s.succ t.castSucc).mp h2⟩

/-- All `2 * m` directed steps `(w t, w (finRotate (2 * m) t))` of a leading cyclic word are
distinct. -/
theorem injective_step_of_leading {w : Fin (2 * m) → α}
    (h : ∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t)))
    (hv : #(univ.image w) = m + 1) :
    Function.Injective fun t : Fin (2 * m) ↦ (w t, w (finRotate (2 * m) t)) := by
  intro s t hst
  obtain ⟨h1, h2⟩ := Prod.mk.inj hst
  by_contra hne
  have he : s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t)) := by rw [h1, h2]
  have hopp := (eq_and_eq_of_ne_of_sym2_eq h hv hne he).1
  exact ne_finRotate_of_leading h hv s (hopp.trans h2.symm)

omit [DecidableEq α] in
private noncomputable def oppositeStep {w : Fin (2 * m) → α}
    (h : ∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t)))
    (t : Fin (2 * m)) : Fin (2 * m) :=
  Classical.choose (h t)

private theorem oppositeStep_spec {w : Fin (2 * m) → α}
    (h : ∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t)))
    (hv : #(univ.image w) = m + 1) (t : Fin (2 * m)) :
    w (oppositeStep h t) = w (finRotate (2 * m) t) ∧
      w (finRotate (2 * m) (oppositeStep h t)) = w t := by
  obtain ⟨hne, he⟩ := Classical.choose_spec (h t)
  exact eq_and_eq_of_ne_of_sym2_eq h hv hne he

private theorem oppositeStep_involutive {w : Fin (2 * m) → α}
    (h : ∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t)))
    (hv : #(univ.image w) = m + 1) (t : Fin (2 * m)) :
    oppositeStep h (oppositeStep h t) = t :=
  injective_step_of_leading h hv <| Prod.ext
    ((oppositeStep_spec h hv (oppositeStep h t)).1.trans (oppositeStep_spec h hv t).2)
    ((oppositeStep_spec h hv (oppositeStep h t)).2.trans (oppositeStep_spec h hv t).1)

end DecidableEq

section LinearOrder

variable {α : Type*} [LinearOrder α] {m : ℕ}

/-- On a linearly ordered vertex set, a leading cyclic word of length `2 * m` has exactly `m`
strictly increasing steps `w t < w (finRotate (2 * m) t)`. -/
theorem card_filter_lt_finRotate {w : Fin (2 * m) → α}
    (h : ∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t)))
    (hv : #(univ.image w) = m + 1) :
    #{t : Fin (2 * m) | w t < w (finRotate (2 * m) t)} = m := by
  have hbij : #{t : Fin (2 * m) | ¬ w t < w (finRotate (2 * m) t)} =
      #{t : Fin (2 * m) | w t < w (finRotate (2 * m) t)} := by
    refine card_nbij' (oppositeStep h) (oppositeStep h) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
      (fun t _ ↦ oppositeStep_involutive h hv t) (fun t _ ↦ oppositeStep_involutive h hv t)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      rw [(oppositeStep_spec h hv t).1, (oppositeStep_spec h hv t).2]
      exact (not_lt.mp ht).lt_of_ne (ne_finRotate_of_leading h hv t).symm
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
      rw [(oppositeStep_spec h hv t).1, (oppositeStep_spec h hv t).2]
      exact ht.not_gt
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * m))))
    (fun t ↦ w t < w (finRotate (2 * m) t))
  rw [hbij, card_univ, Fintype.card_fin] at hsum
  omega

/-- On a linearly ordered vertex set, any commutative-monoid product over the steps of a leading
cyclic word factors into paired opposite-direction factors over the `m` strictly increasing steps.
-/
theorem prod_eq_prod_filter_lt_finRotate {M : Type*} [CommMonoid M] (f : α → α → M)
    {w : Fin (2 * m) → α}
    (h : ∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t)))
    (hv : #(univ.image w) = m + 1) :
    ∏ t : Fin (2 * m), f (w t) (w (finRotate (2 * m) t)) =
      ∏ t : Fin (2 * m) with w t < w (finRotate (2 * m) t),
        f (w t) (w (finRotate (2 * m) t)) * f (w (finRotate (2 * m) t)) (w t) := by
  rw [← prod_filter_mul_prod_filter_not univ (fun t ↦ w t < w (finRotate (2 * m) t))
    (fun t ↦ f (w t) (w (finRotate (2 * m) t))), prod_mul_distrib]
  congr 1
  refine prod_nbij' (oppositeStep h) (oppositeStep h) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    (fun t _ ↦ oppositeStep_involutive h hv t) (fun t _ ↦ oppositeStep_involutive h hv t)
    (fun t _ ↦ ?_)
  · rw [mem_filter] at ht ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [(oppositeStep_spec h hv t).1, (oppositeStep_spec h hv t).2]
    exact (not_lt.mp ht.2).lt_of_ne (ne_finRotate_of_leading h hv t).symm
  · rw [mem_filter] at ht ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [(oppositeStep_spec h hv t).1, (oppositeStep_spec h hv t).2]
    exact ht.2.not_gt
  · rw [(oppositeStep_spec h hv t).1, (oppositeStep_spec h hv t).2]

end LinearOrder

end TauCeti.TreeWalk
