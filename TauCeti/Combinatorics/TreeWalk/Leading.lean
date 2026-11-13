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
leading word in the Wigner moment expansion. Extending it to a path by `cyclicPath` and labeling
each vertex by its first visit turns it into a closed tree walk, and conversely every closed walk
whose canonicalization is a tree walk has this vertex and edge structure.

Combining the `catalan m` count of `ClosedTreeWalk m` with `card_canonicalWalk_eq` counts the
leading paths and, for `m ≠ 0`, the leading cyclic words on a finite vertex set `α` as
`catalan m * (Fintype.card α).descFactorial (m + 1)`. Moreover, every unordered edge of a leading
cyclic word is traversed once in each direction, so its `2 * m` directed steps are distinct.

## Main definitions

* `TauCeti.TreeWalk.cyclicPath`: view a cyclic word as a closed path by repeating its initial
  vertex at the endpoint.
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
* `TauCeti.TreeWalk.eq_and_eq_of_ne_of_sym2_eq` and
  `TauCeti.TreeWalk.injective_step_of_leading`: opposite-direction edge pairing and injectivity of
  the `2 * m` directed steps of a leading cyclic word.

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

/-- Extending the prefix of a closed path by `cyclicPath` recovers the original path. -/
theorem cyclicPath_castSucc_eq {k : ℕ} [NeZero k] {v : Fin (k + 1) → α}
    (hclosed : v (Fin.last k) = v 0) :
    cyclicPath (fun t : Fin k ↦ v t.castSucc) = v := by
  funext i
  exact Fin.lastCases (by simp [hclosed])
    (fun j ↦ congrArg v (Fin.ext (Nat.mod_eq_of_lt j.isLt))) i

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
    IsTreeWalk m (canonicalWalk (cyclicPath w)) :=
  isTreeWalk_canonicalWalk (cyclicPath w) (by simp) (by simpa using hv)
    (card_edge_fiber_cyclicPath w h hv)

/-- A cyclic word of positive length `2 * m` canonicalizes to a tree walk if and only if it has no
singleton unordered edge and visits `m + 1` vertices. -/
theorem isTreeWalk_canonicalWalk_cyclic_iff [NeZero m] (w : Fin (2 * m) → α) :
    IsTreeWalk m (canonicalWalk (cyclicPath w)) ↔
      (∀ i, ∃ j ≠ i, s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i))) ∧
        #(univ.image w) = m + 1 := by
  refine ⟨fun hw ↦ ?_, fun ⟨h, hv⟩ ↦ isTreeWalk_canonicalWalk_cyclic w h hv⟩
  obtain ⟨_, hv, he⟩ := (isTreeWalk_canonicalWalk_iff (cyclicPath w)).mp hw
  rw [image_cyclicPath] at hv
  refine ⟨fun i ↦ ?_, hv⟩
  have hcard : #{j : Fin (2 * m) |
      s(w j, w (finRotate (2 * m) j)) = s(w i, w (finRotate (2 * m) i))} = 2 := by
    simpa only [cyclicPath_castSucc, cyclicPath_succ] using he i
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
  toFun w := ⟨cyclicPath w.1, (isTreeWalk_canonicalWalk_cyclic_iff w.1).mpr w.2⟩
  invFun v :=
    have hcompat : cyclicPath (fun t : Fin (2 * m) ↦ v.1 t.castSucc) = v.1 :=
      cyclicPath_castSucc_eq ((isTreeWalk_canonicalWalk_iff v.1).mp v.2).1
    ⟨fun t ↦ v.1 t.castSucc,
      (isTreeWalk_canonicalWalk_cyclic_iff _).mp (hcompat.symm ▸ v.2)⟩
  left_inv w := Subtype.ext <| funext (cyclicPath_castSucc w.1)
  right_inv v := Subtype.ext <|
    cyclicPath_castSucc_eq ((isTreeWalk_canonicalWalk_iff v.1).mp v.2).1

/-- The forward map of `leadingCyclicWordEquiv` extends the cyclic word by `cyclicPath`. -/
@[simp]
theorem leadingCyclicWordEquiv_apply_coe [NeZero m]
    (w : {w : Fin (2 * m) → α //
      (∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1}) :
    (leadingCyclicWordEquiv w).1 = cyclicPath w.1 :=
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

/-- Distinct steps of a leading cyclic word that share an unordered edge traverse it in opposite
directions. -/
theorem eq_and_eq_of_ne_of_sym2_eq {w : Fin (2 * m) → α}
    (h : ∀ t, ∃ s ≠ t, s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t)))
    (hv : #(univ.image w) = m + 1) {s t : Fin (2 * m)} (hst : s ≠ t)
    (he : s(w s, w (finRotate (2 * m) s)) = s(w t, w (finRotate (2 * m) t))) :
    w s = w (finRotate (2 * m) t) ∧ w (finRotate (2 * m) s) = w t := by
  have : NeZero m := ⟨by rintro rfl; simp at hv⟩
  have hw := isTreeWalk_canonicalWalk_cyclic w h hv
  have hec : s(canonicalWalk (cyclicPath w) s.castSucc, canonicalWalk (cyclicPath w) s.succ) =
      s(canonicalWalk (cyclicPath w) t.castSucc, canonicalWalk (cyclicPath w) t.succ) := by
    simp only [Sym2.eq_iff, canonicalWalk_eq_iff, cyclicPath_castSucc, cyclicPath_succ]
    exact Sym2.eq_iff.mp he
  obtain ⟨h1, h2⟩ := hw.eq_and_eq_of_sym2_eq s.isLt t.isLt (Fin.val_ne_of_ne hst) hec
  exact ⟨by simpa using (canonicalWalk_eq_iff (cyclicPath w) s.castSucc t.succ).mp h1,
    by simpa using (canonicalWalk_eq_iff (cyclicPath w) s.succ t.castSucc).mp h2⟩

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
  exact (ne_and_card_edge_fiber_eq_two_of_no_singleton_edge_of_card_image_eq w h hv).1 s
    (hopp.trans h2.symm)

end TauCeti.TreeWalk
